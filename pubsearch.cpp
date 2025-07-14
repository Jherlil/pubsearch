#include <iostream>
#include <vector>
#include <thread>
#include <atomic>
#include <cstring>
#include <cassert>
#include <chrono>
#include <iomanip>
#include <immintrin.h>

extern "C" {
#include "addr.c"
}

//-----------------------------------------------------------
// CONFIGURAÇÃO
//-----------------------------------------------------------
static const std::string TARGET_PREFIX = "f6f5431d25bbf7b12e8add9af5e3475c44a0a5b8";
static const std::string START_PUBKEY_HEX = "02d5305c2115885468c6fe4a4cc15d168b7091a585fedaefae9733f52833cda662";
static const int BATCH_SIZE = 1000000;
static const int AVX2_LANES = 8;

//-----------------------------------------------------------
// GLOBALS
//-----------------------------------------------------------
static std::atomic<bool> g_found(false);
static std::atomic<uint64_t> g_total_keys(0);

//-----------------------------------------------------------
// HEX / BYTE UTILS
//-----------------------------------------------------------
static std::vector<unsigned char> hex_to_bytes(const std::string &hex) {
    std::vector<unsigned char> bytes;
    bytes.reserve(hex.size() / 2);
    for (size_t i = 0; i < hex.size(); i += 2) {
        unsigned int byte;
        sscanf(hex.substr(i, 2).c_str(), "%x", &byte);
        bytes.push_back(static_cast<unsigned char>(byte));
    }
    return bytes;
}

static std::string bytes_to_hex(const unsigned char* data, size_t len) {
    static const char* hexdig = "0123456789abcdef";
    std::string hex;
    hex.reserve(len * 2);
    for (size_t i = 0; i < len; i++) {
        unsigned char c = data[i];
        hex.push_back(hexdig[c >> 4]);
        hex.push_back(hexdig[c & 0xF]);
    }
    return hex;
}

//-----------------------------------------------------------
// HASH160 USANDO IMPLEMENTAÇÕES OTIMIZADAS (SHA256 + RIPEMD160)
//-----------------------------------------------------------
static void hash160_avx2(const unsigned char* data[AVX2_LANES], size_t data_len,
                         unsigned char out20[AVX2_LANES][20]) {
    const int BATCH = RMD_LEN;
    u8 msg[BATCH][64];
    u32 rs[BATCH][16];
    u32 r160[BATCH][5];

    for (int start = 0; start < AVX2_LANES; start += BATCH) {
        for (int i = 0; i < BATCH; i++) {
            int idx = start + i;
            memcpy(msg[i], data[idx], data_len);
            memset(msg[i] + data_len, 0, sizeof(msg[i]) - data_len);
            msg[i][data_len] = 0x80;
            msg[i][62] = 0x01;
            msg[i][63] = 0x08;
            sha256_final(rs[i], msg[i], sizeof(msg[i]));
            rs[i][8] = 0x80000000;
            rs[i][14] = 0x00010000;
        }

        rmd160_batch(r160, rs);

        for (int i = 0; i < BATCH; i++) {
            int idx = start + i;
            for (int j = 0; j < 5; j++) {
                u32 v = r160[i][j];
                out20[idx][4 * j + 0] = (v >> 24) & 0xFF;
                out20[idx][4 * j + 1] = (v >> 16) & 0xFF;
                out20[idx][4 * j + 2] = (v >> 8) & 0xFF;
                out20[idx][4 * j + 3] = v & 0xFF;
            }
        }
    }
}

//-----------------------------------------------------------
// CHECK PREFIX
//-----------------------------------------------------------
static bool check_prefix(const unsigned char out20[20]) {
    std::string hash_hex = bytes_to_hex(out20, 20);
    return hash_hex.compare(0, TARGET_PREFIX.size(), TARGET_PREFIX) == 0;
}

//-----------------------------------------------------------
// EXPONENTIAÇÃO MOD P
//-----------------------------------------------------------
static void fe_modp_pow(fe r, const fe a, const fe e) {
    fe result;
    fe base;
    fe_clone(base, a);
    fe_set64(result, 1);
    for (int limb = 3; limb >= 0; --limb) {
        for (int bit = 63; bit >= 0; --bit) {
            fe_modp_sqr(result, result);
            if (e[limb] & (1ULL << bit)) {
                fe_modp_mul(result, result, base);
            }
        }
    }
    fe_clone(r, result);
}

static void fe_modp_sqrt(fe r, const fe a) {
    static const fe SQRT_EXP = {0xffffffffbfffff0cULL, 0xffffffffffffffffULL,
                                0xffffffffffffffffULL, 0x3fffffffffffffffULL};
    fe_modp_pow(r, a, SQRT_EXP);
}

//-----------------------------------------------------------
// PARSE E SERIALIZAÇÃO DE PUBKEY
//-----------------------------------------------------------
static bool parse_pubkey(const std::string &hex, pe &pubkey) {
    std::vector<unsigned char> data = hex_to_bytes(hex);
    if (data.size() != 33) {
        std::cerr << "Invalid compressed pubkey length: " << data.size() << "\n";
        return false;
    }
    bool odd = data[0] & 1;
    std::string x_hex = hex.substr(2);
    fe_from_hex(pubkey.x, x_hex.c_str());
    fe t, seven;
    fe_modp_sqr(t, pubkey.x);        // x^2
    fe_modp_mul(t, t, pubkey.x);     // x^3
    fe_set64(seven, 7);
    fe_modp_add(t, t, seven);        // x^3 + 7
    fe_modp_sqrt(pubkey.y, t);       // sqrt
    if ((pubkey.y[0] & 1ULL) != odd) {
        fe_modp_sub(pubkey.y, FE_P, pubkey.y);
    }
    fe_set64(pubkey.z, 1);
    return true;
}

static void serialize_pubkey(const pe &pubkey, unsigned char out[33]) {
    out[0] = (pubkey.y[0] & 1ULL) ? 0x03 : 0x02;
    for (int i = 0; i < 4; ++i) {
        u64 be = swap64(pubkey.x[3 - i]);
        memcpy(out + 1 + i * 8, &be, 8);
    }
}

//-----------------------------------------------------------
// POINT ADDITION BY SCALAR
//-----------------------------------------------------------
//-----------------------------------------------------------
// WORKER THREAD
//-----------------------------------------------------------
static void worker_thread(int thread_id, int num_threads, const pe &start_pubkey) {
    fe tmp;
    fe_set64(tmp, (u64)thread_id);
    pe pubkey_i;
    ec_gtable_mul(&pubkey_i, tmp);
    ec_jacobi_rdc(&pubkey_i, &pubkey_i);
    ec_jacobi_addrdc(&pubkey_i, &start_pubkey, &pubkey_i);

    fe step_scalar;
    fe_set64(step_scalar, (u64)num_threads);
    pe step;
    ec_gtable_mul(&step, step_scalar);
    ec_jacobi_rdc(&step, &step);

    pe pubkeys[AVX2_LANES];
    unsigned char compressed[AVX2_LANES][33];
    const unsigned char* comp_ptrs[AVX2_LANES];
    unsigned char h160[AVX2_LANES][20];

    for (int i = 0; i < AVX2_LANES; i++) {
        if (i == 0) {
            pe_clone(&pubkeys[i], &pubkey_i);
        } else {
            ec_jacobi_addrdc(&pubkeys[i], &pubkeys[i-1], &step);
        }
        comp_ptrs[i] = compressed[i];
    }

    while (!g_found.load(std::memory_order_relaxed)) {
        for (int b = 0; b < BATCH_SIZE; b += AVX2_LANES) {
            if (g_found.load(std::memory_order_relaxed)) break;

            for (int i = 0; i < AVX2_LANES; i++) {
                serialize_pubkey(pubkeys[i], compressed[i]);
            }

            hash160_avx2(comp_ptrs, 33, h160);

            for (int i = 0; i < AVX2_LANES; i++) {
                if (check_prefix(h160[i])) {
                    g_found.store(true, std::memory_order_relaxed);
                    std::string pubkey_hex = bytes_to_hex(compressed[i], 33);
                    std::string hash_hex = bytes_to_hex(h160[i], 20);
                    std::cout << "\n[Thread " << thread_id << "] MATCH FOUND!\n"
                              << "  PubKey:  " << pubkey_hex << "\n"
                              << "  HASH160: " << hash_hex << "\n";
                    break;
                }
            }

            for (int i = 0; i < AVX2_LANES; i++) {
                ec_jacobi_addrdc(&pubkeys[i], &pubkeys[i], &step);
            }

            g_total_keys.fetch_add(AVX2_LANES, std::memory_order_relaxed);
        }
    }
}

//-----------------------------------------------------------
// RELATÓRIO DE VELOCIDADE (M/G/Pkeys)
//-----------------------------------------------------------
static void report_speed() {
    auto last = std::chrono::steady_clock::now();
    while (!g_found.load(std::memory_order_relaxed)) {
        std::this_thread::sleep_for(std::chrono::seconds(1));
        auto now = std::chrono::steady_clock::now();
        double elapsed = std::chrono::duration<double>(now - last).count();
        last = now;

        uint64_t keys = g_total_keys.exchange(0, std::memory_order_relaxed);
        double rate = keys / elapsed; // keys per second
        const char* unit = "keys";
        if (rate >= 1e15) { unit = "Pkeys"; rate /= 1e15; }
        else if (rate >= 1e9) { unit = "Gkeys"; rate /= 1e9; }
        else if (rate >= 1e6) { unit = "Mkeys"; rate /= 1e6; }
        else if (rate >= 1e3) { unit = "Kkeys"; rate /= 1e3; }

        std::cout << "[Progress] " << std::fixed << std::setprecision(2)
                  << rate << ' ' << unit << "/s\n";
    }
}

//-----------------------------------------------------------
// MAIN
//-----------------------------------------------------------
int main() {
    ec_gtable_init();

    pe start_pubkey;
    if (!parse_pubkey(START_PUBKEY_HEX, start_pubkey)) {
        std::cerr << "Failed to parse START_PUBKEY_HEX\n";
        return 1;
    }

    unsigned int num_threads = std::thread::hardware_concurrency();
    if (num_threads == 0) num_threads = 1;

    std::cout << "Starting vanity search:\n"
              << "  Start PubKey: " << START_PUBKEY_HEX << "\n"
              << "  Target prefix: " << TARGET_PREFIX << "\n"
              << "  Using " << num_threads << " threads.\n"
              << "  Batch size:    " << BATCH_SIZE << "\n"
              << "  AVX2 lanes:    " << AVX2_LANES << "\n";

    // Iniciar thread para relatar a velocidade de busca
    std::thread reporter(report_speed);

    // Lançar threads de trabalho
    std::vector<std::thread> threads;
    threads.reserve(num_threads);
    for (unsigned int i = 0; i < num_threads; i++) {
        threads.emplace_back(worker_thread, i, num_threads, start_pubkey);
    }

    // Aguardar threads
    for (auto &th : threads) {
        th.join();
    }

    // Aguardar thread de relatório
    reporter.join();

    std::cout << "Done.\n";
    return 0;
}