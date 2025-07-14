#include <iostream>
#include <vector>
#include <thread>
#include <atomic>
#include <cstring>
#include <cassert>
#include <chrono>
#include <iomanip>
#include <immintrin.h>
#include <secp256k1.h>
#include <openssl/evp.h> // Usar EVP API em vez de SHA/RIPEMD diretamente
#include <openssl/err.h>

extern "C" {
#include "compat.c"
#include "sha256.c"
#include "rmd160s.c"
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
static secp256k1_context* g_ctx = nullptr;

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
// INICIALIZAÇÃO SECP256K1
//-----------------------------------------------------------
static void init_secp256k1() {
    if (!g_ctx) {
        g_ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
        unsigned char seed[32] = {0};
        if (!secp256k1_context_randomize(g_ctx, seed)) {
            std::cerr << "Failed to randomize secp256k1 context\n";
            secp256k1_context_destroy(g_ctx);
            g_ctx = nullptr;
        }
    }
}

//-----------------------------------------------------------
// PARSE E SERIALIZAÇÃO DE PUBKEY
//-----------------------------------------------------------
static bool parse_pubkey(const std::string &hex, secp256k1_pubkey &pubkey) {
    std::vector<unsigned char> data = hex_to_bytes(hex);
    if (data.size() != 33) {
        std::cerr << "Invalid compressed pubkey length: " << data.size() << "\n";
        return false;
    }
    if (!secp256k1_ec_pubkey_parse(g_ctx, &pubkey, data.data(), data.size())) {
        std::cerr << "Error parsing pubkey\n";
        return false;
    }
    return true;
}

static std::string serialize_pubkey(const secp256k1_pubkey &pubkey) {
    unsigned char out[33];
    size_t outlen = 33;
    secp256k1_ec_pubkey_serialize(g_ctx, out, &outlen, &pubkey, SECP256K1_EC_COMPRESSED);
    return bytes_to_hex(out, outlen);
}

//-----------------------------------------------------------
// TWEAK ADD
//-----------------------------------------------------------
static bool pubkey_tweak_add(secp256k1_pubkey &pubkey, const unsigned char tweak[32]) {
    return secp256k1_ec_pubkey_tweak_add(g_ctx, &pubkey, tweak) != 0;
}

//-----------------------------------------------------------
// INT TO 32 BYTES
//-----------------------------------------------------------
static void int_to_32bytes(uint64_t v, unsigned char out[32]) {
    memset(out, 0, 32);
    for (int i = 0; i < 8; i++) {
        out[31 - i] = (unsigned char)((v >> (8 * i)) & 0xFF);
    }
}

//-----------------------------------------------------------
// WORKER THREAD
//-----------------------------------------------------------
static void worker_thread(int thread_id, int num_threads, const secp256k1_pubkey &start_pubkey) {
    secp256k1_pubkey pubkey_i = start_pubkey;
    unsigned char tweak_init[32];
    int_to_32bytes(thread_id, tweak_init);
    if (!pubkey_tweak_add(pubkey_i, tweak_init)) {
        std::cerr << "[Thread " << thread_id << "] pubkey_tweak_add(i) failed.\n";
        return;
    }

    unsigned char tweak_step[32];
    int_to_32bytes(num_threads, tweak_step);

    // Buffers para AVX2
    const unsigned char* compressed[AVX2_LANES]; // Alterado para const
    unsigned char h160[AVX2_LANES][20];
    secp256k1_pubkey pubkeys[AVX2_LANES];

    for (int i = 0; i < AVX2_LANES; i++) {
        compressed[i] = new unsigned char[33];
        pubkeys[i] = pubkey_i;
        if (i > 0) {
            unsigned char tweak_lane[32];
            int_to_32bytes(i * num_threads, tweak_lane);
            if (!pubkey_tweak_add(pubkeys[i], tweak_lane)) {
                std::cerr << "[Thread " << thread_id << "] pubkey_tweak_add(lane " << i << ") failed.\n";
                return;
            }
        }
    }

    while (!g_found.load(std::memory_order_relaxed)) {
        for (int b = 0; b < BATCH_SIZE; b += AVX2_LANES) {
            if (g_found.load(std::memory_order_relaxed)) break;

            // Serializar pubkeys para cada lane
            for (int i = 0; i < AVX2_LANES; i++) {
                size_t clen = 33;
                secp256k1_ec_pubkey_serialize(g_ctx, const_cast<unsigned char*>(compressed[i]), &clen, &pubkeys[i], SECP256K1_EC_COMPRESSED);
            }

            // Calcular HASH160 para todas as lanes com AVX2
            hash160_avx2(compressed, 33, h160);

            // Verificar prefixos
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

            // Incrementar todas as pubkeys
            for (int i = 0; i < AVX2_LANES; i++) {
                if (!pubkey_tweak_add(pubkeys[i], tweak_step)) {
                    std::cerr << "[Thread " << thread_id << "] pubkey_tweak_add(step) failed.\n";
                    break;
                }
            }

            // Atualizar contador de chaves
            g_total_keys.fetch_add(AVX2_LANES, std::memory_order_relaxed);
        }
    }

    // Limpeza
    for (int i = 0; i < AVX2_LANES; i++) {
        delete[] compressed[i];
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
    init_secp256k1();
    if (!g_ctx) {
        std::cerr << "Failed to initialize secp256k1 context\n";
        return 1;
    }

    secp256k1_pubkey start_pubkey;
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
    if (g_ctx) {
        secp256k1_context_destroy(g_ctx);
        g_ctx = nullptr;
    }

    return 0;
}