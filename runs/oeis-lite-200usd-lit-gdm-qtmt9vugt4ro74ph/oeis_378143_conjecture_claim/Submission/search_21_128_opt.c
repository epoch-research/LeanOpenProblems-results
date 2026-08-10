#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <pthread.h>
#include <stdlib.h>
#include <stdatomic.h>

#define NUM_THREADS 32

volatile _Atomic bool found_flag = false;

typedef unsigned __int128 uint128_t;

static inline uint128_t mul_mod(uint128_t a, uint128_t b, uint128_t m) {
    return (a * b) % m;
}

typedef struct {
    int n;
    uint64_t start_k;
    uint64_t end_k;
    int thread_id;
} ThreadArg;

// Small primes for trial division
static const uint64_t PRIMES[] = {
    3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199
};
#define NUM_PRIMES (sizeof(PRIMES)/sizeof(PRIMES[0]))

void* search_thread(void* arg) {
    ThreadArg* targ = (ThreadArg*)arg;
    int n = targ->n;
    uint64_t start_k = targ->start_k;
    uint64_t end_k = targ->end_k;
    uint128_t modulus = (uint128_t)1 << (n + 1);

    uint64_t progress_step = (end_k - start_k) / 10;
    if (progress_step == 0) progress_step = 1;

    // Precompute modulus % d for each prime
    uint64_t mod_d[NUM_PRIMES];
    for (int i = 0; i < NUM_PRIMES; i++) {
        mod_d[i] = (uint64_t)(modulus % PRIMES[i]);
    }

    for (uint64_t k = start_k; k < end_k; k++) {
        if (atomic_load(&found_flag)) break;

        if (targ->thread_id == 0 && (k - start_k) % progress_step == 0) {
            printf("Thread 0 progress: %.1f%%\n", (double)(k - start_k) * 100.0 / (end_k - start_k));
            fflush(stdout);
        }

        // Fast trial division using 64-bit arithmetic
        bool composite = false;
        for (int i = 0; i < NUM_PRIMES; i++) {
            uint64_t rem = (k % PRIMES[i]) * mod_d[i] + 1;
            if (rem % PRIMES[i] == 0) {
                composite = true;
                break;
            }
        }
        if (composite) continue;

        uint128_t p = (uint128_t)k * modulus + 1;
        
        // GFN divisor test: check if 10^(2^n) == -1 mod p
        uint128_t x = 10 % p;
        for (int i = 0; i < n; i++) {
            x = mul_mod(x, x, p);
        }
        
        if (x == p - 1) {
            // Found divisor! Print it.
            char p_str[50];
            int idx = 0;
            uint128_t temp = p;
            while (temp > 0) {
                p_str[idx++] = '0' + (temp % 10);
                temp /= 10;
            }
            p_str[idx] = '\0';
            for (int j = 0; j < idx / 2; j++) {
                char t = p_str[j];
                p_str[j] = p_str[idx - 1 - j];
                p_str[idx - 1 - j] = t;
            }
            printf("\nFOUND DIVISOR for n=%d: p=%s (k=%lu)\n", n, p_str, k);
            fflush(stdout);
            atomic_store(&found_flag, true);
            break;
        }
    }
    return NULL;
}

int main(int argc, char** argv) {
    if (argc < 4) {
        printf("Usage: %s <n> <start_k_billions> <end_k_billions>\n", argv[0]);
        return 1;
    }
    int n = atoi(argv[1]);
    uint64_t start_k = atoll(argv[2]) * 1000000000ULL;
    uint64_t end_k = atoll(argv[3]) * 1000000000ULL;
    if (start_k == 0) start_k = 1;

    printf("Starting fast optimized 128-bit search for n=%d using %d threads from k=%lu to %lu...\n", n, NUM_THREADS, start_k, end_k);

    pthread_t threads[NUM_THREADS];
    ThreadArg args[NUM_THREADS];
    uint64_t chunk = (end_k - start_k) / NUM_THREADS;

    for (int i = 0; i < NUM_THREADS; i++) {
        args[i].n = n;
        args[i].start_k = start_k + i * chunk;
        args[i].end_k = (i == NUM_THREADS - 1) ? end_k : start_k + (i + 1) * chunk;
        args[i].thread_id = i;
        pthread_create(&threads[i], NULL, search_thread, &args[i]);
    }

    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], NULL);
    }
    printf("Search for n=%d completed. Found status: %s\n", n, atomic_load(&found_flag) ? "YES" : "NO");
    return 0;
}
