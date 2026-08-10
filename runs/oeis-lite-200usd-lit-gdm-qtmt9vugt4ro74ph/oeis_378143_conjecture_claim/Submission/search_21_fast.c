#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <pthread.h>
#include <stdlib.h>
#include <stdatomic.h>
#include <time.h>

#define NUM_THREADS 32

volatile _Atomic bool found_flag = false;

static inline uint64_t mul_mod(uint64_t a, uint64_t b, uint64_t m) {
    return (uint64_t)(((__int128)a * b) % m);
}

typedef struct {
    int n;
    uint64_t start_k;
    uint64_t end_k;
    int thread_id;
} ThreadArg;

void* search_thread(void* arg) {
    ThreadArg* targ = (ThreadArg*)arg;
    int n = targ->n;
    uint64_t start_k = targ->start_k;
    uint64_t end_k = targ->end_k;
    uint64_t modulus = 1ULL << (n + 1);

    uint64_t progress_step = (end_k - start_k) / 10;
    if (progress_step == 0) progress_step = 1;

    for (uint64_t k = start_k; k < end_k; k++) {
        if (atomic_load(&found_flag)) break;

        if (targ->thread_id == 0 && (k - start_k) % progress_step == 0) {
            printf("Thread 0 progress: %.1f%%\n", (double)(k - start_k) * 100.0 / (end_k - start_k));
            fflush(stdout);
        }

        uint64_t p = k * modulus + 1;
        
        // GFN divisor test: check if 10^(2^n) == -1 mod p
        uint64_t x = 10 % p;
        for (int i = 0; i < n; i++) {
            x = mul_mod(x, x, p);
        }
        
        if (x == p - 1) {
            printf("\nFOUND DIVISOR for n=%d: p=%lu (k=%lu)\n", n, p, k);
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

    printf("Starting fast search for n=%d using %d threads from k=%lu to %lu...\n", n, NUM_THREADS, start_k, end_k);

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
