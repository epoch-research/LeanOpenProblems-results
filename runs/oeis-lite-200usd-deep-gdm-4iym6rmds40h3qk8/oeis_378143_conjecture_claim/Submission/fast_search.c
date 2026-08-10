#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <pthread.h>

typedef unsigned __int128 uint128_t;

uint64_t pow_mod(uint64_t base, uint64_t exp, uint64_t mod) {
    uint128_t res = 1;
    uint128_t b = base % mod;
    while (exp > 0) {
        if (exp & 1) res = (res * b) % mod;
        b = (b * b) % mod;
        exp >>= 1;
    }
    return (uint64_t)res;
}

#define NUM_THREADS 32

typedef struct {
    int n;
    uint64_t start_k;
    uint64_t end_k;
    uint64_t step;
    uint64_t exp;
} ThreadArg;

int check_factor_13(uint64_t factor) {
    uint128_t b = 10;
    b = (b * b) % factor; // 10^2
    b = (b * b) % factor; // 10^4
    b = (b * b) % factor; // 10^8
    b = (b * b) % factor; // 10^16
    b = (b * b) % factor; // 10^32
    b = (b * b) % factor; // 10^64
    b = (b * b) % factor; // 10^128
    b = (b * b) % factor; // 10^256
    b = (b * b) % factor; // 10^512
    b = (b * b) % factor; // 10^1024
    b = (b * b) % factor; // 10^2048
    b = (b * b) % factor; // 10^4096
    b = (b * b) % factor; // 10^8192
    return b == factor - 1;
}

int check_factor_14(uint64_t factor) {
    uint128_t b = 10;
    b = (b * b) % factor; // 10^2
    b = (b * b) % factor; // 10^4
    b = (b * b) % factor; // 10^8
    b = (b * b) % factor; // 10^16
    b = (b * b) % factor; // 10^32
    b = (b * b) % factor; // 10^64
    b = (b * b) % factor; // 10^128
    b = (b * b) % factor; // 10^256
    b = (b * b) % factor; // 10^512
    b = (b * b) % factor; // 10^1024
    b = (b * b) % factor; // 10^2048
    b = (b * b) % factor; // 10^4096
    b = (b * b) % factor; // 10^8192
    b = (b * b) % factor; // 10^16384
    return b == factor - 1;
}

void* search_thread(void* arg) {
    ThreadArg* t_arg = (ThreadArg*)arg;
    uint64_t step = t_arg->step;
    uint64_t exp = t_arg->exp;
    int n = t_arg->n;
    printf("Thread started: start_k=%llu, end_k=%llu\n", (unsigned long long)t_arg->start_k, (unsigned long long)t_arg->end_k);
    if (n == 13) {
        for (uint64_t k = t_arg->start_k; k < t_arg->end_k; k++) {
            uint64_t factor = k * step + 1;
            if (check_factor_13(factor)) {
                printf("FOUND FACTOR for n=%d: %llu (k=%llu)\n", n, (unsigned long long)factor, (unsigned long long)k);
                exit(0);
            }
        }
    } else if (n == 14) {
        for (uint64_t k = t_arg->start_k; k < t_arg->end_k; k++) {
            uint64_t factor = k * step + 1;
            if (check_factor_14(factor)) {
                printf("FOUND FACTOR for n=%d: %llu (k=%llu)\n", n, (unsigned long long)factor, (unsigned long long)k);
                exit(0);
            }
        }
    } else {
        for (uint64_t k = t_arg->start_k; k < t_arg->end_k; k++) {
            uint64_t factor = k * step + 1;
            if (pow_mod(10, exp, factor) == factor - 1) {
                printf("FOUND FACTOR for n=%d: %llu (k=%llu)\n", n, (unsigned long long)factor, (unsigned long long)k);
                exit(0);
            }
        }
    }
    return NULL;
}

void search(int n, uint64_t max_k) {
    uint64_t step = 1ULL << (n + 1);
    uint64_t exp = 1ULL << n;
    printf("Searching for n=%d, step=%llu, exp=%llu up to k=%llu\n", n, (unsigned long long)step, (unsigned long long)exp, (unsigned long long)max_k);
    
    pthread_t threads[NUM_THREADS];
    ThreadArg args[NUM_THREADS];
    uint64_t chunk = max_k / NUM_THREADS;
    
    for (int i = 0; i < NUM_THREADS; i++) {
        args[i].n = n;
        args[i].step = step;
        args[i].exp = exp;
        args[i].start_k = 1 + i * chunk;
        args[i].end_k = (i == NUM_THREADS - 1) ? max_k : (1 + (i + 1) * chunk);
        pthread_create(&threads[i], NULL, search_thread, &args[i]);
    }
    
    for (int i = 0; i < NUM_THREADS; i++) {
        pthread_join(threads[i], NULL);
    }
}

int main(int argc, char** argv) {
    if (argc < 3) {
        printf("Usage: %s <n> <max_k_in_billions>\n", argv[0]);
        return 1;
    }
    int n = atoi(argv[1]);
    uint64_t max_k = atoll(argv[2]) * 1000000000ULL;
    search(n, max_k);
    return 0;
}
