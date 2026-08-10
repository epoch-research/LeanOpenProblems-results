#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <pthread.h>

typedef unsigned __int128 uint128_t;

int check_factor(int n, uint64_t factor) {
    uint128_t b = 10;
    for (int i = 0; i < n; i++) {
        b = (b * b) % factor;
    }
    return b == factor - 1;
}

#define NUM_THREADS 32

typedef struct {
    int n;
    uint64_t start_k;
    uint64_t end_k;
    uint64_t step;
} ThreadArg;

void* search_thread(void* arg) {
    ThreadArg* t_arg = (ThreadArg*)arg;
    uint64_t step = t_arg->step;
    int n = t_arg->n;
    for (uint64_t k = t_arg->start_k; k < t_arg->end_k; k++) {
        uint64_t factor = k * step + 1;
        if (check_factor(n, factor)) {
            printf("FOUND FACTOR for n=%d: %llu (k=%llu)\n", n, (unsigned long long)factor, (unsigned long long)k);
            fflush(stdout);
            exit(0);
        }
    }
    return NULL;
}

void search(int n, uint64_t max_k) {
    uint64_t step = 1ULL << (n + 1);
    printf("Searching for n=%d, step=%llu up to k=%llu\n", n, (unsigned long long)step, (unsigned long long)max_k);
    fflush(stdout);
    
    pthread_t threads[NUM_THREADS];
    ThreadArg args[NUM_THREADS];
    uint64_t chunk = max_k / NUM_THREADS;
    
    for (int i = 0; i < NUM_THREADS; i++) {
        args[i].n = n;
        args[i].step = step;
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
        printf("Usage: %s <n> <max_k_in_millions>\n", argv[0]);
        return 1;
    }
    int n = atoi(argv[1]);
    uint64_t max_k = atoll(argv[2]) * 1000000ULL;
    search(n, max_k);
    return 0;
}
