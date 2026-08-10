#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <time.h>
#include <omp.h>

static inline uint64_t mul_mod(uint64_t a, uint64_t b, uint64_t m) {
    return (uint64_t)(((__int128)a * b) % m);
}

uint64_t power_mod(uint64_t base, uint64_t exp, uint64_t m) {
    uint64_t res = 1;
    base = base % m;
    while (exp > 0) {
        if (exp & 1) res = mul_mod(res, base, m);
        base = mul_mod(base, base, m);
        exp >>= 1;
    }
    return res;
}

bool is_prime(uint64_t n) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0 || n % 3 == 0) return false;
    for (uint64_t i = 5; i * i <= n; i += 6) {
        if (n % i == 0 || n % (i + 2) == 0) return false;
    }
    return true;
}

int main(int argc, char** argv) {
    if (argc < 4) {
        printf("Usage: %s <n> <start_k> <end_k>\n", argv[0]);
        return 1;
    }
    int n = atoi(argv[1]);
    uint64_t start_k = strtoull(argv[2], NULL, 10);
    uint64_t end_k = strtoull(argv[3], NULL, 10);

    uint64_t step = 1ULL << (n + 1);
    uint64_t exp = 1ULL << n;

    printf("Searching for n=%d, k in [%llu, %llu], step=%llu using %d threads...\n", 
           n, (unsigned long long)start_k, (unsigned long long)end_k, 
           (unsigned long long)step, omp_get_max_threads());

    double start_time = omp_get_wtime();
    volatile bool found = false;

    #pragma omp parallel for schedule(dynamic, 100000)
    for (uint64_t k = start_k; k < end_k; k++) {
        if (found) continue;
        uint64_t p = k * step + 1;
        if (power_mod(10, exp, p) == p - 1) {
            if (is_prime(p)) {
                #pragma omp critical
                {
                    if (!found) {
                        double end_time = omp_get_wtime();
                        printf("\nFOUND FACTOR for n=%d: %llu (k=%llu) in %.2fs\n", 
                               n, (unsigned long long)p, (unsigned long long)k, end_time - start_time);
                        found = true;
                    }
                }
            }
        }
    }

    double end_time = omp_get_wtime();
    if (!found) {
        printf("No factor found in range [%llu, %llu] in %.2fs\n", 
               (unsigned long long)start_k, (unsigned long long)end_k, end_time - start_time);
    }
    return 0;
}
