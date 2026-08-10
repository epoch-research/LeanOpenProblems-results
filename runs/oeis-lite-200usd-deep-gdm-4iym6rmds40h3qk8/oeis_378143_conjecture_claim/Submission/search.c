#include <stdio.h>
#include <stdint.h>

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

void search(int n, uint64_t max_k) {
    uint64_t step = 1ULL << (n + 1);
    uint64_t exp = 1ULL << n;
    printf("Searching for n=%d, step=%llu, exp=%llu\n", n, (unsigned long long)step, (unsigned long long)exp);
    for (uint64_t k = 1; k < max_k; k++) {
        uint64_t factor = k * step + 1;
        // Check if pow_mod(10, exp, factor) == factor - 1
        if (pow_mod(10, exp, factor) == factor - 1) {
            printf("Found factor for n=%d: %llu (k=%llu)\n", n, (unsigned long long)factor, (unsigned long long)k);
            return;
        }
    }
    printf("No factor found for n=%d up to k=%llu\n", n, (unsigned long long)max_k);
}

int main() {
    search(10, 10000000000ULL);
    search(13, 10000000000ULL);
    search(14, 10000000000ULL);
    return 0;
}
