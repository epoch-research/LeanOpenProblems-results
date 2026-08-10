#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

// Modular multiplication (a * b) % m
static inline uint64_t mul_mod(uint64_t a, uint64_t b, uint64_t m) {
    return (uint64_t)(((__int128)a * b) % m);
}

// Modular exponentiation (base ^ exp) % m
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

void search(int n, uint64_t max_k) {
    printf("Searching factors for n=%d up to k=%llu...\n", n, (unsigned long long)max_k);
    uint64_t step = 1ULL << (n + 1);
    uint64_t exp = 1ULL << n;
    for (uint64_t k = 1; k <= max_k; k++) {
        uint64_t p = k * step + 1;
        // Check 10^(2^n) % p
        if (power_mod(10, exp, p) == p - 1) {
            if (is_prime(p)) {
                printf("FOUND FACTOR for n=%d: %llu (k=%llu)\n", n, (unsigned long long)p, (unsigned long long)k);
                return;
            }
        }
    }
    printf("No factor found for n=%d under k=%llu\n", n, (unsigned long long)max_k);
}

int main() {
    search(13, 200000000ULL);
    search(14, 200000000ULL);
    return 0;
}
