#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>

// Fast modular exponentiation: (base ^ exp) % mod
uint64_t power_mod(uint64_t base, uint64_t exp, uint64_t mod) {
    uint64_t res = 1;
    base = base % mod;
    while (exp > 0) {
        if (exp & 1) {
            // Avoid overflow using __int128
            res = (uint64_t)(((unsigned __int128)res * base) % mod);
        }
        base = (uint64_t)(((unsigned __int128)base * base) % mod);
        exp >>= 1;
    }
    return res;
}

// Simple prime check for trial division
bool is_prime(uint64_t n) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0 || n % 3 == 0) return false;
    for (uint64_t i = 5; i * i <= n; i += 6) {
        if (n % i == 0 || n % (i + 2) == 0) return false;
    }
    return true;
}

int main() {
    uint64_t n = 19;
    uint64_t max_p = 2000000000ULL; // 2 billion
    printf("Searching for a prime factor of a(15) up to %llu...\n", max_p);
    
    // We can use a simple wheel sieve or just step through odds
    for (uint64_t p = 3; p < max_p; p += 2) {
        // Compute 2^n mod (p-1)
        uint64_t pow2_n_mod = power_mod(2, n, p - 1);
        
        // Compute 2^pow2_n_mod mod p
        uint64_t t1 = power_mod(2, pow2_n_mod, p);
        
        // Compute 2^n mod p
        uint64_t t2 = power_mod(2, n, p);
        
        if ((t1 + t2) % p == 1) {
            printf("Found factor: %llu\n", p);
            return 0;
        }
    }
    printf("No factor found up to %llu\n", max_p);
    return 0;
}
