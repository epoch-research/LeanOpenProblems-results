#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <math.h>

#define LIMIT 1000000000
#define MAX_VAL 2000000000LL

// Use a bitset for prime sieve to save memory and cache
unsigned char *is_prime;
int *prime_count;

void sieve() {
    is_prime = malloc(MAX_VAL / 8 + 1);
    prime_count = malloc(MAX_VAL * sizeof(int));
    if (!is_prime || !prime_count) {
        printf("Memory allocation failed!\n");
        exit(1);
    }
    for (long long i = 0; i < MAX_VAL / 8 + 1; i++) is_prime[i] = 0xFF;
    // 0 and 1 are not prime
    is_prime[0] &= ~3; // clear bit 0 and 1
    for (long long i = 2; i * i < MAX_VAL; i++) {
        if (is_prime[i / 8] & (1 << (i % 8))) {
            for (long long j = i * i; j < MAX_VAL; j += i) {
                is_prime[j / 8] &= ~(1 << (j % 8));
            }
        }
    }
    int count = 0;
    for (long long i = 0; i < MAX_VAL; i++) {
        if ((is_prime[i / 8] & (1 << (i % 8))) != 0) {
            count++;
        }
        prime_count[i] = count;
    }
}

inline bool is_p(long long x) {
    if (x < 0 || x >= MAX_VAL) return false;
    return (is_prime[x / 8] & (1 << (x % 8))) != 0;
}

inline bool has_prime_in_range(long long low, long long high) {
    if (low > high) return false;
    if (low < 0) low = 0;
    int count_high = prime_count[high];
    int count_low_minus_1 = (low == 0) ? 0 : prime_count[low - 1];
    return count_high > count_low_minus_1;
}

int main() {
    printf("Starting sieve up to 2 billion...\n");
    sieve();
    printf("Sieve completed.\n");
    
    // We can check each n
    for (int n = 3; n <= LIMIT; n++) {
        bool found = false;
        int r_start = (int)sqrt(n + 2);
        int r_end = (int)sqrt(2 * n - 1);
        for (int r = r_start; r <= r_end; r++) {
            if (is_p(r)) {
                int low = r * r - n;
                int high = (r + 1) * (r + 1) - 1 - n;
                if (high >= n) high = n - 1;
                if (has_prime_in_range(low, high)) {
                    found = true;
                    break;
                }
            }
        }
        if (!found) {
            printf("COUNTEREXAMPLE FOUND: n = %d\n", n);
            return 0;
        }
        if (n % 100000000 == 0) {
            printf("Checked up to %d\n", n);
        }
    }
    printf("Checked all n up to 1 billion. No counterexamples found!\n");
    return 0;
}
