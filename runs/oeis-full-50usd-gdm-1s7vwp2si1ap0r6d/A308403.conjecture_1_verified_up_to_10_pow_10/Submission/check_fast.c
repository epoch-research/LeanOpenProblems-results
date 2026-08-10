#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <time.h>

#define LIMIT 21000000000ULL

// We only store odd numbers. index i represents 2*i + 1.
// 2*i+1 < LIMIT => 2*i < LIMIT-1 => i < LIMIT/2.
#define SIEVE_SIZE (LIMIT / 16 + 1)
uint8_t *sieve_array;

uint64_t *primes;
uint64_t prime_count = 0;
uint64_t *S;
uint8_t *in_S;

void bit_sieve() {
    printf("Allocating sieve_array of size %llu MB...\n", SIEVE_SIZE / (1024 * 1024));
    sieve_array = malloc(SIEVE_SIZE);
    if (!sieve_array) {
        printf("Failed to allocate sieve_array\n");
        exit(1);
    }
    for (uint64_t i = 0; i < SIEVE_SIZE; i++) sieve_array[i] = 0xFF;
    
    // 1 is not prime (represented by i = 0, i.e., 2*0+1 = 1)
    sieve_array[0] &= ~1;

    printf("Sieving...\n");
    for (uint64_t p = 3; p * p < LIMIT; p += 2) {
        uint64_t i = p >> 1;
        if (sieve_array[i >> 3] & (1 << (i & 7))) {
            for (uint64_t j = p * p; j < LIMIT; j += 2 * p) {
                uint64_t k = j >> 1;
                sieve_array[k >> 3] &= ~(1 << (k & 7));
            }
        }
    }

    // count primes (including 2)
    prime_count = 1; // for 2
    for (uint64_t i = 1; 2 * i + 1 < LIMIT; i++) {
        if (sieve_array[i >> 3] & (1 << (i & 7))) {
            prime_count++;
        }
    }
    printf("Found %lu primes\n", prime_count);

    primes = malloc(prime_count * sizeof(uint64_t));
    if (!primes) {
        printf("Failed to allocate primes\n");
        exit(1);
    }
    primes[0] = 2;
    uint64_t idx = 1;
    for (uint64_t i = 1; 2 * i + 1 < LIMIT; i++) {
        if (sieve_array[i >> 3] & (1 << (i & 7))) {
            primes[idx++] = 2 * i + 1;
        }
    }
    free(sieve_array);
}

int main() {
    time_t start = time(NULL);
    bit_sieve();
    printf("Sieve took %ld seconds\n", time(NULL) - start);

    printf("Computing S...\n");
    S = malloc((prime_count + 1) * sizeof(uint64_t));
    if (!S) {
        printf("Failed to allocate S\n");
        exit(1);
    }
    S[1] = 2;
    uint64_t max_S = 2;
    for (uint64_t k = 2; k <= prime_count; k++) {
        S[k] = primes[k-1] - S[k-1];
        if (S[k] > max_S) max_S = S[k];
    }
    printf("Max S: %lu\n", max_S);

    in_S = calloc(max_S / 8 + 1, 1);
    if (!in_S) {
        printf("Failed to allocate in_S\n");
        exit(1);
    }
    for (uint64_t k = 1; k <= prime_count; k++) {
        in_S[S[k] >> 3] |= (1 << (S[k] & 7));
    }

    printf("Searching for counterexample...\n");
    uint64_t search_limit = 10000000000ULL; // 10^10
    for (uint64_t n = 3; n < search_limit; n++) {
        if (n % 100000000 == 0) {
            printf("Checked up to %lu...\n", n);
            fflush(stdout);
        }
        bool found = false;
        // try powers of 6
        uint64_t pow6 = 1;
        while (pow6 < n) {
            // try powers of 3
            uint64_t pow3 = 1;
            while (pow6 + pow3 < n) {
                uint64_t rem = n - (pow6 + pow3);
                if (rem <= max_S && (in_S[rem >> 3] & (1 << (rem & 7)))) {
                    found = true;
                    break;
                }
                pow3 *= 3;
            }
            if (found) break;
            pow6 *= 6;
        }
        if (!found) {
            printf("COUNTEREXAMPLE FOUND: %lu\n", n);
            return 0;
        }
    }
    printf("No counterexamples found up to %lu\n", search_limit);
    return 0;
}
