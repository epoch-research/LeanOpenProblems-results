#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <time.h>

#define LIMIT 21000000000ULL
#define SIEVE_SIZE (LIMIT / 16 + 1)

// We only store odd numbers. index i represents 2*i + 1.
uint8_t *sieve_array;

#define IN_S_LIMIT 10000000000ULL
#define IN_S_SIZE (IN_S_LIMIT / 8 + 1)
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
    printf("Sieving completed.\n");
}

int main() {
    setvbuf(stdout, NULL, _IONBF, 0);
    time_t start = time(NULL);
    bit_sieve();
    printf("Sieve took %ld seconds\n", time(NULL) - start);

    printf("Allocating in_S of size %llu MB...\n", IN_S_SIZE / (1024 * 1024)); // Wait, IN_S_SIZE
    in_S = calloc(IN_S_SIZE, 1);
    if (!in_S) {
        printf("Failed to allocate in_S\n");
        exit(1);
    }

    printf("Computing S on the fly...\n");
    // S[1] = 2, from prime 2
    uint64_t prev_S = 2;
    in_S[2 >> 3] |= (1 << (2 & 7));

    uint64_t k = 2;
    for (uint64_t i = 1; 2 * i + 1 < LIMIT; i++) {
        if (sieve_array[i >> 3] & (1 << (i & 7))) {
            uint64_t p = 2 * i + 1;
            uint64_t curr_S = p - prev_S;
            if (curr_S < IN_S_LIMIT) {
                in_S[curr_S >> 3] |= (1 << (curr_S & 7));
            }
            prev_S = curr_S;
            k++;
        }
    }
    printf("Computed S up to k=%lu. Freeing sieve_array...\n", k);
    free(sieve_array);

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
                if (rem < IN_S_LIMIT && (in_S[rem >> 3] & (1 << (rem & 7)))) {
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
