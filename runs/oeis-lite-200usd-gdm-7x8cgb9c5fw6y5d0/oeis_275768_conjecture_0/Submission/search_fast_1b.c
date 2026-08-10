#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#define LIMIT 1000000000ULL

unsigned char *prime_bitset;

#define GET_BIT(x) (prime_bitset[(x) >> 3] & (1 << ((x) & 7)))
#define CLEAR_BIT(x) (prime_bitset[(x) >> 3] &= ~(1 << ((x) & 7)))

void sieve() {
    size_t size = (LIMIT >> 3) + 1;
    prime_bitset = malloc(size);
    if (!prime_bitset) {
        perror("malloc failed");
        exit(1);
    }
    for (size_t i = 0; i < size; i++) {
        prime_bitset[i] = 0xFF;
    }
    CLEAR_BIT(0);
    CLEAR_BIT(1);
    for (unsigned long long i = 2; i * i < LIMIT; i++) {
        if (GET_BIT(i)) {
            for (unsigned long long j = i * i; j < LIMIT; j += i) {
                CLEAR_BIT(j);
            }
        }
    }
}

int main() {
    printf("Starting sieve to 1 billion...\n");
    sieve();
    printf("Sieve complete.\n");
    
    unsigned long long max_n = LIMIT / 2;
    for (unsigned long long n = 24; n < max_n; n += 6) {
        int cnt = 0;
        for (unsigned long long q = 5; q < n; q += 2) {
            if (GET_BIT(q)) {
                if (GET_BIT(n - q) && GET_BIT(n + q)) {
                    cnt++;
                    if (cnt >= 5) {
                        break;
                    }
                }
            }
        }
        if (cnt < 5) {
            printf("FOUND counterexample: a(%llu) = %d\n", n, cnt);
            return 0;
        }
    }
    printf("No counterexample found up to %llu\n", max_n);
    free(prime_bitset);
    return 0;
}
