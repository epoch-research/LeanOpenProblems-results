#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <math.h>

#define MAX_VAL 3000000

bool is_prime[MAX_VAL];
int primes[MAX_VAL];
int num_primes = 0;

void sieve() {
    for (int i = 0; i < MAX_VAL; i++) is_prime[i] = true;
    is_prime[0] = is_prime[1] = false;
    for (int i = 2; i * i < MAX_VAL; i++) {
        if (is_prime[i]) {
            for (int j = i * i; j < MAX_VAL; j += i) {
                is_prime[j] = false;
            }
        }
    }
    for (int i = 2; i < MAX_VAL; i++) {
        if (is_prime[i]) {
            primes[num_primes++] = i;
        }
    }
}

int main() {
    sieve();
    printf("Sieve completed. Primes: %d\n", num_primes);
    
    for (int n = 3; n <= 1000000; n++) {
        bool found = false;
        for (int i = 0; i < num_primes; i++) {
            int p = primes[i];
            if (p >= n) break;
            int val = (int)sqrt(n + p);
            if (is_prime[val]) {
                found = true;
                break;
            }
        }
        if (!found) {
            printf("Counterexample found: n = %d\n", n);
            return 0;
        }
    }
    printf("No counterexamples found up to 1,000,000.\n");
    return 0;
}
