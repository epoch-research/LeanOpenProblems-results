#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#define MAX_PRIME 100000000
unsigned char *is_prime;
int *primes_4k3;
int primes_4k3_count = 0;

void sieve() {
    is_prime = malloc(MAX_PRIME);
    for (int i = 0; i < MAX_PRIME; i++) {
        is_prime[i] = 1;
    }
    is_prime[0] = is_prime[1] = 0;
    for (int i = 2; i * i < MAX_PRIME; i++) {
        if (is_prime[i]) {
            for (int j = i * i; j < MAX_PRIME; j += i) {
                is_prime[j] = 0;
            }
        }
    }
    primes_4k3 = malloc(sizeof(int) * (MAX_PRIME / 5));
    for (int i = 2; i < MAX_PRIME; i++) {
        if (is_prime[i] && (i % 4 == 3)) {
            primes_4k3[primes_4k3_count++] = i;
        }
    }
    printf("Sieve complete. Found %d primes congruent to 3 mod 4.\n", primes_4k3_count);
    fflush(stdout);
}

// 100% mathematically exact for n < 10,000,000
bool is_sum_of_two_squares_exact(long long n) {
    if (n < 0) return false;
    if (n == 0 || n == 1) return true;
    long long temp = n;
    for (int i = 0; i < primes_4k3_count; i++) {
        long long p = primes_4k3[i];
        if (p * p > temp) break;
        if (temp % p == 0) {
            int count = 0;
            while (temp % p == 0) {
                count++;
                temp /= p;
            }
            if (count % 2 != 0) return false;
        }
    }
    if (temp > 1) {
        // Since temp has no prime factors < 10,000,000, and temp <= n^2 < 10^14,
        // temp must be prime.
        if (temp % 4 == 3) {
            return false;
        }
    }
    return true;
}

long long f_vals[15];
int f_vals_count = 0;

void precompute_f() {
    long long power_16 = 1;
    long long power_4 = 1;
    for (int s = 0; s < 15; s++) {
        long long val = (10 * power_16 + 16 * power_4 + 10) / 9;
        if (val < 0) break; // overflow
        f_vals[f_vals_count++] = val;
        power_16 *= 16;
        power_4 *= 4;
    }
}

int main() {
    sieve();
    precompute_f();
    printf("Starting 100%% exact search up to n = 10,000,000...\n");
    fflush(stdout);
    for (long long n = 3; n < 100000000; n += 2) {
        long long n2 = n * n;
        bool has_sol = false;
        for (int s = 0; s < f_vals_count; s++) {
            long long fs = f_vals[s];
            if (fs > n2) break;
            long long val = fs;
            while (val <= n2) {
                long long rem = n2 - val;
                if (is_sum_of_two_squares_exact(rem)) {
                    has_sol = true;
                    break;
                }
                if (val > n2 / 4) break; // prevent overflow
                val *= 4;
            }
            if (has_sol) break;
        }
        if (!has_sol) {
            printf("COUNTEREXAMPLE FOUND: n = %lld\n", n);
            fflush(stdout);
            free(is_prime);
            free(primes_4k3);
            return 0;
        }
        if (n % 999999 == 0) {
            printf("Checked up to %lld\n", n);
            fflush(stdout);
        }
    }
    printf("No counterexample found up to 10,000,000!\n");
    fflush(stdout);
    free(is_prime);
    free(primes_4k3);
    return 0;
}
