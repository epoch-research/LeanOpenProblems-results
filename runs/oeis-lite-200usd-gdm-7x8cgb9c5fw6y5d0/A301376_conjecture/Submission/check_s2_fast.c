#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#define MAX_PRIME 1000000
int primes_4k3[MAX_PRIME / 10];
int primes_4k3_count = 0;
bool is_prime[MAX_PRIME];

void sieve() {
    for (int i = 0; i < MAX_PRIME; i++) {
        is_prime[i] = true;
    }
    is_prime[0] = is_prime[1] = false;
    for (int i = 2; i * i < MAX_PRIME; i++) {
        if (is_prime[i]) {
            for (int j = i * i; j < MAX_PRIME; j += i) {
                is_prime[j] = false;
            }
        }
    }
    for (int i = 2; i < MAX_PRIME; i++) {
        if (is_prime[i] && (i % 4 == 3)) {
            primes_4k3[primes_4k3_count++] = i;
        }
    }
}

bool is_sum_of_two_squares(long long n) {
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
        if (temp % 4 == 3) {
            return false;
        }
    }
    return true;
}

long long f_vals[3] = {4, 26, 314};

int main() {
    sieve();
    printf("Starting search up to n = 10,000,000 using only s in {0,1,2}...\n");
    for (long long n = 3; n < 10000000; n += 2) {
        long long n2 = n * n;
        bool has_sol = false;
        for (int s = 0; s < 3; s++) {
            long long fs = f_vals[s];
            if (fs > n2) continue;
            long long val = fs;
            while (val <= n2) {
                long long rem = n2 - val;
                if (is_sum_of_two_squares(rem)) {
                    has_sol = true;
                    break;
                }
                if (val > n2 / 4) break; // prevent overflow
                val *= 4;
            }
            if (has_sol) break;
        }
        if (!has_sol) {
            printf("COUNTEREXAMPLE FOUND for s in {0,1,2}: n = %lld\n", n);
            return 0;
        }
        if (n % 1999999 == 0) {
            printf("Checked up to %lld\n", n);
        }
    }
    printf("No counterexample found for s in {0,1,2} up to 10,000,000!\n");
    return 0;
}
