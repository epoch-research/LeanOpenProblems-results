#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <math.h>

#define MAX_PRIME 1000000
bool is_prime[MAX_PRIME];
int primes_4k3[MAX_PRIME];
int primes_4k3_count = 0;

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
        if (temp < MAX_PRIME) {
            if (is_prime[temp] && (temp % 4 == 3)) {
                return false;
            }
        } else {
            // Since temp <= n2 < 10^14 and MAX_PRIME is 10^6,
            // if temp has no prime factors < 10^6, then temp must be prime!
            if (temp % 4 == 3) {
                return false;
            }
        }
    }
    return true;
}

bool has_actual_solution(long long N) {
    long long N2 = N * N;
    // We search over all u <= v such that 2^(v-1) <= N
    // 2^(v-1) <= N => v - 1 <= log2(N) => v <= log2(N) + 1
    int max_v = (int)(log2(N)) + 2;
    for (int v = 0; v <= max_v; v++) {
        for (int u = 0; u <= v; u++) {
            // (2^v - 2^u) % 6 == 0
            long long pow_v = 1ULL << v;
            long long pow_u = 1ULL << u;
            if ((pow_v - pow_u) % 6 == 0) {
                long long x = (pow_v + pow_u) / 2;
                long long y = (pow_v - pow_u) / 6;
                long long val = x*x + y*y;
                if (val <= N2) {
                    if (is_sum_of_two_squares(N2 - val)) {
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

int main() {
    sieve();
    printf("Sieve complete. Primes congruent to 3 mod 4: %d\n", primes_4k3_count);
    printf("Searching for the smallest true counterexample N...\n");
    for (long long N = 1; N < 1000000; N++) {
        if (N % 10000 == 0) {
            printf("Checked up to %lld...\n", N);
            fflush(stdout);
        }
        if (!has_actual_solution(N)) {
            printf("FOUND TRUE COUNTEREXAMPLE! N = %lld\n", N);
            return 0;
        }
    }
    printf("No true counterexample found up to 10,000,000!\n");
    return 0;
}
