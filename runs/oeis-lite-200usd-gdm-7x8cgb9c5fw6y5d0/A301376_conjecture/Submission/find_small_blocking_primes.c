#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <omp.h>

#define PRIME_LIMIT 2000000000LL

int primes_3mod4[60000000];
int primes_count = 0;

bool is_prime(long long n) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0) return false;
    long long d = n - 1;
    int s = 0;
    while (d % 2 == 0) {
        d /= 2;
        s++;
    }
    long long bases[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (int i = 0; i < 12; i++) {
        long long a = bases[i];
        if (a >= n) break;
        long long x = 1;
        long long base = a % n;
        long long exp = d;
        while (exp > 0) {
            if (exp % 2 == 1) x = (__int128)x * base % n;
            base = (__int128)base * base % n;
            exp /= 2;
        }
        if (x == 1 || x == n - 1) continue;
        bool composite = true;
        for (int r = 1; r < s; r++) {
            x = (__int128)x * x % n;
            if (x == n - 1) {
                composite = false;
                break;
            }
        }
        if (composite) return false;
    }
    return true;
}

void init_primes() {
    printf("Allocating 2 GB memory for sieve...\n");
    fflush(stdout);
    char *is_prime_b = malloc(PRIME_LIMIT);
    if (!is_prime_b) {
        printf("Failed to allocate memory for sieve.\n");
        exit(1);
    }
    printf("Initializing sieve array...\n");
    fflush(stdout);
    for (long long i = 0; i < PRIME_LIMIT; i++) is_prime_b[i] = 1;
    is_prime_b[0] = is_prime_b[1] = 0;
    printf("Sieving up to 2 billion...\n");
    fflush(stdout);
    for (long long i = 2; i * i < PRIME_LIMIT; i++) {
        if (is_prime_b[i]) {
            for (long long j = i * i; j < PRIME_LIMIT; j += i) {
                is_prime_b[j] = 0;
            }
        }
    }
    printf("Collecting primes congruent to 3 mod 4...\n");
    fflush(stdout);
    for (long long i = 3; i < PRIME_LIMIT; i++) {
        if (is_prime_b[i] && (i % 4 == 3)) {
            primes_3mod4[primes_count++] = i;
        }
    }
    free(is_prime_b);
    printf("Initialized %d primes congruent to 3 mod 4 under 2 billion.\n", primes_count);
}

long long f_vals[300];
int f_vals_count = 0;

void precompute_f() {
    f_vals[f_vals_count++] = 1; // 1 is at index 199 in Lean
    long long power_16 = 1;
    for (int s = 0; s < 11; s++) {
        long long fs = (10 * power_16 + 16 * (power_16 / (1LL << (2 * s))) + 10) / 9;
        // Wait, let's write fs more robustly:
        // fs = (10 * 16^s + 16 * 4^s + 10) / 9
        long long p16 = 1;
        for (int j = 0; j < s; j++) p16 *= 16;
        long long p4 = 1;
        for (int j = 0; j < s; j++) p4 *= 4;
        long long val = (10 * p16 + 16 * p4 + 10) / 9;
        
        long long p4_i = 1;
        for (int i = 0; i < 20; i++) {
            long long v = val * p4_i;
            // Let's add unique values of v to f_vals
            bool exists = false;
            for (int k = 0; k < f_vals_count; k++) {
                if (f_vals[k] == v) {
                    exists = true;
                    break;
                }
            }
            if (!exists) {
                f_vals[f_vals_count++] = v;
            }
            p4_i *= 4;
        }
    }
    
    // Sort f_vals
    for (int i = 0; i < f_vals_count - 1; i++) {
        for (int j = i + 1; j < f_vals_count; j++) {
            if (f_vals[i] > f_vals[j]) {
                long long tmp = f_vals[i];
                f_vals[i] = f_vals[j];
                f_vals[j] = tmp;
            }
        }
    }
    printf("Precomputed %d unique values of v.\n", f_vals_count);
}

int main() {
    init_primes();
    precompute_f();

    printf("Starting parallel search for N...\n");
    fflush(stdout);

    long long found_N = -1;

    #pragma omp parallel for schedule(dynamic, 1000)
    for (long long N = 1105300; N < 2000000LL; N++) {
        if (found_N != -1 && N >= found_N) continue;

        long long N2 = N * N;
        bool all_blocked = true;

        for (int idx = 0; idx < f_vals_count; idx++) {
            long long v = f_vals[idx];
            if (v >= N2) continue;

            long long diff = N2 - v;
            bool blocked = false;
            for (int p_idx = 0; p_idx < primes_count; p_idx++) {
                long long p = primes_3mod4[p_idx];
                if (p * p > diff) {
                    if (diff % 4 == 3 && is_prime(diff)) {
                        blocked = true;
                    }
                    break;
                }
                if (diff % p == 0) {
                    if ((diff / p) % p != 0) {
                        blocked = true;
                        break;
                    }
                }
            }
            if (!blocked) {
                all_blocked = false;
                break;
            }
        }

        if (all_blocked) {
            #pragma omp critical
            {
                if (found_N == -1 || N < found_N) {
                    found_N = N;
                    printf("\nFOUND SUCCESSFUL N = %lld\n", N);
                    fflush(stdout);
                }
            }
        }

        if (N % 100000 == 0 && omp_get_thread_num() == 0) {
            printf("Checked N up to %lld...\n", N);
            fflush(stdout);
        }
    }

    if (found_N != -1) {
        printf("\nSUCCESS! N = %lld\n", found_N);
    } else {
        printf("\nFailed to find any N.\n");
    }

    return 0;
}
