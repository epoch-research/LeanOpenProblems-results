#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <omp.h>

#define MAX_PRIME 2000000
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
    printf("Sieve complete. Found %d primes congruent to 3 mod 4 under %d.\n", primes_4k3_count, MAX_PRIME);
    fflush(stdout);
}

long long gcd(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

long long pollard_rho(long long n) {
    if (n < 2) return 1;
    if (n % 2 == 0) return 2;
    long long x = 2, y = 2, d = 1, c = 1;
    while (d == 1) {
        x = ((__int128)x * x + c) % n;
        y = ((__int128)y * y + c) % n;
        y = ((__int128)y * y + c) % n;
        long long diff = x > y ? x - y : y - x;
        d = gcd(diff, n);
        if (d == n) {
            // Try different c
            x = 2; y = 2; d = 1; c++;
        }
    }
    return d;
}

bool miller_rabin_prime(long long n) {
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
        if (miller_rabin_prime(temp)) {
            if (temp % 4 == 3) return false;
        } else {
            long long q1 = pollard_rho(temp);
            if (q1 > 1 && q1 < temp) {
                long long q2 = temp / q1;
                // Recursively check q1 and q2 or check their congruences if they are prime
                if (miller_rabin_prime(q1) && miller_rabin_prime(q2)) {
                    if ((q1 % 4 == 3) != (q2 % 4 == 3)) return false;
                    if (q1 % 4 == 3 && q2 % 4 == 3) {
                        if (q1 != q2) return false;
                    }
                } else {
                    return is_sum_of_two_squares_exact(q1) && is_sum_of_two_squares_exact(q2);
                }
            }
        }
    }
    return true;
}

long long f_vals[20];
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
    printf("Starting parallel exact ultra-fast search from n = 3 to 1,000,000,000...\n");
    fflush(stdout);

    long long found_n = -1;

    #pragma omp parallel for schedule(dynamic, 1000)
    for (long long n = 3; n < 1000000000; n += 2) {
        if (found_n != -1) continue;

        long long n2 = n * n;
        bool has_sol = false;

        // Check v = 1 first
        if (is_sum_of_two_squares_exact(n2 - 1)) {
            has_sol = true;
        }

        if (!has_sol) {
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
        }

        if (!has_sol) {
            #pragma omp critical
            {
                if (found_n == -1 || n < found_n) {
                    found_n = n;
                    printf("\nFOUND COUNTEREXAMPLE N = %lld\n", n);
                    fflush(stdout);
                }
            }
        }

        if (n % 1000000 == 1 && omp_get_thread_num() == 0) {
            printf("Checked up to N = %lld...\n", n);
            fflush(stdout);
        }
    }

    if (found_n != -1) {
        printf("\nSUCCESS! Absolute smallest counterexample found: N = %lld\n", found_n);
    } else {
        printf("Finished search with no counterexample found.\n");
    }
    return 0;
}
