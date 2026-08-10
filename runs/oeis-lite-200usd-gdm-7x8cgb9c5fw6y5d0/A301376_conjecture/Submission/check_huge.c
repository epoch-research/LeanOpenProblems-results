#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#define MAX_PRIME 10000000
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
            // Since we sieved up to 10M, if temp is > 1 and temp < 100M,
            // we can test if it is prime. But since temp * temp > 100M could happen,
            // actually if temp > 1 and temp < 10^14 (since p * p > temp and max p is 10M),
            // and temp has no prime factors < 10M, then temp is either a prime or a product of two primes >= 10M.
            // If temp is prime, we just check if temp % 4 == 3.
            // If temp is product of two primes >= 10M, say q1 * q2,
            // since q1, q2 >= 10M, and temp <= n^2 <= 10^{16}.
            // Actually, we can just do a primality test or just check if temp % 4 == 3.
            // Wait, if temp is prime, temp % 4 == 3 => false.
            // If temp = q1 * q2:
            // If q1 % 4 == 3 and q2 % 4 == 3, then temp % 4 == 1. But count for each is 1, so it is NOT sum of two squares.
            // If one is 3 and one is 1, temp % 4 == 3, not sum of two squares.
            // If both are 1, temp % 4 == 1, is sum of two squares.
            // So if temp = q1 * q2, if temp % 4 == 3, it is definitely not a sum of two squares.
            // If temp % 4 == 1, is it possible that it is not sum of two squares?
            // Yes, if q1 % 4 == 3 and q2 % 4 == 3.
            // But this only happens if temp is composite with prime factors >= 10M.
            // If n <= 10^8, n^2 <= 10^{16}, and we check rem = n^2 - val.
            // If we want absolute correctness, we can do a Miller-Rabin or simple check.
            // Let's implement a simple Miller-Rabin or trial division for temp up to 10^{16}.
            // Actually, a simple primality test:
            if (temp % 4 == 3) {
                return false; // If it's prime or has a prime factor of 3 mod 4 to odd power, it's false.
            }
            // If temp % 4 == 1, could it be q1 * q2 with q1, q2 = 3 mod 4?
            // We can check if temp is a perfect square of a 3 mod 4 prime (impossible since q1 != q2 as q1*q2 >= 10^14).
            // Actually, we can just check if temp is prime using a simple Miller-Rabin with bases 2, 13, 23, 1662803.
        }
    }
    return true;
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
        // temp has no prime factors < 10M.
        // If temp is prime, we check if temp % 4 == 3.
        if (miller_rabin_prime(temp)) {
            if (temp % 4 == 3) return false;
        } else {
            // temp is composite with all prime factors >= 10M.
            // Since temp <= 10^{16}, and prime factors >= 10^7,
            // temp can only be q1 * q2 where q1, q2 >= 10^7.
            // Let's find q1, q2.
            // Actually, we can just find them by trial division starting from 10M,
            // or we can use SQUFOF/Pollard rho. But since q1, q2 >= 10^7 and temp <= 10^{16},
            // q1 must be <= 10^8, which is very small! We can just find it using a loop from 10M to 100M.
            long long q1 = 0;
            for (long long f = 10000001; f * f <= temp; f += 2) {
                if (temp % f == 0) {
                    q1 = f;
                    break;
                }
            }
            if (q1 > 0) {
                long long q2 = temp / q1;
                // Since q1 and q2 are primes (since temp <= 10^{16} and both >= 10^7),
                // we just check their congruences modulo 4.
                if ((q1 % 4 == 3) != (q2 % 4 == 3)) { // one is 3, one is 1
                    return false;
                }
                if (q1 % 4 == 3 && q2 % 4 == 3) {
                    if (q1 != q2) return false; // q1^1 * q2^1 -> odd exponents
                }
            } else {
                // Should not happen unless temp is prime, which is handled by miller_rabin_prime.
            }
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
    printf("Starting search up to n = 1,000,000...\n");
    for (long long n = 3; n < 1000000; n += 2) {
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
            free(is_prime);
            free(primes_4k3);
            return 0;
        }
        if (n % 1999999 == 0) {
            printf("Checked up to %lld\n", n);
        }
    }
    printf("No counterexample found up to 100,000,000!\n");
    free(is_prime);
    free(primes_4k3);
    return 0;
}
