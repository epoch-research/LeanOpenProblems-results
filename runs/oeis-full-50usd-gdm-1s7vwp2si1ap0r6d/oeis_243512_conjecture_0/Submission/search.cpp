#include <iostream>
#include <vector>
#include <cmath>
#include <numeric>

using namespace std;

// We want to find k up to 10^9 such that:
// s(k) | (1680 * k - sigma(k))
// and q = (1680 * k - sigma(k)) / s(k) is prime,
// and gcd(1680, q) == 1, gcd(k, q) == 1.

const int LIMIT = 100000000;

// Since we cannot fit 10^9 elements in memory easily, we can use a segmented sieve
// or we can just compute sigma(k) on the fly for each k using a fast factorization.
// Actually, factorization on the fly is very fast if we precompute primes up to sqrt(LIMIT).

const int MAX_PRIME = 40000;
vector<int> primes;
bool is_prime_sieve[MAX_PRIME];

void sieve() {
    fill(is_prime_sieve, is_prime_sieve + MAX_PRIME, true);
    is_prime_sieve[0] = is_prime_sieve[1] = false;
    for (int p = 2; p * p < MAX_PRIME; p++) {
        if (is_prime_sieve[p]) {
            for (int i = p * p; i < MAX_PRIME; i += p)
                is_prime_sieve[i] = false;
        }
    }
    for (int p = 2; p < MAX_PRIME; p++) {
        if (is_prime_sieve[p]) primes.push_back(p);
    }
}

long long get_sigma(long long n) {
    long long temp = n;
    long long sum = 1;
    for (int p : primes) {
        if ((long long)p * p > temp) break;
        if (temp % p == 0) {
            long long p_pow = p;
            long long cur_sum = 1 + p;
            temp /= p;
            while (temp % p == 0) {
                p_pow *= p;
                cur_sum += p_pow;
                temp /= p;
            }
            sum *= cur_sum;
        }
    }
    if (temp > 1) {
        sum *= (1 + temp);
    }
    return sum;
}

bool is_prime(long long n) {
    if (n < 2) return false;
    for (long long p : primes) {
        if (p * p > n) break;
        if (n % p == 0) return false;
    }
    for (long long d = MAX_PRIME; d * d <= n; d += 2) {
        if (n % d == 0) return false;
    }
    return true;
}

long long gcd(long long a, long long b) {
    return std::gcd(a, b);
}

int main() {
    sieve();
    cout << "Sieve completed. Primes count: " << primes.size() << endl;
    long long n = 1680;
    for (long long k = 2; k < LIMIT; k++) {
        if (k % 50000000 == 0) {
            cout << "Checked up to " << k << endl;
        }
        long long sig_k = get_sigma(k);
        long long s_k = sig_k - k;
        if (s_k == 0) continue;
        long long num = n * k - sig_k;
        if (num <= 0) continue;
        if (num % s_k == 0) {
            long long q = num / s_k;
            if (q <= 1) continue;
            if (is_prime(q)) {
                if (gcd(n, q) == 1 && gcd(k, q) == 1) {
                    cout << "FOUND: k=" << k << ", q=" << q << ", i=" << k * q << endl;
                    return 0;
                }
            }
        }
    }
    cout << "Not found up to " << LIMIT << endl;
    return 0;
}
