#include <iostream>
#include <vector>
#include <cmath>

using namespace std;

typedef unsigned __int128 u128;

unsigned long long power(unsigned long long base, unsigned long long exp, unsigned long long mod) {
    unsigned long long res = 1;
    base %= mod;
    while (exp > 0) {
        if (exp % 2 == 1) res = (u128)res * base % mod;
        base = (u128)base * base % mod;
        exp /= 2;
    }
    return res;
}

bool miller_rabin(unsigned long long n, int a) {
    if (n % a == 0) return false;
    unsigned long long d = n - 1;
    int s = 0;
    while (d % 2 == 0) {
        d /= 2;
        s++;
    }
    unsigned long long x = power(a, d, n);
    if (x == 1 || x == n - 1) return true;
    for (int r = 1; r < s; r++) {
        x = (u128)x * x % n;
        if (x == n - 1) return true;
    }
    return false;
}

bool is_prime(unsigned long long n) {
    if (n < 2) return false;
    if (n == 2 || n == 3 || n == 5 || n == 7) return true;
    if (n % 2 == 0 || n % 3 == 0 || n % 5 == 0 || n % 7 == 0) return false;
    static const int small_primes[] = {
        11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
        101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199
    };
    for (int p : small_primes) {
        if (n % p == 0) return n == p;
    }
    int bases[] = {2, 3, 5, 7, 11, 13, 17};
    for (int a : bases) {
        if (n == a) return true;
        if (!miller_rabin(n, a)) return false;
    }
    return true;
}

int main() {
    int max_n = 512720;
    vector<bool> sieve(max_n + 1, true);
    sieve[0] = sieve[1] = false;
    for (int i = 2; i * i <= max_n; ++i) {
        if (sieve[i]) {
            for (int j = i * i; j <= max_n; j += i) {
                sieve[j] = false;
            }
        }
    }
    vector<int> pi(max_n + 1, 0);
    int cnt = 0;
    for (int i = 1; i <= max_n; ++i) {
        if (sieve[i]) cnt++;
        pi[i] = cnt;
    }

    cout << "Sieve completed. Starting search up to " << max_n << "..." << endl;

    for (int n = 2; n <= max_n; ++n) {
        int pin = pi[n];
        int an = 0;
        unsigned long long n2 = (unsigned long long)n * n;
        for (int s = 1; s < n; ++s) {
            if (is_prime(n2 + (unsigned long long)s * s)) {
                an++;
            }
        }

        if (pin < an) {
            cout << "COUNTEREXAMPLE (pi < a): n = " << n 
                 << ", a(n) = " << an << ", pi(n) = " << pin << endl;
            break;
        }
        if (5 * an < pin) {
            cout << "COUNTEREXAMPLE (5 * a < pi): n = " << n 
                 << ", a(n) = " << an << ", pi(n) = " << pin << endl;
            break;
        }

        if (n % 10000 == 0) {
            cout << "Checked up to " << n << endl;
        }
    }
    return 0;
}
