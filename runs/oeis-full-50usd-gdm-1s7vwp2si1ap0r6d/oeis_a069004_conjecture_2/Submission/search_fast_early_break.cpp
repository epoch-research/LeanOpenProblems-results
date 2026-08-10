#include <iostream>
#include <vector>
#include <cmath>
#include <omp.h>

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
    int bases[] = {2, 3, 5, 7, 11, 13, 17};
    for (int a : bases) {
        if (n == a) return true;
        if (!miller_rabin(n, a)) return false;
    }
    return true;
}

int main() {
    int max_n = 2000000;
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

    cout << "Sieve completed. Starting optimized search..." << endl;

    bool found = false;

    #pragma omp parallel for shared(found) schedule(dynamic, 1000)
    for (int n = 2; n <= max_n; ++n) {
        if (found) continue;

        int pin = pi[n];
        int target = (pin + 4) / 5;

        int an = 0;
        unsigned long long n2 = (unsigned long long)n * n;
        int start_s = (n % 2 == 0) ? 1 : 2;
        for (int s = start_s; s < n; s += 2) {
            if (is_prime(n2 + (unsigned long long)s * s)) {
                an++;
                if (an >= target) break;
            }
        }

        if (an < target) {
            // Re-verify fully
            int full_an = 0;
            for (int s = 1; s < n; ++s) {
                if (is_prime(n2 + (unsigned long long)s * s)) {
                    full_an++;
                }
            }
            if (5 * full_an < pin) {
                #pragma omp critical
                {
                    if (!found) {
                        cout << "COUNTEREXAMPLE FOUND! n = " << n 
                             << ", a(n) = " << full_an << ", pi(n) = " << pin << endl;
                        found = true;
                    }
                }
            }
        }
    }

    if (!found) {
        cout << "No counterexample found up to " << max_n << "!" << endl;
    }
    return 0;
}
