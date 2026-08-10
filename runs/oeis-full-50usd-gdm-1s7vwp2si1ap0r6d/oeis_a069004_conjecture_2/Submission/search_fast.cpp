#include <iostream>
#include <vector>
#include <cmath>
#include <omp.h>

using namespace std;

const int MAX_PRIME = 1000000;
vector<bool> is_prime(MAX_PRIME, true);
vector<int> primes;

void sieve() {
    is_prime[0] = is_prime[1] = false;
    for (int i = 2; i * i < MAX_PRIME; ++i) {
        if (is_prime[i]) {
            for (int j = i * i; j < MAX_PRIME; j += i) {
                is_prime[j] = false;
            }
        }
    }
    for (int i = 2; i < MAX_PRIME; ++i) {
        if (is_prime[i]) {
            primes.push_back(i);
        }
    }
}

bool check_prime(long long x) {
    if (x < MAX_PRIME) return is_prime[x];
    for (int p : primes) {
        if ((long long)p * p > x) return true;
        if (x % p == 0) return false;
    }
    return true;
}

int main() {
    sieve();
    cout << "Sieve completed. Number of primes up to 1M: " << primes.size() << endl;

    int max_n = 200000;
    vector<int> pi(max_n + 1, 0);
    int cnt = 0;
    for (int i = 1; i <= max_n; ++i) {
        if (i < MAX_PRIME && is_prime[i]) cnt++;
        pi[i] = cnt;
    }

    #pragma omp parallel for schedule(dynamic, 100)
    for (int n = 2; n <= max_n; ++n) {
        int an = 0;
        long long n2 = (long long)n * n;
        for (int s = 1; s < n; ++s) {
            if (check_prime(n2 + (long long)s * s)) {
                an++;
            }
        }
        int pin = pi[n];

        if (pin < an) {
            #pragma omp critical
            {
                cout << "COUNTEREXAMPLE 1 (pi(n) < a(n)): n = " << n 
                     << ", a(n) = " << an << ", pi(n) = " << pin << endl;
            }
        }
        if (5 * an < pin) {
            #pragma omp critical
            {
                cout << "COUNTEREXAMPLE 2 (5 * a(n) < pi(n)): n = " << n 
                     << ", a(n) = " << an << ", pi(n) = " << pin << endl;
            }
        }
    }
    cout << "Search completed up to " << max_n << "!" << endl;
    return 0;
}
