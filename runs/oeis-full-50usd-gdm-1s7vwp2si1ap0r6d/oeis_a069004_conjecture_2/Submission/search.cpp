#include <iostream>
#include <vector>
#include <cmath>
#include <omp.h>

using namespace std;

const int MAX_PRIME_SAFE = 1500000;
vector<bool> is_prime_safe(MAX_PRIME_SAFE, true);
vector<int> primes_safe;

void sieve_safe() {
    is_prime_safe[0] = is_prime_safe[1] = false;
    for (int i = 2; i * i < MAX_PRIME_SAFE; ++i) {
        if (is_prime_safe[i]) {
            for (int j = i * i; j < MAX_PRIME_SAFE; j += i) {
                is_prime_safe[j] = false;
            }
        }
    }
    for (int i = 2; i < MAX_PRIME_SAFE; ++i) {
        if (is_prime_safe[i]) {
            primes_safe.push_back(i);
        }
    }
}

bool check_prime(long long x) {
    if (x < MAX_PRIME_SAFE) return is_prime_safe[x];
    for (int p : primes_safe) {
        if ((long long)p * p > x) return true;
        if (x % p == 0) return false;
    }
    return true;
}

int main() {
    sieve_safe();
    cout << "Sieve completed." << endl;

    vector<int> pi(150000, 0);
    int cnt = 0;
    for (int i = 1; i < 150000; ++i) {
        if (is_prime_safe[i]) cnt++;
        pi[i] = cnt;
    }

    bool found = false;

    #pragma omp parallel for shared(found) schedule(dynamic, 100)
    for (int n = 2; n < 100000; ++n) {
        if (found) continue;

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
                if (!found) {
                    cout << "Counterexample to cond1 found: n = " << n 
                         << ", a(n) = " << an << ", pi(n) = " << pin << endl;
                    found = true;
                }
            }
        }
    }
    cout << "Search completed!" << endl;
    return 0;
}
