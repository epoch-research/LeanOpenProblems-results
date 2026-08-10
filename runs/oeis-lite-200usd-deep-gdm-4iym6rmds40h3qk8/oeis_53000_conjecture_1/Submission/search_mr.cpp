#include <iostream>
#include <vector>
#include <cmath>

using namespace std;

typedef unsigned long long ull;

// Fast modular multiplication (a * b) % mod
ull mul_mod(ull a, ull b, ull m) {
    __int128 r = (__int128)a * b;
    return r % m;
}

// Fast modular exponentiation (base^exp) % mod
ull power(ull base, ull exp, ull mod) {
    ull res = 1;
    base %= mod;
    while (exp > 0) {
        if (exp % 2 == 1) res = mul_mod(res, base, mod);
        base = mul_mod(base, base, mod);
        exp /= 2;
    }
    return res;
}

// Miller-Rabin Primality Test
bool is_prime_mr(ull n) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0 || n % 3 == 0) return false;
    
    ull d = n - 1;
    int s = 0;
    while (d % 2 == 0) {
        d /= 2;
        s++;
    }
    
    // Witness bases for n < 2^64
    static const ull bases[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (ull a : bases) {
        if (n <= a) break;
        ull x = power(a, d, n);
        if (x == 1 || x == n - 1) continue;
        bool composite = true;
        for (int r = 1; r < s; r++) {
            x = mul_mod(x, x, n);
            if (x == n - 1) {
                composite = false;
                break;
            }
        }
        if (composite) return false;
    }
    return true;
}

const int MAX_N = 10000000;

int main() {
    cout << "Allocating memory..." << endl;
    vector<int> phi(MAX_N + 1);
    for (int i = 0; i <= MAX_N; ++i) phi[i] = i;
    for (int i = 2; i <= MAX_N; ++i) {
        if (phi[i] == i) {
            for (int j = i; j <= MAX_N; j += i) {
                phi[j] -= phi[j] / i;
            }
        }
    }
    cout << "Phi table computed." << endl;

    cout << "Searching..." << endl;
    for (int n = 1; n <= MAX_N; ++n) {
        ull n2 = (ull)n * n;
        ull p = n2 + 1;
        while (!is_prime_mr(p)) {
            p++;
        }
        ull an = p - n2;
        ull limit = 1 + phi[n];
        if (an > limit) {
            cout << "COUNTEREXAMPLE FOUND: n=" << n << ", an=" << an << ", phi=" << phi[n] << endl;
            return 0;
        }
        if (n % 1000000 == 0) {
            cout << "Checked up to n=" << n << endl;
        }
    }
    cout << "Finished search up to " << MAX_N << ", no counterexamples found." << endl;
    return 0;
}
