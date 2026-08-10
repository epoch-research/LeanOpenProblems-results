#include <iostream>
#include <vector>
#include <numeric>
#include <cmath>
#include <algorithm>
#include <omp.h>

using namespace std;

typedef unsigned __int128 u128;

u128 power(u128 base, u128 exp, u128 mod) {
    u128 res = 1;
    base %= mod;
    while (exp > 0) {
        if (exp % 2 == 1) res = (res * base) % mod;
        base = (base * base) % mod;
        exp /= 2;
    }
    return res;
}

bool miller_rabin(u128 n) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0) return false;
    u128 d = n - 1;
    int s = 0;
    while (d % 2 == 0) {
        d /= 2;
        s++;
    }
    static const u128 bases[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47};
    for (u128 a : bases) {
        if (n <= a) break;
        u128 x = power(a, d, n);
        if (x == 1 || x == n - 1) continue;
        bool composite = true;
        for (int r = 1; r < s; r++) {
            x = (x * x) % n;
            if (x == n - 1) {
                composite = false;
                break;
            }
        }
        if (composite) return false;
    }
    return true;
}

long long gcd_calc(long long a, long long b) {
    return b == 0 ? a : gcd_calc(b, a % b);
}

int main() {
    // Generate primes up to 2000
    vector<int> primes;
    vector<bool> is_p(2000, true);
    for (int p = 2; p < 2000; p++) {
        if (is_p[p]) {
            primes.push_back(p);
            for (int i = 2 * p; i < 2000; i += p) is_p[i] = false;
        }
    }
    
    int n_primes = primes.size();
    cout << "Loaded " << n_primes << " primes." << endl;
    
    cout << "Starting 4-prime distinct search..." << endl;
    
    #pragma omp parallel for schedule(dynamic)
    for (int i = 0; i < n_primes; i++) {
        long long q1 = primes[i];
        for (int j = i + 1; j < n_primes; j++) {
            long long q2 = primes[j];
            for (int k_idx = j + 1; k_idx < n_primes; k_idx++) {
                long long q3 = primes[k_idx];
                for (int l = k_idx + 1; l < n_primes; l++) {
                    long long q4 = primes[l];
                    
                    // Check overflow
                    if (q1 > 2000000000000000LL / q2) continue;
                    long long g12 = q1 * q2;
                    if (g12 > 2000000000000000LL / q3) continue;
                    long long g123 = g12 * q3;
                    if (g123 > 2000000000000000LL / q4) continue;
                    long long g = g123 * q4;
                    
                    long long sig = (q1 + 1) * (q2 + 1) * (q3 + 1) * (q4 + 1);
                    long long s_prime = sig - g;
                    if (s_prime <= 0) continue;
                    
                    long long gc = gcd_calc(sig, g);
                    long long val = s_prime / gc;
                    if (1679 % val == 0) {
                        long long b_val = g / gc;
                        long long k = 1679 / val;
                        u128 p = (u128)k * b_val - 1;
                        if (p > 1 && g % p != 0 && gcd_calc(sig, p) == 1 && miller_rabin(p)) {
                            #pragma omp critical
                            {
                                cout << "FOUND (4 primes, distinct)! q1=" << q1 << ", q2=" << q2 << ", q3=" << q3 << ", q4=" << q4 << endl;
                                cout << "g=" << g << ", p=" << (long long)p << ", i=" << (long long)g * (long long)p << endl;
                                exit(0);
                            }
                        }
                    }
                }
            }
        }
    }
    
    cout << "Finished 4-prime distinct search." << endl;
    return 0;
}
