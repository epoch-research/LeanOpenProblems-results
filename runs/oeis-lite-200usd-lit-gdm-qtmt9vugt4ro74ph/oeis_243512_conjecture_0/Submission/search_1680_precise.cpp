#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>

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
    static const u128 bases[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
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

const int MAX_G = 100000000; // 100 million
vector<long long> sig;

int main() {
    cout << "Sieving sigma up to " << MAX_G << "..." << endl;
    sig.resize(MAX_G, 0);
    for (int i = 1; i < MAX_G; i++) {
        for (int j = i; j < MAX_G; j += i) {
            sig[j] += i;
        }
    }
    cout << "Sieve done. Searching..." << endl;
    for (long long g = 2; g < MAX_G; g++) {
        long long s_g = sig[g] - g;
        if (s_g == 0) continue;
        
        // Find divisors of g
        for (long long d = 1; d * d <= g; d++) {
            if (g % d == 0) {
                // divisor d
                long long m = g / d;
                if (1680 - m > 0) {
                    long long num = (1680 - m) * d;
                    if (num % s_g == 0) {
                        long long p = num / s_g - 1;
                        if (p > 1 && miller_rabin(p)) {
                            if (gcd_calc(g, p) == 1) {
                                long long val_check = sig[g] * (1680 - m) / s_g;
                                if (gcd_calc(val_check, m) == 1) {
                                    cout << "FOUND preimage for 1680! g = " << g << ", p = " << p << ", i = " << g * p << endl;
                                    return 0;
                                }
                            }
                        }
                    }
                }
                
                // divisor m
                long long d2 = m;
                long long m2 = d;
                if (1680 - m2 > 0) {
                    long long num = (1680 - m2) * d2;
                    if (num % s_g == 0) {
                        long long p = num / s_g - 1;
                        if (p > 1 && miller_rabin(p)) {
                            if (gcd_calc(g, p) == 1) {
                                long long val_check = sig[g] * (1680 - m2) / s_g;
                                if (gcd_calc(val_check, m2) == 1) {
                                    cout << "FOUND preimage for 1680! g = " << g << ", p = " << p << ", i = " << g * p << endl;
                                    return 0;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    cout << "Finished up to " << MAX_G << endl;
    return 0;
}
