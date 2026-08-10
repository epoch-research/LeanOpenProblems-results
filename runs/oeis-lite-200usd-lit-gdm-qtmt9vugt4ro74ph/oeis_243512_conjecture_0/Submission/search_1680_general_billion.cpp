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

const int LIMIT = 1000000000; // 1 billion
vector<uint64_t> sig;

int main() {
    cout << "Allocating memory for sieve (8 GB)..." << endl;
    sig.assign(LIMIT, 1);
    cout << "Computing sieve..." << endl;
    for (int i = 2; i < LIMIT; ++i) {
        if (i % 100000000 == 0) {
            cout << "Sieved up to " << i << "..." << endl;
        }
        for (int j = i; j < LIMIT; j += i) {
            sig[j] += i;
        }
    }
    cout << "Sieve done. Searching general preimages for 1680..." << endl;
    
    for (int g = 1; g < LIMIT; ++g) {
        if (g % 100000000 == 0) {
            cout << "Searched up to " << g << "..." << endl;
        }
        long long s_prime = sig[g] - g;
        if (s_prime <= 0) continue;
        long long gc = gcd_calc(s_prime, g);
        long long val = s_prime / gc;
        long long b_init = g / gc;
        
        for (long long d = 1; d * d <= b_init; ++d) {
            if (b_init % d == 0) {
                long long divisors[2] = {d, b_init / d};
                for (int i = 0; i < 2; ++i) {
                    long long b = divisors[i];
                    if (1680 - b > 0 && (1680 - b) % val == 0) {
                        long long m = (1680 - b) / val;
                        long long k = b_init / b;
                        long long p = m * k - 1;
                        if (p > 1 && g % p != 0 && miller_rabin(p)) {
                            long long sig_gp = sig[g] * (p + 1);
                            long long i_val = g * p;
                            long long gc_gp = gcd_calc(sig_gp, i_val);
                            if ((sig_gp - i_val) / gc_gp == 1680) {
                                cout << "FOUND PREIMAGE!!! g = " << g << ", p = " << p << ", i = " << i_val << ", b = " << b << ", val = " << val << endl;
                                return 0;
                            }
                        }
                    }
                }
            }
        }
    }
    cout << "Finished search up to " << LIMIT << ". No preimage found." << endl;
    return 0;
}
