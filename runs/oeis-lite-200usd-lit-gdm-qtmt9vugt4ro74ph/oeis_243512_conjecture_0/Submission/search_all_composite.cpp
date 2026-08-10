#include <iostream>
#include <vector>
#include <numeric>
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

bool miller_rabin(u128 n, int k=5) {
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

int main() {
    vector<int> missing = {
        630, 756, 1398, 1404, 1566, 1578, 1680, 1740, 1770, 2046, 
        2190, 2226, 2316, 2484, 2646, 2718, 3066, 3150, 3156, 3276, 
        3354, 3366, 3378, 3420, 3432, 3438, 3444, 3504, 3564, 3570, 
        3630, 3640, 3666, 3744, 3960, 4116, 4164, 4170, 4224, 4266, 
        4368, 4470, 4488, 4500, 4536, 4554, 4578, 4830, 4940, 4998
    };
    
    // Generate primes up to 10000
    vector<int> primes;
    vector<bool> is_p(10000, true);
    for (int p=2; p<10000; p++) {
        if (is_p[p]) {
            primes.push_back(p);
            for (int i=2*p; i<10000; i+=p) is_p[i] = false;
        }
    }
    
    cout << "Loaded " << primes.size() << " primes." << endl;
    
    vector<int> found(5001, 0);
    int found_count = 0;
    
    // Try 2-prime search first
    for (size_t i=0; i<primes.size(); i++) {
        long long q1 = primes[i];
        for (size_t j=i+1; j<primes.size(); j++) {
            long long q2 = primes[j];
            
            for (int a=1; a<=10; a++) {
                long long g1 = 1; long long sig1 = 1;
                bool ovf1 = false;
                for (int x=0; x<a; x++) {
                    if (g1 > 1e16 / q1) { ovf1 = true; break; }
                    g1 *= q1; sig1 += g1;
                }
                if (ovf1) break;
                
                for (int b=1; b<=10; b++) {
                    long long g2 = 1; long long sig2 = 1;
                    bool ovf2 = false;
                    for (int y=0; y<b; y++) {
                        if (g2 > 1e16 / q2) { ovf2 = true; break; }
                        g2 *= q2; sig2 += g2;
                    }
                    if (ovf2) break;
                    
                    if (g1 > 1e16 / g2) continue;
                    long long g = g1 * g2;
                    long long sig = sig1 * sig2;
                    
                    long long gc = gcd_calc(sig, g);
                    long long val = (sig - g) / gc;
                    if (val > 0) {
                        for (int n : missing) {
                            if (found[n] == 0 && (n - 1) % val == 0) {
                                long long b_val = g / gc;
                                long long k = (n - 1) / val;
                                u128 p = (u128)k * b_val - 1;
                                if (p > 1 && g % p != 0 && gcd_calc(sig, p) == 1 && miller_rabin(p)) {
                                    found[n] = 1;
                                    found_count++;
                                    cout << "FOUND for " << n << " (2-prime): g = " << g << ", p = " << (long long)p << ", i = " << (long long)g * (long long)p << endl;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    
    cout << "Finished 2-prime search. Found: " << found_count << "/" << missing.size() << endl;
    
    if (found_count < missing.size()) {
        cout << "Remaining missing: ";
        for (int n : missing) {
            if (found[n] == 0) cout << n << " ";
        }
        cout << endl;
    }
    
    return 0;
}
