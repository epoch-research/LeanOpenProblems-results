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

const long long LIMIT = 2000000000LL; // 2 billion
const int BLOCK_SIZE = 10000000; // 10 million

int main() {
    cout << "Starting block search up to " << LIMIT << " using block size " << BLOCK_SIZE << "..." << endl;
    vector<uint64_t> sig(BLOCK_SIZE);
    
    for (long long start = 1; start < LIMIT; start += BLOCK_SIZE) {
        long long end = min(start + BLOCK_SIZE, LIMIT);
        long long sieve_limit = (end - 1) / 2;
        
        fill(sig.begin(), sig.begin() + (end - start), 1);
        
        for (long long d = 2; d <= sieve_limit; ++d) {
            long long first = ((start + d - 1) / d) * d;
            if (first < start) first += d;
            for (long long j = first; j < end; j += d) {
                sig[j - start] += d;
            }
        }
        
        for (long long g = start; g < end; ++g) {
            long long s = sig[g - start];
            if (g > sieve_limit) {
                s += g;
            }
            
            long long s_prime = s - g;
            if (s_prime <= 0) continue;
            long long gc = gcd_calc(s_prime, g);
            long long val = s_prime / gc;
            if (val > 1679) continue;
            
            long long b_init = g / gc;
            for (long long b = 1; b < 1680; ++b) {
                if (b_init % b == 0) {
                    if ((1680 - b) % val == 0) {
                        long long m = (1680 - b) / val;
                        long long k = b_init / b;
                        long long p = m * k - 1;
                        if (p > 1 && g % p != 0 && miller_rabin(p)) {
                            long long sig_gp = s * (p + 1);
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
        
        if (start % (BLOCK_SIZE * 5) == 1) {
            cout << "Processed up to " << start << endl;
        }
    }
    
    cout << "Finished search up to " << LIMIT << ". No preimage found." << endl;
    return 0;
}
