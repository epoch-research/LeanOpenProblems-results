#include <iostream>
#include <vector>
#include <numeric>
#include <cmath>
#include <algorithm>

using namespace std;

long long gcd_calc(long long a, long long b) {
    return b == 0 ? a : gcd_calc(b, a % b);
}

bool is_prime(long long n) {
    if (n <= 1) return false;
    if (n <= 3) return true;
    if (n % 2 == 0 || n % 3 == 0) return false;
    for (long long i = 5; i * i <= n; i += 6) {
        if (n % i == 0 || n % (i + 2) == 0) return false;
    }
    return true;
}

const int LIMIT = 20000000; // 20 million
vector<long long> sig;

int main() {
    cout << "Allocating memory for sieve (1.6 GB)..." << endl;
    sig.assign(LIMIT, 1);
    cout << "Computing sieve..." << endl;
    for (int i = 2; i < LIMIT; ++i) {
        for (int j = i; j < LIMIT; j += i) {
            sig[j] += i;
        }
    }
    cout << "Sieve done. Searching general preimages for 1680..." << endl;
    
    for (int g = 1; g < LIMIT; ++g) {
        long long s_prime = sig[g] - g;
        if (s_prime <= 0) continue;
        long long gc = gcd_calc(s_prime, g);
        long long val = s_prime / gc;
        long long b_init = g / gc;
        
        // We want val to divide 1680 - b, where b is a divisor of b_init.
        // So (1680 - b) % val == 0.
        // Let us find divisors of b_init.
        for (long long d = 1; d * d <= b_init; ++d) {
            if (b_init % d == 0) {
                long long divisors[2] = {d, b_init / d};
                for (int i = 0; i < 2; ++i) {
                    long long b = divisors[i];
                    if (1680 - b > 0 && (1680 - b) % val == 0) {
                        long long m = (1680 - b) / val;
                        // p = m * k - 1, where k = b_init / b
                        long long k = b_init / b;
                        long long p = m * k - 1;
                        if (p > 1 && g % p != 0 && is_prime(p)) {
                            // double check with actual A243473_val
                            unsigned __int128 temp_i = (unsigned __int128)g * p;
                            if (temp_i < LIMIT) {
                                // Already covered by sieve, but let us check
                            }
                            // Let us calculate divisor_sigma of g * p
                            // Since gcd(g, p) = 1 (we checked g % p != 0 and p is prime),
                            // sig(g * p) = sig(g) * (p + 1)
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
