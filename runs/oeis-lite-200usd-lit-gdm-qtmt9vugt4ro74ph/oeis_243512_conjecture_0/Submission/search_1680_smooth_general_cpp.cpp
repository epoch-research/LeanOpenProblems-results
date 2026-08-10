#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <string>

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

u128 gcd128(u128 a, u128 b) {
    return b == 0 ? a : gcd128(b, a % b);
}

long long gcd_calc(long long a, long long b) {
    return b == 0 ? a : gcd_calc(b, a % b);
}

void print128(u128 n) {
    if (n == 0) {
        cout << 0;
        return;
    }
    string s = "";
    while (n > 0) {
        s += (char)('0' + (n % 10));
        n /= 10;
    }
    reverse(s.begin(), s.end());
    cout << s;
}

const long long primes[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97};
const int NUM_PRIMES = 25;
const long long LIMIT = 100000000000000LL; // 10^14

long long count_smooth = 0;

void test_g(long long g, long long s) {
    count_smooth++;
    if (count_smooth % 100000000 == 0) {
        cout << "Processed " << count_smooth << " smooth numbers..." << endl;
    }
    long long s_prime = s - g;
    if (s_prime <= 0) return;
    long long gc = gcd_calc(s_prime, g);
    long long val = s_prime / gc;
    if (val > 1679) return;
    
    long long b_init = g / gc;
    for (long long b = 1; b < 1680; ++b) {
        if (b_init % b == 0) {
            if ((1680 - b) % val == 0) {
                long long m = (1680 - b) / val;
                long long k = b_init / b;
                u128 p = (u128)m * k - 1;
                if (p > 1 && g % p != 0 && miller_rabin(p)) {
                    u128 sig_gp = (u128)s * (p + 1);
                    u128 i_val = (u128)g * p;
                    u128 gc_gp = gcd128(sig_gp, i_val);
                    if ((sig_gp - i_val) / gc_gp == 1680) {
                        cout << "FOUND PREIMAGE!!! g = " << g << ", p = ";
                        print128(p);
                        cout << ", i = ";
                        print128(i_val);
                        cout << ", b = " << b << ", val = " << val << endl;
                        exit(0);
                    }
                }
            }
        }
    }
}

void dfs(int idx, long long current_g, long long current_s) {
    test_g(current_g, current_s);
    
    for (int i = idx; i < NUM_PRIMES; ++i) {
        long long p = primes[i];
        if (current_g > LIMIT / p) continue;
        
        long long next_g = current_g * p;
        long long temp = current_g;
        long long pe = 1;
        while (temp % p == 0) {
            pe *= p;
            temp /= p;
        }
        long long next_s = current_s * (pe * p * p - 1) / (pe * p - 1);
        
        dfs(i, next_g, next_s);
    }
}

int main() {
    cout << "Starting C++ general smooth backtracking search up to " << LIMIT << "..." << endl;
    dfs(0, 1, 1);
    cout << "Finished search up to " << LIMIT << ". Found nothing." << endl;
    return 0;
}
