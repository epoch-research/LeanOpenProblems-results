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

const int MAX_LIMIT = 50000000;
long long sig[MAX_LIMIT];

int main() {
    cout << "Initializing sieve..." << endl;
    for (int i = 1; i < MAX_LIMIT; i++) sig[i] = 0;
    for (int i = 1; i < MAX_LIMIT; i++) {
        for (int j = i; j < MAX_LIMIT; j += i) {
            sig[j] += i;
        }
    }
    cout << "Sieve done. Checking candidates..." << endl;
    for (long long g = 1; g < MAX_LIMIT; g++) {
        long long s = sig[g] - g;
        if (s == 23) {
            long long p = 73 * g - 1;
            if (miller_rabin(p) && gcd_calc(73 * sig[g], p) == 1) {
                cout << "FOUND for 1680: g = " << g << ", p = " << p << ", i = " << g * p << endl;
                return 0;
            }
        } else if (s == 73) {
            long long p = 23 * g - 1;
            if (miller_rabin(p) && gcd_calc(23 * sig[g], p) == 1) {
                cout << "FOUND for 1680: g = " << g << ", p = " << p << ", i = " << g * p << endl;
                return 0;
            }
        } else if (s == 1679) {
            long long p = 1 * g - 1;
            if (miller_rabin(p) && gcd_calc(1 * sig[g], p) == 1) {
                cout << "FOUND for 1680: g = " << g << ", p = " << p << ", i = " << g * p << endl;
                return 0;
            }
        }
    }
    cout << "Finished checking up to " << MAX_LIMIT << endl;
    return 0;
}
