#include <iostream>
#include <vector>
#include <cmath>

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

int main() {
    long long LIMIT = 2000000000LL; // 2 billion
    cout << "Allocating sieve of size " << LIMIT << "..." << endl;
    vector<bool> is_prime(LIMIT, true);
    is_prime[0] = is_prime[1] = false;
    for (long long p = 2; p * p < LIMIT; p++) {
        if (is_prime[p]) {
            for (long long i = p * p; i < LIMIT; i += p) {
                is_prime[i] = false;
            }
        }
    }
    cout << "Sieve done. Searching for prime g such that 1679*g - 1 is prime..." << endl;
    for (long long g = 2; g < LIMIT; g++) {
        if (is_prime[g]) {
            long long p = 1679LL * g - 1;
            if (miller_rabin(p)) {
                cout << "FOUND! g = " << g << ", p = " << p << ", i = " << g * p << endl;
                return 0;
            }
        }
    }
    cout << "Finished checking up to " << LIMIT << endl;
    return 0;
}
