#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <chrono>

using namespace std;

// Miller-Rabin primality test for 64-bit integers
unsigned __int128 power(unsigned __int128 base, unsigned __int128 exp, unsigned __int128 mod) {
    unsigned __int128 res = 1;
    base %= mod;
    while (exp > 0) {
        if (exp % 2 == 1) res = (res * base) % mod;
        base = (base * base) % mod;
        exp /= 2;
    }
    return res;
}

bool miller_rabin(long long n, int k=5) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0 || n % 3 == 0) return false;
    
    long long d = n - 1;
    int s = 0;
    while (d % 2 == 0) {
        d /= 2;
        s++;
    }
    
    // Witness bases for 64-bit integers
    static const long long bases[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (long long a : bases) {
        if (n <= a) break;
        unsigned __int128 x = power(a, d, n);
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

const int KNOWN_ZEROS[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 21, 24, 51, 84, 1011, 59586};
bool is_known_zero(long long n) {
    for (int z : KNOWN_ZEROS) {
        if (n == z) return true;
    }
    return false;
}

bool has_representation(long long n) {
    long long N = 2 * n - 1;
    int B = 64 - __builtin_clzll(N); // log2(N) + 1
    
    for (int sum_xy = 2; sum_xy <= 2 * B + 2; ++sum_xy) {
        for (int x = 1; x < sum_xy; ++x) {
            int y = sum_xy - x;
            if (x > B || y > B) continue;
            long long S = (1LL << x) + 11LL * (1LL << y);
            if (S >= N) continue;
            long long p = N - S;
            if (p % 6 == 1 && miller_rabin(p)) {
                return true;
            }
        }
    }
    return false;
}

int main() {
    auto t0 = chrono::high_resolution_clock::now();
    
    // We check from 1 to 10 billion
    long long start = 1;
    long long end = 10000000000LL;
    
    cout << "Checking from " << start << " to " << end << "..." << endl;
    
    // Print progress every 100 million
    for (long long n = start; n <= end; ++n) {
        if (n % 100000000LL == 0) {
            auto t1 = chrono::high_resolution_clock::now();
            cout << "Checked up to " << n << " in " 
                 << chrono::duration_cast<chrono::seconds>(t1 - t0).count() << " seconds." << endl;
        }
        if (!has_representation(n)) {
            if (!is_known_zero(n)) {
                cout << "COUNTEREXAMPLE FOUND: n = " << n << endl;
            }
        }
    }
    
    auto t1 = chrono::high_resolution_clock::now();
    cout << "Total time: " << chrono::duration_cast<chrono::seconds>(t1 - t0).count() << " seconds." << endl;
    return 0;
}
