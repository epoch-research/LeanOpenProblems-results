#include <iostream>
#include <vector>
#include <numeric>
#include <cmath>

using namespace std;

const int LIMIT = 200000000; // 2 * 10^8

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

int main() {
    cout << "Allocating memory..." << endl;
    vector<unsigned int> sig(LIMIT, 1);
    cout << "Computing sieve..." << endl;
    for (int i = 2; i < LIMIT; ++i) {
        for (int j = i; j < LIMIT; j += i) {
            sig[j] += i;
        }
    }
    cout << "Sieve done. Checking Case 1 for 630 and 756..." << endl;
    
    // 630: n-1 = 629. Divisors: 1, 17, 37, 629
    // 756: n-1 = 755. Divisors: 1, 5, 151, 755
    for (int g = 1; g < LIMIT; ++g) {
        long long s = sig[g];
        long long gc = gcd_calc(s, g);
        long long val = (s - g) / gc;
        long long b = g / gc;
        long long a = s / gc;
        
        // Check 630
        if (val > 0 && 629 % val == 0) {
            long long k = 629 / val;
            long long p = k * b - 1;
            if (p > 1 && g % p != 0 && gcd_calc(k * a, p) == 1 && is_prime(p)) {
                cout << "Found for 630: g = " << g << ", p = " << p << ", i = " << (long long)g * p << endl;
            }
        }
        
        // Check 756
        if (val > 0 && 755 % val == 0) {
            long long k = 755 / val;
            long long p = k * b - 1;
            if (p > 1 && g % p != 0 && gcd_calc(k * a, p) == 1 && is_prime(p)) {
                cout << "Found for 756: g = " << g << ", p = " << p << ", i = " << (long long)g * p << endl;
            }
        }
    }
    cout << "Done searching." << endl;
    return 0;
}
