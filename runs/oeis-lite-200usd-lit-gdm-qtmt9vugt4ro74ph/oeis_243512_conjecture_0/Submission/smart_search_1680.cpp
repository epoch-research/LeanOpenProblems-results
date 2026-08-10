#include <iostream>
#include <vector>
#include <numeric>
#include <cmath>

using namespace std;

const int LIMIT = 1500000000; // 1.5 * 10^9

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
    cout << "Allocating memory (6 GB)..." << endl;
    vector<unsigned int> sig(LIMIT, 1);
    cout << "Computing sieve..." << endl;
    for (int i = 2; i < LIMIT; ++i) {
        for (int j = i; j < LIMIT; j += i) {
            sig[j] += i;
        }
    }
    cout << "Sieve done. Checking Case 1 for 1680..." << endl;
    
    for (int g = 1; g < LIMIT; ++g) {
        long long s = sig[g];
        long long gc = gcd_calc(s, g);
        long long val = (s - g) / gc;
        long long b = g / gc;
        long long a = s / gc;
        
        if (val > 0 && 1679 % val == 0) {
            long long k = 1679 / val;
            long long p = k * b - 1;
            if (p > 1 && g % p != 0 && gcd_calc(k * a, p) == 1 && is_prime(p)) {
                cout << "Found for 1680: g = " << g << ", p = " << p << ", i = " << (long long)g * p << endl;
                break;
            }
        }
    }
    cout << "Done searching." << endl;
    return 0;
}
