#include <iostream>
#include <vector>
#include <numeric>
#include <cmath>

using namespace std;

const long long LIMIT = 2000000000LL; // 2 billion

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
    cout << "Allocating memory (8 GB)..." << endl;
    vector<unsigned int> sig(LIMIT, 1);
    cout << "Computing sieve..." << endl;
    for (int i = 2; i < LIMIT; ++i) {
        if (i % 100000000 == 0) {
            cout << "Sieved up to " << i << endl;
        }
        for (int j = i; j < LIMIT; j += i) {
            sig[j] += i;
        }
    }
    cout << "Sieve done. Checking for 1680..." << endl;
    
    for (int g = 1; g < LIMIT; ++g) {
        if (g % 100000000 == 0) {
            cout << "Checked up to " << g << endl;
        }
        long long s = sig[g];
        long long gc = gcd_calc(s, g);
        long long val = (s - g) / gc;
        long long b = g / gc;
        long long a = s / gc;
        
        if (val > 0 && 1679 % val == 0) {
            long long k = 1679 / val;
            long long p = k * b - 1;
            if (p > 1 && g % p != 0 && gcd_calc(s, p) == 1 && is_prime(p)) {
                cout << "SUCCESS! Found for 1680: g = " << g << ", p = " << p << ", i = " << (long long)g * p << endl;
                return 0;
            }
        }
    }
    cout << "No preimage found for 1680 up to " << LIMIT << endl;
    return 0;
}
