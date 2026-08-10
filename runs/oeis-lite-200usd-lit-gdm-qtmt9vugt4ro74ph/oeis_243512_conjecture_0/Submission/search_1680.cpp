#include <iostream>
#include <vector>
#include <numeric>
#include <cmath>

using namespace std;

const int LIMIT = 1500000000; // 1.5 * 10^9

long long gcd_calc(long long a, long long b) {
    return b == 0 ? a : gcd_calc(b, a % b);
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
    cout << "Sieve done. Searching for 1680..." << endl;
    for (int i = 1; i < LIMIT; ++i) {
        long long s = sig[i];
        long long g = gcd_calc(s, i);
        long long val = (s - i) / g;
        if (val == 1680) {
            cout << "FOUND 1680: i = " << i << endl;
            return 0;
        }
    }
    cout << "NOT FOUND 1680." << endl;
    return 0;
}
