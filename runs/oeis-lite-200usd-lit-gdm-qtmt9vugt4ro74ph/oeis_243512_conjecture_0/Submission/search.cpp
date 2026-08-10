#include <iostream>
#include <vector>
#include <numeric>
#include <cmath>

using namespace std;

const int LIMIT = 500000000; // 5 * 10^8

long long gcd(long long a, long long b) {
    return b == 0 ? a : gcd(b, a % b);
}

int main() {
    cout << "Allocating memory..." << endl;
    vector<long long> sig(LIMIT, 1);
    cout << "Computing sieve..." << endl;
    for (int i = 2; i < LIMIT; ++i) {
        for (int j = i; j < LIMIT; j += i) {
            sig[j] += i;
        }
    }
    cout << "Sieve done. Searching..." << endl;
    for (int i = 1; i < LIMIT; ++i) {
        long long s = sig[i];
        long long g = gcd(s, i);
        long long val = (s - i) / g;
        if (val == 624) {
            cout << "Found 624: i = " << i << endl;
        }
        if (val == 630) {
            cout << "Found 630: i = " << i << endl;
        }
        if (val == 756) {
            cout << "Found 756: i = " << i << endl;
        }
        if (val == 918) {
            cout << "Found 918: i = " << i << endl;
        }
        if (val == 950) {
            cout << "Found 950: i = " << i << endl;
        }
        if (val == 966) {
            cout << "Found 966: i = " << i << endl;
        }
    }
    cout << "Search done." << endl;
    return 0;
}

