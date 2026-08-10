#include <iostream>
#include <vector>
#include <numeric>
#include <cmath>

using namespace std;

const int LIMIT = 300000000; // 300 million

long long gcd_calc(long long a, long long b) {
    return b == 0 ? a : gcd_calc(b, a % b);
}

int main() {
    cout << "Allocating memory (1.2 GB)..." << endl;
    vector<unsigned int> sig(LIMIT, 1);
    cout << "Computing sieve..." << endl;
    for (int i = 2; i < LIMIT; ++i) {
        for (int j = i; j < LIMIT; j += i) {
            sig[j] += i;
        }
    }
    cout << "Sieve done. Checking..." << endl;
    vector<int> first_i(5001, 0);
    int missing_count = 5001; // including 0
    for (int i = 1; i < LIMIT; ++i) {
        long long s = sig[i];
        long long g = gcd_calc(s, i);
        long long val = (s - i) / g;
        if (val <= 5000) {
            if (first_i[val] == 0) {
                first_i[val] = i;
                missing_count--;
            }
        }
    }
    cout << "Missing count for n <= 5000: " << missing_count << endl;
    for (int n = 0; n <= 5000; ++n) {
        if (first_i[n] == 0) {
            cout << "Missing: n = " << n << endl;
        }
    }
    return 0;
}
