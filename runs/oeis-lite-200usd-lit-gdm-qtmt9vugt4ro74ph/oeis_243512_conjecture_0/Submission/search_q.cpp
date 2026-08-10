#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>

using namespace std;

long long gcd_calc(long long a, long long b) {
    return b == 0 ? a : gcd_calc(b, a % b);
}

const int LIMIT = 200000000; // 200 million

int main() {
    cout << "Allocating memory..." << endl;
    vector<long long> sig(LIMIT, 1);
    cout << "Sieving..." << endl;
    for (int i = 2; i < LIMIT; ++i) {
        for (int j = i; j < LIMIT; j += i) {
            sig[j] += i;
        }
    }
    cout << "Sieve done. Checking s(q) == 1680..." << endl;
    for (int q = 1; q < LIMIT; ++q) {
        if (sig[q] - q == 1680) {
            cout << "FOUND: q = " << q << ", gcd = " << gcd_calc(q, 1680) << endl;
        }
    }
    cout << "Finished." << endl;
    return 0;
}
