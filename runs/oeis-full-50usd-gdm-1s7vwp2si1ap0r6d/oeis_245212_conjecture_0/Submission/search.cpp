#include <iostream>
#include <vector>
#include <cmath>
#include <numeric>

using namespace std;

// We want to find odd m >= 3 and k >= 1 such that
// (2^(k+1) - 1) divides C' * (k + 1)
// and D * (2^(k+1) - 1) == C' * (k * 2^(k+1) + 1)
// where C' = C_m - m * tau(m)
// and D = m * tau(m) - S_m

int main() {
    int MAX = 100000000;
    cout << "Allocating memory for MAX=" << MAX << "..." << endl;
    vector<int> tau(MAX, 0);
    vector<long long> sigma(MAX, 0);
    vector<long long> C(MAX, 0);

    cout << "Sieving..." << endl;
    for (int i = 1; i < MAX; ++i) {
        for (int j = i; j < MAX; j += i) {
            tau[j]++;
            sigma[j] += i;
        }
    }

    for (int i = 1; i < MAX; ++i) {
        long long t_i = tau[i];
        for (int j = i; j < MAX; j += i) {
            C[j] += (long long)i * t_i;
        }
    }

    cout << "Searching for counterexamples..." << endl;
    for (int m = 3; m < MAX; m += 2) {
        long long Sm = sigma[m];
        long long tm = tau[m];
        long long Cm = C[m];
        long long C_prime = Cm - (long long)m * tm;
        long long D = (long long)m * tm - Sm;

        if (C_prime <= 0 || D <= 0) continue;

        // check if D * (2^(k+1) - 1) == C_prime * (k * 2^(k+1) + 1)
        // Since 2^(k+1) - 1 <= C_prime * (k + 1), and C_prime < m * tm < 10^8 * 100,
        // k is at most 30.
        for (int k = 0; k <= 30; ++k) {
            long long two_pow = 1LL << (k + 1);
            long long lhs = D * (two_pow - 1);
            long long rhs = C_prime * (k * two_pow + 1);
            if (lhs == rhs) {
                cout << "FOUND COUNTEREXAMPLE! m=" << m << ", k=" << k << endl;
                cout << "C_prime=" << C_prime << ", D=" << D << endl;
            }
        }
    }
    cout << "Search complete up to " << MAX << endl;
    return 0;
}
