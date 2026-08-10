#include <iostream>
#include <vector>

using namespace std;

int main() {
    int limit = 4000000;
    vector<bool> is_prime(limit, true);
    is_prime[0] = is_prime[1] = false;
    for (int i = 2; i * i < limit; ++i) {
        if (is_prime[i]) {
            for (int j = i * i; j < limit; j += i) {
                is_prime[j] = false;
            }
        }
    }

    vector<int> pi(limit, 0);
    int curr = 0;
    for (int i = 0; i < limit; ++i) {
        if (is_prime[i]) {
            curr++;
        }
        pi[i] = curr;
    }

    cout << "Sieve completed." << endl;

    for (int m = 11; m < limit / 2; ++m) {
        int pi_m = pi[m];
        for (int n = m; n < limit - m; ++n) {
            if (pi[m + n] >= pi_m + pi[n]) {
                cout << "FOUND: m=" << m << ", n=" << n 
                     << ", pi(m)=" << pi_m << ", pi(n)=" << pi[n] 
                     << ", pi(m+n)=" << pi[m + n] << endl;
                return 0;
            }
        }
    }

    cout << "No counterexamples found up to " << limit << endl;
    return 0;
}
