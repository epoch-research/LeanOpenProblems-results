#include <iostream>
#include <vector>

using namespace std;

int main() {
    long long max_val = 1000000000LL;
    vector<bool> is_p(max_val, true);
    is_p[0] = is_p[1] = false;
    for (long long i = 2; i * i < max_val; ++i) {
        if (is_p[i]) {
            for (long long j = i * i; j < max_val; j += i) {
                is_p[j] = false;
            }
        }
    }
    cout << "Primes generated." << endl;

    long long max_n = 500000000LL;
    vector<int> primes;
    for (int i = 2; i < max_n; ++i) {
        if (is_p[i]) primes.push_back(i);
    }
    cout << "Primes vector populated with " << primes.size() << " primes." << endl;

    // Now check each n
    for (int n = 30; n < max_n; n += 6) {
        int cnt = 0;
        for (int q : primes) {
            if (q >= n) break;
            if (is_p[n - q] && is_p[n + q]) {
                cnt++;
                if (cnt > 4) break; // Early exit!
            }
        }
        if (cnt == 4) {
            cout << "FOUND: a(" << n << ") == 4" << endl;
            return 0;
        }
    }
    cout << "No counterexample found up to " << max_n << endl;
    return 0;
}
