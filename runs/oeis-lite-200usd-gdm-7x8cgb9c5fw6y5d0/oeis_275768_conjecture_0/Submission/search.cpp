#include <iostream>
#include <vector>

using namespace std;

int main() {
    int max_val = 150000000;
    vector<bool> is_p(max_val, true);
    is_p[0] = is_p[1] = false;
    for (int i = 2; i * i < max_val; ++i) {
        if (is_p[i]) {
            for (int j = i * i; j < max_val; j += i) {
                is_p[j] = false;
            }
        }
    }
    cout << "Primes generated." << endl;

    int max_n = 50000000;
    vector<int> counts(max_n, 0);
    vector<int> primes;
    for (int i = 2; i < max_val; ++i) {
        if (is_p[i]) primes.push_back(i);
    }

    for (int q : primes) {
        if (q >= max_n / 2) break;
        for (int p1 : primes) {
            if (p1 >= max_n - q) break;
            if (is_p[p1 + 2 * q]) {
                counts[q + p1]++;
            }
        }
    }

    for (int n = 30; n < max_n; n += 6) {
        if (counts[n] == 4) {
            cout << "FOUND: a(" << n << ") == 4" << endl;
            return 0;
        }
    }
    cout << "No counterexample found up to " << max_n << endl;
    return 0;
}
