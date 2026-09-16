#include <iostream>
#include <vector>

using namespace std;

int main() {
    long long max_n = 500000;
    long long max_p = 6 * max_n + 4;
    vector<bool> is_prime(max_p, true);
    is_prime[0] = is_prime[1] = false;
    for (long long p = 2; p * p < max_p; p++) {
        if (is_prime[p]) {
            for (long long i = p * p; i < max_p; i += p)
                is_prime[i] = false;
        }
    }
    
    int zeros = 0;
    for (long long n = 0; n < max_n; n++) {
        bool found = false;
        for (long long p = 5; p <= 6 * n + 2; p++) {
            long long q1 = 6 * n - p;
            long long q2 = 6 * n + 2 - p;
            if (q1 < 0 || q2 < 0) continue;
            if (is_prime[p] && is_prime[p - 2] && is_prime[q1] && is_prime[q2]) {
                found = true;
                break;
            }
        }
        if (!found) {
            cout << "Zero: " << n << "\n";
            zeros++;
        }
    }
    cout << "Total zeros: " << zeros << "\n";
    return 0;
}
