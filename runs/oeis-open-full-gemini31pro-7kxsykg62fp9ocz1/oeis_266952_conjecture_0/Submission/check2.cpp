#include <iostream>
#include <vector>

using namespace std;

int main() {
    int max_n = 5000000;
    int max_p = 6 * max_n + 4;
    vector<bool> is_prime(max_p, true);
    is_prime[0] = is_prime[1] = false;
    for (int p = 2; p * p < max_p; p++) {
        if (is_prime[p]) {
            for (int i = p * p; i < max_p; i += p)
                is_prime[i] = false;
        }
    }
    
    int zeros = 0;
    for (int n = 0; n < max_n; n++) {
        bool found = false;
        for (int p = 5; p <= 6 * n + 2; p++) {
            if (is_prime[p] && is_prime[p - 2] && is_prime[6 * n - p] && is_prime[6 * n + 2 - p]) {
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
