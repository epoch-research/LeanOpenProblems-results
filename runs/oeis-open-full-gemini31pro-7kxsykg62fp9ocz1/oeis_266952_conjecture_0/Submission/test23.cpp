#include <iostream>
#include <vector>

using namespace std;

bool is_prime(int n) {
    if (n < 2) return false;
    for (int i = 2; i * i <= n; i++) {
        if (n % i == 0) return false;
    }
    return true;
}

int main() {
    int max_n = 50000;
    for (int n = 0; n < max_n; n++) {
        bool found = false;
        for (int p = 0; p <= 6 * n + 2; p++) {
            if (is_prime(p) && is_prime(p - 2) && is_prime(6 * n - p) && is_prime(6 * n + 2 - p)) {
                found = true;
                break;
            }
        }
        if (!found) {
            cout << n << endl;
        }
    }
    return 0;
}
