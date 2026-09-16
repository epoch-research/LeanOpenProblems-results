#include <iostream>
using namespace std;

int S(long long m) {
    int s = 0;
    while (m > 0) {
        s += m % 10;
        m /= 10;
    }
    return s;
}

int main() {
    for (long long n = 1; n <= 100000000; n++) {
        int max_k = 0;
        for (int k = 1; k <= 100; k++) {
            if (S(k * n) == k) max_k = k;
        }
        if (max_k > 0 && max_k < 12 && max_k != 9) {
            // Verify up to 1000
            bool ok = true;
            for (int k = 101; k <= 1000; k++) {
                if (S(k * n) == k) { ok = false; break; }
            }
            if (ok) {
                cout << "FOUND! n=" << n << " max_k=" << max_k << "\n";
                return 0;
            }
        }
    }
    cout << "None up to 10^8\n";
    return 0;
}
