#include <iostream>
using namespace std;

int S(__int128 m) {
    int s = 0;
    while (m > 0) {
        s += m % 10;
        m /= 10;
    }
    return s;
}

// We want to find n with S(n) = 10.
// We can just try random n with S(n) = 10 and length up to 35.

#include <vector>
#include <cstdlib>

int main() {
    srand(12345);
    for (int iter = 0; iter < 10000000; iter++) {
        __int128 n = 0;
        int rem = 10;
        int length = rand() % 35 + 1;
        __int128 p10 = 1;
        for (int i = 0; i < length; i++) {
            if (rem == 0) break;
            int d = rand() % (rem + 1);
            if (i == length - 1) d = rem;
            n += d * p10;
            rem -= d;
            p10 *= 10;
        }
        if (rem > 0) continue;
        
        int max_k = 0;
        for (int k = 11; k <= 100; k++) {
            if (S(k * n) == k) {
                max_k = k;
                break;
            }
        }
        if (max_k == 0) {
            for (int k = 101; k <= 300; k++) {
                if (S(k * n) == k) {
                    max_k = k;
                    break;
                }
            }
            if (max_k == 0) {
                cout << "FOUND! n=" << (long long)(n % 1000000000000000000LL) << "\n";
                return 0;
            }
        }
    }
    cout << "None found in 10M iterations.\n";
    return 0;
}
