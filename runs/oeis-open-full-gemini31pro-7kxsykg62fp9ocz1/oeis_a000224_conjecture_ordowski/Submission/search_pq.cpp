#include <iostream>

using namespace std;

bool is_prime(long long n) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0 || n % 3 == 0) return false;
    for (long long i = 5; i * i <= n; i += 6) {
        if (n % i == 0 || n % (i + 2) == 0) return false;
    }
    return true;
}

int main() {
    for (long long p = 3; p <= 1000000; p += 2) {
        if (!is_prime(p)) continue;
        for (long long q = p + 2; q <= 1000000; q += 2) {
            if (!is_prime(q)) continue;
            long long A = (p + 1) * (q + 1) / 4;
            long long M = A * (A - 1);
            long long n = p * q;
            // careful with overflow: n*n - 1 can be up to 10^24, we need int128
            unsigned __int128 n2 = (unsigned __int128)n * n - 1;
            if (n2 % M == 0) {
                cout << "Found: p=" << p << ", q=" << q << ", n=" << n << endl;
            }
        }
    }
    return 0;
}
