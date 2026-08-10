#include <iostream>
#include <vector>
#include <algorithm>

using namespace std;

inline int sd(long long n) {
    int sum = 0;
    while (n > 0) {
        sum += n % 10;
        n /= 10;
    }
    return sum;
}

int main() {
    long long limit = 1000000000; // 1 billion
    for (long long n = 10; n < limit; n += 9) {
        int s_n = sd(n);
        if (s_n >= 10) {
            int max_val = 0;
            // Since n < 10^9, any valid multiplier M is at most 110
            for (int M = 1; M <= 120; ++M) {
                if (sd(M * n) == M) {
                    max_val = M;
                }
            }
            if (max_val == 1 || max_val == 2 || max_val == 3 || max_val == 4 || max_val == 5 || 
                max_val == 6 || max_val == 7 || max_val == 8 || max_val == 10 || max_val == 11) {
                cout << "COUNTEREXAMPLE FOUND: n=" << n << ", max_val=" << max_val << endl;
                return 0;
            }
        }
    }
    cout << "No counterexample found up to " << limit << endl;
    return 0;
}
