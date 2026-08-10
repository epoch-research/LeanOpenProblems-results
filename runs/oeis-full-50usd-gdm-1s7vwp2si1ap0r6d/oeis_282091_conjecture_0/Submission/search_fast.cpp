#include <iostream>
#include <vector>
#include <cmath>

using namespace std;

int main() {
    const int N = 10000000; // 10 Million
    cout << "Allocating sieve for N = " << N << "..." << endl;
    vector<bool> achievable_p1(N + 1, false);
    vector<bool> achievable_p2(N + 1, false);

    // Precompute squares
    vector<long long> sq;
    for (long long i = 0; i * i <= N; ++i) {
        sq.push_back(i * i);
    }

    cout << "Sieving..." << endl;

    // Loop over c for Part 2: x + y - z = c^3 => z = x + y - c^3
    // Since x <= y <= z => x <= y <= x + y - c^3 => c^3 <= x.
    // Also x^2 + y^2 + z^2 <= N => z <= sqrt(N) => x + y - c^3 <= sqrt(N).
    // So c^3 must be at most sqrt(N).
    // Max value of c is around N^(1/6). For N = 20M, N^(1/6) is around 16.
    // Min value of c: c can be negative. But x^2 + y^2 + z^2 <= N => z <= sqrt(N) => x + y - c^3 <= sqrt(N).
    // Since x, y >= 0, -c^3 <= sqrt(N) => c^3 >= -sqrt(N).
    // So c can be negative, down to around -16.
    int limit_c = pow(sqrt(N), 1.0/3.0) + 2;

    for (int c = -limit_c; c <= limit_c; ++c) {
        long long c3 = (long long)c * c * c;
        long long start_x = max(0LL, c3);
        for (long long x = start_x; x * x <= N; ++x) {
            long long x2 = x * x;
            for (long long y = x; ; ++y) {
                long long z = x + y - c3;
                if (z < y) break; // since z = x + y - c3 >= y is checked (it's equivalent to x >= c3, which is true)
                long long sum_xyz = x2 + y * y + z * z;
                if (sum_xyz > N) break;

                // Part 2 achieved
                for (int w = 0; w < sq.size() && sum_xyz + sq[w] <= N; ++w) {
                    achievable_p2[sum_xyz + sq[w]] = true;
                }
            }
        }
    }

    // Loop over c for Part 1: x >= y <= z, x % 2 == y % 2, x + y - z = c^3 => z = x + y - c^3
    // Since y <= z => y <= x + y - c^3 => c^3 <= x.
    // Since y <= x, and x^2 + y^2 + z^2 <= N.
    for (int c = -limit_c; c <= limit_c; ++c) {
        long long c3 = (long long)c * c * c;
        long long start_x = max(0LL, c3);
        for (long long x = start_x; x * x <= N; ++x) {
            long long x2 = x * x;
            for (long long y = 0; y <= x; ++y) {
                if (x % 2 != y % 2) continue;
                long long z = x + y - c3;
                if (z < y) continue; // we need y <= z
                long long sum_xyz = x2 + y * y + z * z;
                if (sum_xyz > N) continue;

                // Part 1 achieved
                for (int w = 0; w < sq.size() && sum_xyz + sq[w] <= N; ++w) {
                    achievable_p1[sum_xyz + sq[w]] = true;
                }
            }
        }
    }

    cout << "Checking results..." << endl;
    for (int n = 0; n <= N; ++n) {
        if (!achievable_p1[n]) {
            cout << "COUNTEREXAMPLE for Part 1 at n = " << n << endl;
            return 0;
        }
        if (!achievable_p2[n]) {
            cout << "COUNTEREXAMPLE for Part 2 at n = " << n << endl;
            return 0;
        }
    }

    cout << "No counterexample found up to " << N << "!" << endl;
    return 0;
}
