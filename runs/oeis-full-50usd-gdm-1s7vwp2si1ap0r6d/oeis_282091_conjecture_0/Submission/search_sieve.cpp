#include <iostream>
#include <vector>
#include <cmath>

using namespace std;

bool is_perfect_cube(long long m) {
    if (m < 0) {
        long long k = (long long)round(pow(-m, 1.0/3.0));
        return -k*k*k == m;
    } else {
        long long k = (long long)round(pow(m, 1.0/3.0));
        return k*k*k == m;
    }
}

int main() {
    const int N = 1000000;
    cout << "Allocating sieve for N = " << N << "..." << endl;
    vector<bool> achievable_p1(N + 1, false);
    vector<bool> achievable_p2(N + 1, false);

    // Precompute squares
    vector<int> sq;
    for (int i = 0; i * i <= N; ++i) {
        sq.push_back(i * i);
    }
    int max_val = sq.size() - 1;

    cout << "Sieving Part 1..." << endl;
    for (int x = 0; x <= max_val; ++x) {
        int x2 = sq[x];
        for (int y = 0; y <= x; ++y) {
            int x2_y2 = x2 + sq[y];
            if (x2_y2 > N) break;
            if (x % 2 != y % 2) continue;
            for (int z = y; z <= max_val; ++z) {
                int sum_xyz = x2_y2 + sq[z];
                if (sum_xyz > N) break;
                if (is_perfect_cube(x + y - z)) {
                    for (int w = 0; w < sq.size() && sum_xyz + sq[w] <= N; ++w) {
                        achievable_p1[sum_xyz + sq[w]] = true;
                    }
                }
            }
        }
    }

    cout << "Sieving Part 2..." << endl;
    for (int x = 0; x <= max_val; ++x) {
        int x2 = sq[x];
        for (int y = x; y <= max_val; ++y) {
            int x2_y2 = x2 + sq[y];
            if (x2_y2 > N) break;
            for (int z = y; z <= max_val; ++z) {
                int sum_xyz = x2_y2 + sq[z];
                if (sum_xyz > N) break;
                if (is_perfect_cube(x + y - z)) {
                    for (int w = 0; w < sq.size() && sum_xyz + sq[w] <= N; ++w) {
                        achievable_p2[sum_xyz + sq[w]] = true;
                    }
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
