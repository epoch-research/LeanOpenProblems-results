#include <iostream>
#include <vector>
#include <cmath>
#include <cmath>
#include <algorithm>

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

bool check_part1(long long n) {
    long long limit_x = (long long)sqrt(n);
    for (long long x = 0; x <= limit_x; ++x) {
        long long x2 = x * x;
        for (long long y = 0; y <= x; ++y) {
            long long x2_y2 = x2 + y * y;
            if (x2_y2 > n) break;
            if (x % 2 != y % 2) continue;
            long long limit_z = (long long)sqrt(n - x2_y2);
            for (long long z = y; z <= limit_z; ++z) {
                long long sum_sq = x2_y2 + z * z;
                long long w2 = n - sum_sq;
                long long w = (long long)sqrt(w2);
                if (w * w == w2) {
                    if (is_perfect_cube(x + y - z)) {
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

bool check_part2(long long n) {
    long long limit_x = (long long)sqrt(n);
    for (long long x = 0; x <= limit_x; ++x) {
        long long x2 = x * x;
        for (long long y = x; y <= limit_x; ++y) {
            long long x2_y2 = x2 + y * y;
            if (x2_y2 > n) break;
            long long limit_z = (long long)sqrt(n - x2_y2);
            for (long long z = y; z <= limit_z; ++z) {
                long long sum_sq = x2_y2 + z * z;
                long long w2 = n - sum_sq;
                long long w = (long long)sqrt(w2);
                if (w * w == w2) {
                    if (is_perfect_cube(x + y - z)) {
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

int main() {
    cout << "Starting search..." << endl;
    for (long long n = 0; n <= 1000000; ++n) {
        if (!check_part1(n)) {
            cout << "COUNTEREXAMPLE found for Part 1: n = " << n << endl;
            return 0;
        }
        if (!check_part2(n)) {
            cout << "COUNTEREXAMPLE found for Part 2: n = " << n << endl;
            return 0;
        }
        if (n % 100000 == 0 && n > 0) {
            cout << "Checked " << n << "..." << endl;
        }
    }
    cout << "No counterexample found up to 1,000,000." << endl;
    return 0;
}
