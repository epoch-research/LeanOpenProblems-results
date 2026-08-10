#include <iostream>
#include <vector>
#include <cmath>
#include <unordered_set>

using namespace std;

// Check if a number is a perfect cube
bool is_cube(long long n) {
    long long c = round(cbrt(n));
    return c * c * c == n;
}

int main() {
    int max_n = 1000000;
    vector<bool> p1_ok(max_n + 1, false);
    vector<bool> p2_ok(max_n + 1, false);

    int limit = sqrt(max_n) + 1;

    // We can precompute cubes for fast lookup
    // Since x + y - z can be negative, we need to handle negative cubes.
    // x + y - z can range from -limit to 2*limit
    // max absolute value is around 2000
    unordered_set<int> cubes;
    for (int i = -200; i <= 200; ++i) {
        cubes.insert(i * i * i);
    }

    cout << "Starting search..." << endl;

    for (int x = 0; x < limit; ++x) {
        int x2 = x * x;
        for (int y = 0; y < limit; ++y) {
            int x2_y2 = x2 + y * y;
            if (x2_y2 > max_n) break;
            for (int z = 0; z < limit; ++z) {
                int val = x2_y2 + z * z;
                if (val > max_n) break;

                int diff = x + y - z;
                if (cubes.count(diff) == 0) continue;

                // Part 1: x >= y <= z and x%2 == y%2
                if (x >= y && y <= z && (x % 2 == y % 2)) {
                    for (int w = 0; val + w * w <= max_n; ++w) {
                        p1_ok[val + w * w] = true;
                    }
                }

                // Part 2: x <= y <= z
                if (x <= y && y <= z) {
                    for (int w = 0; val + w * w <= max_n; ++w) {
                        p2_ok[val + w * w] = true;
                    }
                }
            }
        }
    }

    for (int n = 0; n <= max_n; ++n) {
        if (!p1_ok[n]) {
            cout << "Counterexample for Part 1 at n = " << n << endl;
            return 0;
        }
        if (!p2_ok[n]) {
            cout << "Counterexample for Part 2 at n = " << n << endl;
            return 0;
        }
    }

    cout << "All n <= " << max_n << " satisfy both parts!" << endl;
    return 0;
}
