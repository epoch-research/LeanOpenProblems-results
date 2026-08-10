#include <iostream>
#include <vector>
#include <cmath>

using namespace std;

bool has_rep(int m) {
    int n = 8 * m;
    // We want to find x, y, z, w such that:
    // x^2 + y^2 + z^2 + w^2 = 8 * m
    // and x + 3*y + 4*z is a perfect square.
    // Since x, y, z, w must all be even, let x = 2*x1, y = 2*y1, z = 2*z1, w = 2*w1.
    // x1^2 + y1^2 + z1^2 + w1^2 = 2 * m.
    // And 2 * x1 + 6 * y1 + 8 * z1 must be a perfect square.
    // This is equivalent to x1 + 3*y1 + 4*z1 = 2 * s^2 for some s.
    
    int limit = 2 * m;
    // We can loop x1, y1, z1 such that x1^2 + y1^2 + z1^2 <= limit
    // and check if limit - (x1^2 + y1^2 + z1^2) is a perfect square.
    for (int x1 = 0; x1 * x1 <= limit; ++x1) {
        int x1_sq = x1 * x1;
        for (int y1 = 0; x1_sq + y1 * y1 <= limit; ++y1) {
            int y1_sq = y1 * y1;
            int sum_1 = x1_sq + y1_sq;
            for (int z1 = 0; sum_1 + z1 * z1 <= limit; ++z1) {
                int rem = limit - (sum_1 + z1 * z1);
                // check if rem is a square
                int w1 = round(sqrt(rem));
                if (w1 * w1 == rem) {
                    // Check if 2 * x1 + 6 * y1 + 8 * z1 is a perfect square
                    int val = 2 * x1 + 6 * y1 + 8 * z1;
                    int s = round(sqrt(val));
                    if (s * s == val) {
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

int main() {
    cout << "Checking odd m..." << endl;
    for (int m = 1; m < 100000; m += 2) {
        if (m == 1 || m == 3 || m == 5 || m == 43) continue;
        if (!has_rep(m)) {
            cout << "No representation for m = " << m << ", n = " << 8 * m << endl;
            return 0;
        }
    }
    cout << "Checked up to m = 100000. All have representations!" << endl;
    return 0;
}
