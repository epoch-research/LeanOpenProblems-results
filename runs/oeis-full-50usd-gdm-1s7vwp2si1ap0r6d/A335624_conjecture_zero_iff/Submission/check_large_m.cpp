#include <iostream>
#include <vector>
#include <cmath>
#include <cstdlib>

using namespace std;

// We want to write 2 * m = x1^2 + y1^2 + z1^2 + w1^2
// such that 2 * x1 + 6 * y1 + 8 * z1 is a perfect square.
// Let us write a heuristic finder.
bool find_rep(int m) {
    int limit = 2 * m;
    int max_val = sqrt(limit);
    
    // We can try to pick z1 first, then y1, then x1, and check if the remainder is a square.
    // To make it fast, we can do some trials. Since we want to find ANY representation,
    // we can loop z1, y1, x1 in some order, but stop as soon as we find one.
    // To find it even faster, we can start the search from some values, or just do a simple nested loop.
    // Actually, for larger m, there are many representations, so a nested loop will find one almost instantly!
    // Let us do a simple nested loop but with a limit on iterations, or just standard nested loops.
    for (int z1 = 0; z1 * z1 <= limit; ++z1) {
        int z1_sq = z1 * z1;
        for (int y1 = 0; z1_sq + y1 * y1 <= limit; ++y1) {
            int y1_sq = y1 * y1;
            int sum_2 = z1_sq + y1_sq;
            for (int x1 = 0; sum_2 + x1 * x1 <= limit; ++x1) {
                int rem = limit - (sum_2 + x1 * x1);
                int w1 = round(sqrt(rem));
                if (w1 * w1 == rem) {
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
    cout << "Checking odd m up to 1,000,000..." << endl;
    for (int m = 1; m < 1000000; m += 2) {
        if (m == 1 || m == 3 || m == 5 || m == 43) continue;
        if (!find_rep(m)) {
            cout << "No representation for m = " << m << endl;
            return 0;
        }
        if (m % 100000 == 1) {
            cout << "Checked up to m = " << m << endl;
        }
    }
    cout << "Checked all odd m up to 1,000,000. All have representations!" << endl;
    return 0;
}
