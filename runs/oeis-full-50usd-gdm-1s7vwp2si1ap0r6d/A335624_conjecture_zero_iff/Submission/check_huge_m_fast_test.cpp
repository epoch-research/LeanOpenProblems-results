#include <iostream>
#include <vector>
#include <cmath>

using namespace std;

bool find_rep(int m, const vector<bool>& is_sq, int MAX_VAL) {
    int limit = 2 * m;
    int max_z = sqrt(limit);
    
    for (int z1 = max_z; z1 >= 0; --z1) {
        int z1_sq = z1 * z1;
        int max_y = sqrt(limit - z1_sq);
        for (int y1 = max_y; y1 >= 0; --y1) {
            int y1_sq = y1 * y1;
            int sum_2 = z1_sq + y1_sq;
            int max_x = sqrt(limit - sum_2);
            for (int x1 = max_x; x1 >= 0; --x1) {
                int rem = limit - (sum_2 + x1 * x1);
                if (is_sq[rem]) {
                    int val = 2 * x1 + 6 * y1 + 8 * z1;
                    if (val < MAX_VAL && is_sq[val]) {
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

int main() {
    int MAX_VAL = 20000005;
    vector<bool> is_sq(MAX_VAL, false);
    for (int i = 0; i * i < MAX_VAL; ++i) {
        is_sq[i * i] = true;
    }
    
    cout << "Checking odd m up to 5,000,000..." << endl;
    for (int m = 1; m < 10000000; m += 2) {
        if (m == 1 || m == 3 || m == 5 || m == 43) continue;
        if (!find_rep(m, is_sq, MAX_VAL)) {
            cout << "No representation found for m = " << m << ", n = " << 8 * m << endl;
            return 0;
        }
        if (m % 1000000 == 1) {
            cout << "Checked up to m = " << m << endl;
            cout.flush();
        }
    }
    cout << "Checked all odd m up to 5,000,000. All have representations!" << endl;
    return 0;
}
