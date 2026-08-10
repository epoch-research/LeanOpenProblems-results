#include <iostream>
#include <vector>
#include <cmath>
#include <set>

using namespace std;

int main() {
    int limit = 5000000;
    vector<bool> represented(limit, false);
    
    // We can iterate over x, y, z, w
    // To optimize, we loop x, y, z, then check if the remaining part is a square.
    // Also we only care about x + 3y + 4z being a square.
    // So we can loop x, y, z such that x^2 + y^2 + z^2 < limit.
    // If x + 3y + 4z is a square, we mark all n = x^2 + y^2 + z^2 + w^2 < limit as represented.
    
    vector<int> sq;
    for (int i = 0; i * i < limit; ++i) {
        sq.push_back(i * i);
    }
    
    // Check if a number is a square
    auto is_square = [](long long n) {
        long long r = round(sqrt(n));
        return r * r == n;
    };
    
    for (int x = 0; x * x < limit; ++x) {
        int x2 = x * x;
        for (int y = 0; x2 + y * y < limit; ++y) {
            int y2 = y * y;
            int x_3y = x + 3 * y;
            for (int z = 0; x2 + y2 + z * z < limit; ++z) {
                int z2 = z * z;
                if (is_square(x_3y + 4 * z)) {
                    int base = x2 + y2 + z2;
                    for (int w = 0; base + w * w < limit; ++w) {
                        represented[base + w * w] = true;
                    }
                }
            }
        }
    }
    
    // Now verify the conjecture
    set<int> m_vals = {1, 3, 5, 43};
    int counterexamples = 0;
    for (int n = 1; n < limit; ++n) {
        int temp = n;
        int k4_3 = 0;
        while (temp % 2 == 0) {
            temp /= 2;
            k4_3++;
        }
        bool has_form = false;
        if (k4_3 % 4 == 3) {
            if (m_vals.count(temp)) {
                has_form = true;
            }
        }
        
        bool is_zero = !represented[n];
        if (is_zero != has_form) {
            cout << "Counterexample: n = " << n << ", represented = " << represented[n] << ", has_form = " << has_form << endl;
            counterexamples++;
            if (counterexamples > 10) break;
        }
    }
    if (counterexamples == 0) {
        cout << "Conjecture holds up to " << limit << "!" << endl;
    }
    return 0;
}
