#include <iostream>
#include <vector>
#include <cmath>

using namespace std;

// Using vector<char> to act as a fast bitset
int main() {
    long long limit = 100000000; // 100 million
    vector<char> is_quad(limit + 1, 0);

    // Populate is_quad
    for (long long x = 0; x * x <= limit; ++x) {
        long long x2 = x * x;
        for (long long y = 0; ; ++y) {
            long long val = x2 + 2 * y * y;
            if (val > limit) break;
            is_quad[val] = 1;
        }
    }
    cout << "Finished populating is_quad" << endl;

    vector<long long> K_vals;
    for (long long z = 0; ; ++z) {
        long long z4 = z * z * z * z;
        if (z4 > limit) break;
        for (long long w = 0; ; ++w) {
            long long val = z4 + z * z * w * w + 4 * w * w * w * w;
            if (val > limit) {
                break;
            }
            K_vals.push_back(val);
        }
    }
    cout << "K_vals size: " << K_vals.size() << endl;

    long long unrepresented_count = 0;
    for (long long n = 0; n <= limit; ++n) {
        bool found = false;
        for (long long K : K_vals) {
            if (n >= K && is_quad[n - K]) {
                found = true;
                break;
            }
        }
        if (!found) {
            if (unrepresented_count < 50) {
                cout << "Unrepresented: " << n << endl;
            }
            unrepresented_count++;
        }
    }

    cout << "Total unrepresented: " << unrepresented_count << endl;
    return 0;
}
