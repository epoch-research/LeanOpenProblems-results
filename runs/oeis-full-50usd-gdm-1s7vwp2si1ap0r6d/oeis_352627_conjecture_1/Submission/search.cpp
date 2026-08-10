#include <iostream>
#include <vector>
#include <cmath>

using namespace std;

int main() {
    long long limit = 100000000; // 100 million
    vector<bool> represented(limit + 1, false);

    vector<long long> K_vals;
    for (long long z = 0; ; ++z) {
        long long z4 = z * z * z * z;
        if (z4 > limit) break;
        for (long long w = 0; ; ++w) {
            long long val = z4 + z * z * w * w + 4 * w * w * w * w;
            if (val > limit) {
                if (w == 0) break;
                continue;
            }
            K_vals.push_back(val);
        }
    }

    vector<long long> quad_vals;
    for (long long x = 0; x * x <= limit; ++x) {
        long long x2 = x * x;
        for (long long y = 0; x2 + 2 * y * y <= limit; ++y) {
            quad_vals.push_back(x2 + 2 * y * y);
        }
    }

    cout << "K_vals size: " << K_vals.size() << endl;
    cout << "quad_vals size: " << quad_vals.size() << endl;

    // To avoid sorting quad_vals, we can just use them.
    // To make it super fast, we can loop over K_vals, then over quad_vals
    for (long long K : K_vals) {
        for (long long q : quad_vals) {
            if (K + q <= limit) {
                represented[K + q] = true;
            }
        }
    }

    long long count = 0;
    for (long long i = 0; i <= limit; ++i) {
        if (!represented[i]) {
            if (count < 50) {
                cout << "Unrepresented: " << i << endl;
            }
            count++;
        }
    }
    cout << "Total unrepresented: " << count << endl;
    return 0;
}
