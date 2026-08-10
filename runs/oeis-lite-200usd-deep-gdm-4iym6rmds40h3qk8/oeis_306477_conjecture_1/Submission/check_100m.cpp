#include <iostream>
#include <vector>
#include <algorithm>

using namespace std;

long long choose(long long n, long long k) {
    if (n < k) return 0;
    if (k == 0 || k == n) return 1;
    if (k > n - k) k = n - k;
    long long ans = 1;
    for (int i = 1; i <= k; i++) {
        ans = ans * (n - i + 1) / i;
    }
    return ans;
}

int main() {
    long long max_n = 100000000; // 100 million
    vector<long long> x_vals;
    for (long long x = 0; ; x++) {
        long long v = choose(x + 3, 4);
        if (v > max_n) break;
        x_vals.push_back(v);
    }
    vector<long long> y_vals;
    for (long long y = 0; ; y++) {
        long long v = choose(y + 5, 6);
        if (v > max_n) break;
        y_vals.push_back(v);
    }
    vector<long long> z_vals;
    for (long long z = 0; ; z++) {
        long long v = choose(z + 7, 8);
        if (v > max_n) break;
        z_vals.push_back(v);
    }

    vector<long long> S_list;
    for (long long xv : x_vals) {
        for (long long yv : y_vals) {
            for (long long zv : z_vals) {
                long long s = xv + yv + zv;
                if (s <= max_n) {
                    S_list.push_back(s);
                }
            }
        }
    }
    sort(S_list.begin(), S_list.end());
    S_list.erase(unique(S_list.begin(), S_list.end()), S_list.end());

    vector<bool> rep(max_n + 1, false);

    vector<long long> T_vals;
    for (long long w = 0; ; w++) {
        long long v = choose(w + 2, 2);
        if (v > max_n) break;
        T_vals.push_back(v);
    }

    for (long long s : S_list) {
        for (long long t : T_vals) {
            long long val = s + t;
            if (val <= max_n) {
                rep[val] = true;
            } else {
                break;
            }
        }
    }

    long long missing_count = 0;
    for (long long n = 1; n <= max_n; n++) {
        if (!rep[n]) {
            if (missing_count < 50) {
                cout << "Missing: " << n << endl;
            }
            missing_count++;
        }
    }
    cout << "Total missing up to " << max_n << ": " << missing_count << endl;

    return 0;
}
