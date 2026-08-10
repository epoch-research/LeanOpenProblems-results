#include <iostream>
#include <vector>
#include <cmath>
#include <thread>
#include <mutex>
#include <atomic>

using namespace std;

bool find_rep(int m, const vector<uint8_t>& is_sq, int MAX_VAL) {
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
    int MAX_VAL = 400000005;
    vector<uint8_t> is_sq(MAX_VAL, 0);
    for (int i = 0; i * i < MAX_VAL; ++i) {
        is_sq[i * i] = 1;
    }
    
    int num_threads = 32;
    vector<thread> threads;
    atomic<int> global_m(1);
    atomic<bool> found_counterexample(false);
    int limit_m = 200000000;
    
    cout << "Starting multi-threaded search up to m = " << limit_m << " using " << num_threads << " threads..." << endl;
    
    for (int t = 0; t < num_threads; ++t) {
        threads.push_back(thread([&]() {
            while (true) {
                int m = global_m.fetch_add(2);
                if (m >= limit_m || found_counterexample) {
                    break;
                }
                if (m == 1 || m == 3 || m == 5 || m == 43) continue;
                if (!find_rep(m, is_sq, MAX_VAL)) {
                    cout << "\nCOUNTEREXAMPLE FOUND! m = " << m << ", n = " << 8 * m << endl;
                    found_counterexample = true;
                    break;
                }
                if (m % 1000000 == 1) {
                    cout << "Checked up to m = " << m << endl;
                    cout.flush();
                }
            }
        }));
    }
    
    for (auto& th : threads) {
        th.join();
    }
    
    if (!found_counterexample) {
        cout << "\nSearch complete. No counterexamples found up to m = " << limit_m << endl;
    }
    return 0;
}
