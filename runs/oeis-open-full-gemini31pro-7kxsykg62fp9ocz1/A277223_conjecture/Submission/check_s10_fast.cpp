#include <iostream>
#include <vector>

using namespace std;

int S(long long m) {
    int s = 0;
    while(m > 0) {
        s += m % 10;
        m /= 10;
    }
    return s;
}

void dfs(long long current, int sum_left, int length) {
    if (length == 0) {
        if (sum_left == 0 && current > 0) {
            int max_k = 0;
            for (int k = 1; k <= 100; k++) {
                // To avoid overflow, we only check if k * current doesn't overflow
                if (k * current / k != current) continue; 
                if (S(k * current) == k) {
                    max_k = k;
                }
            }
            if (max_k > 0 && max_k < 12 && max_k != 9) {
                cout << "Counterexample! n = " << current << ", max_k = " << max_k << "\n";
                exit(0);
            }
        }
        return;
    }
    for (int d = 0; d <= 9 && d <= sum_left; d++) {
        if (current == 0 && d == 0 && length > 1) continue; // no leading zeros unless it's the last
        dfs(current * 10 + d, sum_left - d, length - 1);
    }
}

int main() {
    for (int len = 1; len <= 16; len++) {
        dfs(0, 10, len); // check K=10
        dfs(0, 7, len);  // check K=7
        dfs(0, 8, len);  // check K=8
        dfs(0, 11, len); // check K=11
    }
    cout << "No counterexample up to 16 digits.\n";
    return 0;
}
