#include <iostream>
#include <vector>

using namespace std;

int S(__int128 m) {
    int s = 0;
    while(m > 0) {
        s += (int)(m % 10);
        m /= 10;
    }
    return s;
}

// We want to generate sum of 10 powers of 10 up to 10^35
// This means generating a 35 digit number with digit sum 10.
// Since __int128 goes up to 3.4 * 10^38, we can do 35 digits.

void dfs(__int128 current, int sum_left, int length) {
    if (length == 0) {
        if (sum_left == 0) {
            int max_k = 0;
            for(int k=11; k<=100; k++) {
                if (S(k * current) == k) {
                    max_k = k;
                    break;
                }
            }
            if (max_k == 0) {
                for(int k=101; k<=900; k++) {
                    if (S(k * current) == k) {
                        max_k = k;
                        break;
                    }
                }
                if (max_k == 0) {
                    cout << "Found! n=" << (long long)current << "\n";
                    exit(0);
                }
            }
        }
        return;
    }
    for(int d=0; d<=9; d++) {
        if (d <= sum_left) {
            if (current == 0 && d == 0 && length > 1) continue;
            dfs(current * 10 + d, sum_left - d, length - 1);
        }
    }
}

int main() {
    // To go up to 30 digits in DFS is too slow (10^8 states maybe?)
    // Let's do random search for lengths 20 to 35
    return 0;
}
