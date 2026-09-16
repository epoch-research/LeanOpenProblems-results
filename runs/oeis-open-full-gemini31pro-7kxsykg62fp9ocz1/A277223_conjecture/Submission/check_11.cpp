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

void dfs(__int128 current, int sum_left, int length, int current_mod) {
    if (length == 0) {
        if (sum_left == 0 && current_mod == 0 && current > 0) {
            __int128 n = current / 11;
            int max_k = 0;
            for(int k=12; k<=200; k++) {
                if (S(k * n) == k) {
                    max_k = k;
                    break;
                }
            }
            if (max_k == 0) {
                // verify k=11
                if (S(11 * n) == 11) {
                    cout << "Found! 11n=" << (long long)current << "\n";
                    exit(0);
                }
            }
        }
        return;
    }
    
    for(int d=0; d<=9; d++) {
        if (d <= sum_left) {
            if (current == 0 && d == 0 && length > 1) continue;
            dfs(current * 10 + d, sum_left - d, length - 1, (current_mod * 10 + d) % 11);
        }
    }
}

int main() {
    for(int len=1; len<=18; len++) {
        dfs(0, 11, len, 0);
    }
    cout << "None up to 18\n";
    return 0;
}
