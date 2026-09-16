
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

void dfs(__int128 current, int sum_left, int length) {
    if (length == 0) {
        if (sum_left == 0) {
            int max_k = 0;
            for(int k=11; k<=120; k++) {
                if (S(k * current) == k) {
                    max_k = k;
                    break;
                }
            }
            if (max_k == 0) {
                // check more
                for(int k=121; k<=300; k++) {
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
    for(int len=1; len<=18; len++) {
        dfs(0, 10, len);
    }
    cout << "None up to 18\n";
    return 0;
}
