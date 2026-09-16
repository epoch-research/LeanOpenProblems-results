#include <iostream>
#include <vector>
#include <cmath>

using namespace std;

typedef unsigned __int128 u128;

int BASE = 38;
int MAX_L = 137;

vector<u128> sols;

void dfs(int k, u128 Ak, u128 Vk, int d_prev) {
    if (k == MAX_L) return; // shouldn't happen if bounded right

    // if k > 0, we can check if we want to stop
    // but the tree needs proper bound
    int m = MAX_L - k;
    
    // We actually only need to check up to exact length L.
    // Wait, the python search fixed L, then searched.
    // Let's do that.
}

int main() {
    // ...
    return 0;
}
