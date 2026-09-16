#include <iostream>

using namespace std;

typedef unsigned __int128 u128;

int BASE = 38;
long long nodes = 0;
int max_L = 137;

void dfs(int k, int L, u128 Ak, u128 Vk, int d_prev) {
    nodes++;
    if (k == L) {
        if (Ak == Vk * d_prev) {
            cout << "Found solution: " << (long long)Ak << " for L=" << L << "\n";
        }
        return;
    }

    int m = L - k;
    
    // v_max calculation
    u128 v = Vk * d_prev + (BASE - 1);
    for (int i = 0; i < m - 1; i++) {
        v = v * (BASE - 1) + (BASE - 1);
    }
    u128 v_max = v * (BASE - 1);
    
    u128 a_min = Ak;
    for (int i = 0; i < m; i++) {
        a_min *= BASE;
    }
    
    if (v_max < a_min) return;
    
    for (int d = 0; d < BASE; d++) {
        if (k == 0 && d == 0) continue;
        dfs(k + 1, L, Ak * BASE + d, (k > 0 ? Vk * d_prev + d : (u128)d), d);
    }
}

int main() {
    for (int L = 1; L <= 7; L++) {
        long long old_nodes = nodes;
        dfs(0, L, 0, 0, 0);
        cout << "L=" << L << " nodes=" << (nodes - old_nodes) << "\n";
    }
    return 0;
}
