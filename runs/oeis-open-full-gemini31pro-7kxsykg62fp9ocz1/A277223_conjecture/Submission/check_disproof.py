import subprocess

cpp = """
#include <iostream>
using namespace std;

int S(__int128 m) {
    int s = 0;
    while(m > 0) {
        s += m % 10;
        m /= 10;
    }
    return s;
}

void dfs(__int128 current, int sum_left, int length, int target_K) {
    if (length == 0) {
        if (sum_left == 0 && current > 0 && current % target_K == 0) {
            __int128 n = current / target_K;
            int max_k = 0;
            for (int k = 1; k <= 500; k++) {
                if (S(k * n) == k) max_k = k;
            }
            if (max_k == target_K) {
                cout << "COUNTEREXAMPLE FOUND: n=" << (long long)n << " max_k=" << max_k << "\\n";
                exit(0);
            }
        }
        return;
    }
    for (int d = 0; d <= 9; d++) {
        if (d <= sum_left) {
            dfs(current * 10 + d, sum_left - d, length - 1, target_K);
        }
    }
}

int main() {
    for (int target : {7, 8, 10, 11}) {
        for (int len = 1; len <= 22; len++) {
            dfs(0, target, len, target);
        }
    }
    cout << "No counterexample up to 22 digits.\\n";
    return 0;
}
"""
with open("/workspace/leanproject/Submission/search_ce.cpp", "w") as f:
    f.write(cpp)

subprocess.run(["g++", "-O3", "/workspace/leanproject/Submission/search_ce.cpp"])
subprocess.run(["./a.out"])
