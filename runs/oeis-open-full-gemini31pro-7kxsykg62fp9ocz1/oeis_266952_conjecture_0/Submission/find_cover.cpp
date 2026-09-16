#include <iostream>
#include <vector>
#include <algorithm>

using namespace std;

// We want to find c_q for each q in P such that all x are covered.
// x is covered by q if x % q == 0, 2, c_q, or c_q + 2.
// We only consider x not 0 or 2 mod q.

int P[] = {5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79};
int num_P = 15;

vector<int> c(num_P, 0);

bool dfs(int depth, vector<int> remaining_x) {
    if (remaining_x.empty()) return true;
    if (depth == num_P) return false;

    int q = P[depth];
    
    // For each possible c_q from 0 to q-1
    for (int cq = 0; cq < q; cq++) {
        vector<int> next_x;
        for (int x : remaining_x) {
            int xq = x % q;
            if (xq != 0 && xq != 2 && xq != cq && xq != (cq + 2) % q) {
                next_x.push_back(x);
            }
        }
        
        // Pruning: if next_x is too large, we might not be able to cover it.
        // A simple heuristic: try the cq that leaves the minimum next_x size.
    }
    return false;
}

int main() {
    // Generate all x up to Prod(P) ... wait Prod(P) is too large!
    // Instead of x, we can just use backtracking on the CRT constraints.
    return 0;
}
