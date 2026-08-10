#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <random>
#include <chrono>

using namespace std;

const int primes[] = {3, 5, 7, 11, 13, 17, 19, 31, 37, 41, 61, 73, 97, 109, 151, 181, 241, 257, 331, 433, 577, 631, 673, 1321};
const int num_primes = 24;

const int M = 720;
const int num_cells = (M / 2) * (M / 2); // 360 * 360 = 129600

long long power(long long base, long long exp, long long mod) {
    long long res = 1;
    base %= mod;
    while (exp > 0) {
        if (exp % 2 == 1) res = (res * base) % mod;
        base = (base * base) % mod;
        exp /= 2;
    }
    return res;
}

// Map subgrid cell (sub_x, sub_y) where x = 2*sub_x + 1, y = 2*sub_y + 2
// sub_x in [0, M/2 - 1], sub_y in [0, M/2 - 1]
inline int get_cell_idx(int sub_x, int sub_y) {
    return sub_x + sub_y * (M / 2);
}

int main() {
    auto t0 = chrono::high_resolution_clock::now();
    
    cout << "Precomputing subgrid cell values..." << endl;
    vector<vector<vector<int>>> cells_with_val(num_primes);
    for (int p_idx = 0; p_idx < num_primes; ++p_idx) {
        cells_with_val[p_idx].resize(primes[p_idx]);
    }
    
    vector<vector<int>> cell_vals(num_cells, vector<int>(num_primes));
    
    for (int sub_x = 0; sub_x < M / 2; ++sub_x) {
        int x = 2 * sub_x + 1;
        for (int sub_y = 0; sub_y < M / 2; ++sub_y) {
            int y = 2 * sub_y + 2;
            int cell_idx = get_cell_idx(sub_x, sub_y);
            for (int p_idx = 0; p_idx < num_primes; ++p_idx) {
                int p = primes[p_idx];
                int val = (power(2, x, p) + 11 * power(2, y, p)) % p;
                cells_with_val[p_idx][val].push_back(cell_idx);
                cell_vals[cell_idx][p_idx] = val;
            }
        }
    }
    
    cout << "Precomputation done. Total subgrid cells: " << num_cells << endl;
    
    mt19937 rng(1337);
    vector<int> chosen_k(num_primes);
    chosen_k[0] = 2; // Fixed to 2 for prime 3 to ensure N = 2 mod 3
    for (int p_idx = 1; p_idx < num_primes; ++p_idx) {
        chosen_k[p_idx] = rng() % primes[p_idx];
    }
    
    vector<int> coverage(num_cells, 0);
    vector<int> uncovered;
    vector<int> cell_to_uncovered_idx(num_cells, -1);
    
    for (int p_idx = 0; p_idx < num_primes; ++p_idx) {
        int k = chosen_k[p_idx];
        for (int cell : cells_with_val[p_idx][k]) {
            coverage[cell]++;
        }
    }
    
    for (int cell = 0; cell < num_cells; ++cell) {
        if (coverage[cell] == 0) {
            cell_to_uncovered_idx[cell] = uncovered.size();
            uncovered.push_back(cell);
        }
    }
    
    cout << "Initial uncovered: " << uncovered.size() << endl;
    int best_uncovered = uncovered.size();
    vector<int> best_chosen = chosen_k;
    
    long long step = 0;
    while (!uncovered.empty() && step < 2000000LL) {
        step++;
        if (step % 200000 == 0) {
            cout << "Step " << step << ": uncovered " << uncovered.size() << ", best " << best_uncovered << endl;
        }
        
        int unc_idx = rng() % uncovered.size();
        int c_idx = uncovered[unc_idx];
        
        int best_p_idx = -1;
        int best_diff = 1e9;
        int best_new_k = -1;
        
        // Try some random primes to change (excluding prime 3 at index 0)
        for (int attempt = 0; attempt < 6; ++attempt) {
            int p_idx = rng() % (num_primes - 1) + 1; // 1 to num_primes - 1
            int old_k = chosen_k[p_idx];
            int new_k = cell_vals[c_idx][p_idx];
            if (old_k == new_k) continue;
            
            int becoming_uncovered = 0;
            for (int cell : cells_with_val[p_idx][old_k]) {
                if (coverage[cell] == 1) becoming_uncovered++;
            }
            int becoming_covered = 0;
            for (int cell : cells_with_val[p_idx][new_k]) {
                if (coverage[cell] == 0) becoming_covered++;
            }
            
            int diff = becoming_uncovered - becoming_covered;
            if (diff < best_diff) {
                best_diff = diff;
                best_p_idx = p_idx;
                best_new_k = new_k;
            }
        }
        
        if (best_p_idx != -1 && best_diff <= 0) { // allow flat moves
            int p_idx = best_p_idx;
            int old_k = chosen_k[p_idx];
            int new_k = best_new_k;
            
            for (int cell : cells_with_val[p_idx][old_k]) {
                coverage[cell]--;
                if (coverage[cell] == 0) {
                    cell_to_uncovered_idx[cell] = uncovered.size();
                    uncovered.push_back(cell);
                }
            }
            for (int cell : cells_with_val[p_idx][new_k]) {
                if (coverage[cell] == 0) {
                    int last_cell = uncovered.back();
                    int idx = cell_to_uncovered_idx[cell];
                    uncovered[idx] = last_cell;
                    cell_to_uncovered_idx[last_cell] = idx;
                    uncovered.pop_back();
                    cell_to_uncovered_idx[cell] = -1;
                }
                coverage[cell]++;
            }
            chosen_k[p_idx] = new_k;
            
            if (uncovered.size() < best_uncovered) {
                best_uncovered = uncovered.size();
                best_chosen = chosen_k;
                if (best_uncovered == 0) break;
            }
        }
    }
    
    cout << "Finished. Best uncovered: " << best_uncovered << endl;
    if (best_uncovered == 0) {
        cout << "SUCCESS! Covering system found!" << endl;
        for (int p_idx = 0; p_idx < num_primes; ++p_idx) {
            cout << primes[p_idx] << ": " << chosen_k[p_idx] << ", ";
        }
        cout << endl;
    } else {
        cout << "Best chosen residues so far:" << endl;
        for (int p_idx = 0; p_idx < num_primes; ++p_idx) {
            cout << primes[p_idx] << ": " << best_chosen[p_idx] << ", ";
        }
        cout << endl;
    }
    
    auto t1 = chrono::high_resolution_clock::now();
    cout << "Total time: " << chrono::duration_cast<chrono::seconds>(t1 - t0).count() << " seconds." << endl;
    return 0;
}
