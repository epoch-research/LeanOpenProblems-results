#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <set>

using namespace std;

const int LIMIT = 100000000;
bool is_p[LIMIT];
vector<int> A(LIMIT, 0);
vector<int> last_occ_idx(LIMIT, -1);
vector<int> prev_occ_idx(LIMIT, -1);

void sieve() {
    fill(is_p, is_p + LIMIT, true);
    is_p[0] = is_p[1] = false;
    for (int i = 2; i * i < LIMIT; ++i) {
        if (is_p[i]) {
            for (int j = i * i; j < LIMIT; j += i) {
                is_p[j] = false;
            }
        }
    }
}

int main() {
    sieve();
    cout << "Sieve completed." << endl;

    A[0] = 0;
    A[1] = 0;
    last_occ_idx[0] = 1;

    for (int n = 1; n < LIMIT - 1; ++n) {
        int a_k = A[n];
        
        // Search the previous occurrences of a_k in reverse order (before linking!)
        int curr = last_occ_idx[a_k];
        int min_prime_p = -1;
        while (curr != -1) {
            int p = n - curr;
            if (is_p[p]) {
                min_prime_p = p;
                break; // First prime distance found is guaranteed to be the minimum!
            }
            curr = prev_occ_idx[curr];
        }

        if (min_prime_p != -1) {
            A[n + 1] = min_prime_p;
        } else {
            A[n + 1] = 0;
        }

        // Link the current occurrence of A[n+1]
        int next_val = A[n + 1];
        prev_occ_idx[n + 1] = last_occ_idx[next_val];
        last_occ_idx[next_val] = n + 1;
    }

    cout << "Simulation completed." << endl;

    set<int> appeared;
    for (int n = 1; n < LIMIT; ++n) {
        if (A[n] > 0 && A[n] < LIMIT) {
            appeared.insert(A[n]);
        }
    }

    vector<int> unappeared;
    for (int p = 2; p < 5000000; ++p) {
        if (is_p[p]) {
            if (appeared.find(p) == appeared.end()) {
                unappeared.push_back(p);
            }
        }
    }

    cout << "Primes up to 1,000,000 that have NOT appeared yet: " << unappeared.size() << endl;
    for (int i = 0; i < min(20, (int)unappeared.size()); ++i) {
        cout << unappeared[i] << " ";
    }
    cout << endl;

    return 0;
}
