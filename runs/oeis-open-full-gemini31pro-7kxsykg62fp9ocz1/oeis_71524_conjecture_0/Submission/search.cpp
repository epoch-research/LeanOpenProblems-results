#include <iostream>
#include <vector>

using namespace std;

bool is_prime(long long n) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0 || n % 3 == 0) return false;
    for (long long i = 5; i * i <= n; i += 6) {
        if (n % i == 0 || n % (i + 2) == 0) return false;
    }
    return true;
}

long long rank_mod_p(vector<vector<long long>>& M, int k, long long p) {
    int r = 0;
    for (int c = 0; c < k; ++c) {
        int pivot = r;
        while (pivot < k && M[pivot][c] == 0) pivot++;
        if (pivot == k) continue;
        swap(M[r], M[pivot]);
        long long inv = 1;
        long long base = M[r][c];
        long long exp = p - 2;
        while (exp > 0) {
            if (exp % 2 == 1) inv = (inv * base) % p;
            base = (base * base) % p;
            exp /= 2;
        }
        for (int i = r + 1; i < k; ++i) {
            if (M[i][c] != 0) {
                long long factor = (M[i][c] * inv) % p;
                for (int j = c; j < k; ++j) {
                    M[i][j] = (M[i][j] - factor * M[r][j]) % p;
                    if (M[i][j] < 0) M[i][j] += p;
                }
            }
        }
        r++;
    }
    return r;
}

int main() {
    long long p = 1000000007;
    for (int n = 2600; n <= 10000; ++n) {
        int k = n / 2;
        vector<vector<long long>> M(k, vector<long long>(k, 0));
        if (n % 2 == 0) {
            for (int x = 0; x < k; ++x) {
                for (int y = 0; y < k; ++y) {
                    long long val = (2LL * x + 1) * (2LL * x + 1) + (2LL * y + 2) * (2LL * y + 2);
                    if (is_prime(val)) M[x][y] = 1;
                }
            }
        } else {
            for (int x = 0; x < k; ++x) {
                for (int y = 0; y < k; ++y) {
                    long long val = (2LL * x + 2) * (2LL * x + 2) + (2LL * y + 3) * (2LL * y + 3);
                    if (is_prime(val)) M[x][y] = 1;
                }
            }
        }
        long long r = rank_mod_p(M, k, p);
        if (r < k) {
            cout << "POSSIBLE COUNTEREXAMPLE: n=" << n << " rank=" << r << endl;
        }
        if (n % 100 == 0) cout << "Checked n=" << n << endl;
    }
    return 0;
}
