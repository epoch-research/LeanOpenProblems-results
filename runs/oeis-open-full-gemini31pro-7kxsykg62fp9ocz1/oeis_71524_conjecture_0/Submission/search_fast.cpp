#include <iostream>
#include <vector>
#include <cstdint>
#include <chrono>

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

int rank_mod2(const vector<vector<int>>& M, int k) {
    int words = (k + 63) / 64;
    vector<vector<uint64_t>> B(k, vector<uint64_t>(words, 0));
    for (int i = 0; i < k; ++i) {
        for (int j = 0; j < k; ++j) {
            if (M[i][j]) {
                B[i][j / 64] |= (1ULL << (j % 64));
            }
        }
    }
    int r = 0;
    for (int c = 0; c < k; ++c) {
        int pivot = r;
        while (pivot < k && (B[pivot][c / 64] & (1ULL << (c % 64))) == 0) pivot++;
        if (pivot == k) continue;
        if (pivot != r) swap(B[r], B[pivot]);
        for (int i = r + 1; i < k; ++i) {
            if (B[i][c / 64] & (1ULL << (c % 64))) {
                for (int w = c / 64; w < words; ++w) B[i][w] ^= B[r][w];
            }
        }
        r++;
    }
    return r;
}

long long rank_mod_p(const vector<vector<int>>& M_in, int k, long long p) {
    vector<vector<long long>> M(k, vector<long long>(k));
    for (int i = 0; i < k; ++i)
        for (int j = 0; j < k; ++j)
            M[i][j] = M_in[i][j];
            
    int r = 0;
    for (int c = 0; c < k; ++c) {
        int pivot = r;
        while (pivot < k && M[pivot][c] == 0) pivot++;
        if (pivot == k) continue;
        if (pivot != r) swap(M[r], M[pivot]);
        long long inv = 1, base = M[r][c], exp = p - 2;
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
    auto start = chrono::high_resolution_clock::now();
    for (int n = 3800; n <= 10000; ++n) {
        int k = n / 2;
        vector<vector<int>> M(k, vector<int>(k, 0));
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
        
        int r2 = rank_mod2(M, k);
        if (r2 < k) {
            int rp = rank_mod_p(M, k, 1000000007);
            if (rp < k) {
                cout << "COUNTEREXAMPLE FOUND: n=" << n << endl;
                return 0;
            }
        }
        
        if (n % 100 == 0) {
            auto now = chrono::high_resolution_clock::now();
            auto dur = chrono::duration_cast<chrono::seconds>(now - start).count();
            cout << "Checked n=" << n << " time=" << dur << "s" << endl;
        }
    }
    return 0;
}
