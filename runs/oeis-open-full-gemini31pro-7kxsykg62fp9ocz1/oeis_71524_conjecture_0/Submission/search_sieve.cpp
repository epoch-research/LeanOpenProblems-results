#include <iostream>
#include <vector>
#include <cstdint>
#include <chrono>

using namespace std;

const long long MAX_VAL = 200000000LL; // covers n=10000 => (10000)^2 + (10000)^2 = 2*10^8
vector<bool> is_p(MAX_VAL + 1, true);

void sieve() {
    is_p[0] = is_p[1] = false;
    for (long long i = 2; i * i <= MAX_VAL; ++i) {
        if (is_p[i]) {
            for (long long j = i * i; j <= MAX_VAL; j += i) {
                is_p[j] = false;
            }
        }
    }
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
    sieve();
    auto sieve_end = chrono::high_resolution_clock::now();
    cout << "Sieve done in " << chrono::duration_cast<chrono::seconds>(sieve_end - start).count() << "s" << endl;
    
    for (int n = 3800; n <= 10000; ++n) {
        int k = n / 2;
        vector<vector<int>> M(k, vector<int>(k, 0));
        if (n % 2 == 0) {
            for (int x = 0; x < k; ++x) {
                for (int y = 0; y < k; ++y) {
                    long long val = (2LL * x + 1) * (2LL * x + 1) + (2LL * y + 2) * (2LL * y + 2);
                    if (is_p[val]) M[x][y] = 1;
                }
            }
        } else {
            for (int x = 0; x < k; ++x) {
                for (int y = 0; y < k; ++y) {
                    long long val = (2LL * x + 2) * (2LL * x + 2) + (2LL * y + 3) * (2LL * y + 3);
                    if (is_p[val]) M[x][y] = 1;
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
