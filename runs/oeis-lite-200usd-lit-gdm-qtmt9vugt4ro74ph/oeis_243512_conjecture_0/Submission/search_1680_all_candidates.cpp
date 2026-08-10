#include <iostream>
#include <vector>
#include <numeric>
#include <cmath>
#include <algorithm>

using namespace std;

typedef unsigned __int128 u128;

long long gcd_calc(long long a, long long b) {
    return b == 0 ? a : gcd_calc(b, a % b);
}

bool is_prime(long long n) {
    if (n <= 1) return false;
    if (n <= 3) return true;
    if (n % 2 == 0 || n % 3 == 0) return false;
    for (long long i = 5; i * i <= n; i += 6) {
        if (n % i == 0 || n % (i + 2) == 0) return false;
    }
    return true;
}

struct Task {
    int v;
    int m;
    long long p;
    long long a;
    long long b;
};

const int SIEVE_LIMIT = 300000000; // 300 million
vector<long long> sig;

int main() {
    vector<Task> tasks;
    
    // v = 23, limit on m is 44
    for (int m = 2; m < 44; m += 2) {
        long long p = 73 * m - 1;
        if (is_prime(p)) {
            long long g_num = m + 23;
            long long g_den = m;
            long long g_gcd = gcd_calc(g_num, g_den);
            tasks.push_back({23, m, p, g_num / g_gcd, g_den / g_gcd});
        }
    }
    
    // v = 73, limit on m is 140
    for (int m = 2; m < 140; m += 2) {
        long long p = 23 * m - 1;
        if (is_prime(p)) {
            long long g_num = m + 73;
            long long g_den = m;
            long long g_gcd = gcd_calc(g_num, g_den);
            tasks.push_back({73, m, p, g_num / g_gcd, g_den / g_gcd});
        }
    }
    
    // v = 1679, limit on m is 3352
    for (int m = 2; m < 3352; m += 2) {
        long long p = m - 1;
        if (is_prime(p)) {
            long long g_num = m + 1679;
            long long g_den = m;
            long long g_gcd = gcd_calc(g_num, g_den);
            tasks.push_back({1679, m, p, g_num / g_gcd, g_den / g_gcd});
        }
    }
    
    cout << "Loaded " << tasks.size() << " tasks." << endl;
    
    cout << "Allocating memory for sieve (2.4 GB)..." << endl;
    sig.assign(SIEVE_LIMIT, 0);
    cout << "Computing sieve..." << endl;
    for (int i = 1; i < SIEVE_LIMIT; i++) {
        for (int j = i; j < SIEVE_LIMIT; j += i) {
            sig[j] += i;
        }
    }
    cout << "Sieve done. Checking tasks..." << endl;
    
    int active_tasks = 0;
    for (const auto& t : tasks) {
        long long max_c = (SIEVE_LIMIT - 1) / t.b;
        if (max_c < 1) continue;
        active_tasks++;
        
        for (long long c = 1; c <= max_c; c++) {
            long long g = t.b * c;
            long long sig_g = sig[g];
            if (sig_g == t.a * c) {
                if (gcd_calc(sig_g, g) == g / t.m) {
                    if (gcd_calc(sig_g, t.p) == 1) {
                        cout << "FOUND PREIMAGE! v = " << t.v << ", m = " << t.m << ", g = " << g << ", p = " << t.p << ", i = " << g * t.p << endl;
                        return 0;
                    }
                }
            }
        }
    }
    cout << "Finished checking " << active_tasks << " active tasks under " << SIEVE_LIMIT << " and found nothing." << endl;
    return 0;
}
