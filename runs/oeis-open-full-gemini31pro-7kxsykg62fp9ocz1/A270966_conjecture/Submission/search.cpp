#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>

using namespace std;

int main() {
    long long limit = 100000000;
    vector<bool> is_prime(sqrt(limit) + 5, true);
    is_prime[0] = is_prime[1] = false;
    for (long long i = 2; i * i < is_prime.size(); ++i) {
        if (is_prime[i]) {
            for (long long j = i * i; j < is_prime.size(); j += i) {
                is_prime[j] = false;
            }
        }
    }
    
    vector<long long> gp;
    for (long long z = 0; ; ++z) {
        long long p1 = z * (3 * z + 1) / 2;
        long long p2 = (-z) * (3 * (-z) + 1) / 2;
        bool added = false;
        if (z == 0) {
            if (p1 <= limit) { gp.push_back(p1); added = true; }
        } else {
            if (p2 <= limit) { gp.push_back(p2); added = true; }
            if (p1 <= limit) { gp.push_back(p1); added = true; }
        }
        if (!added) break;
    }
    sort(gp.begin(), gp.end());
    
    vector<int> a(limit + 1, 0);
    
    long long max_x = sqrt(limit) + 1;
    for (long long x = 0; x <= max_x; ++x) {
        long long x2 = x * x;
        if (x2 > limit) break;
        long long max_y = sqrt(limit - x2) + 1;
        for (long long y = x; y <= max_y; ++y) {
            long long s = x2 + y * y;
            if (s > limit) break;
            if ((x + 1 < is_prime.size() && is_prime[x + 1]) || 
                (y + 1 < is_prime.size() && is_prime[y + 1])) {
                for (long long p : gp) {
                    long long n = s + p;
                    if (n <= limit) {
                        if (a[n] < 2) a[n]++;
                    } else {
                        break;
                    }
                }
            }
        }
    }
    
    for (long long n = 1; n <= limit; ++n) {
        if (a[n] == 0) {
            cout << "Counterexample to a(n) > 0: " << n << endl;
        }
        if (a[n] == 1 && n != 1 && n != 49 && n != 608) {
            cout << "Counterexample to a(n) = 1: " << n << endl;
        }
    }
    cout << "Done up to " << limit << endl;
    return 0;
}
