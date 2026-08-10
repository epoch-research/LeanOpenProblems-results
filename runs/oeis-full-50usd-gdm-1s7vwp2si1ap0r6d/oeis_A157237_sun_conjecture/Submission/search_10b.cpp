#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include <chrono>

using namespace std;

const int KNOWN_ZEROS[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 18, 21, 24, 51, 84, 1011, 59586};
bool is_known_zero(int n) {
    for (int z : KNOWN_ZEROS) {
        if (n == z) return true;
    }
    return false;
}

int main() {
    auto t0 = chrono::high_resolution_clock::now();
    
    long long limit = 10000000000LL; // 10 billion
    long long max_N = 2 * limit;
    
    cout << "Allocating sieve for " << max_N << " elements..." << endl;
    // To save memory, we can use a segmented sieve or just a vector<bool> if memory permits.
    // 20 billion bools in vector<bool> takes 20 billion bits = 2.5 GB. This is perfectly fine!
    vector<bool> is_prime(max_N, true);
    is_prime[0] = is_prime[1] = false;
    for (long long i = 2; i * i < max_N; ++i) {
        if (is_prime[i]) {
            for (long long j = i * i; j < max_N; j += i) {
                is_prime[j] = false;
            }
        }
    }
    
    cout << "Primes sieved. Finding primes congruent to 1 mod 6..." << endl;
    vector<long long> primes;
    for (long long i = 7; i < max_N; i += 6) {
        if (is_prime[i]) {
            primes.push_back(i);
        }
    }
    cout << "Found " << primes.size() << " primes congruent to 1 mod 6." << endl;
    
    // Free the large is_prime vector
    is_prime.clear();
    is_prime.shrink_to_fit();
    
    cout << "Allocating representation tracker..." << endl;
    // 10 billion bits = 1.25 GB
    vector<bool> has_rep(limit + 1, false);
    
    cout << "Computing representations..." << endl;
    for (int x = 1; ; ++x) {
        long long p2x = 1LL << x;
        if (p2x >= max_N) break;
        for (int y = 1; ; ++y) {
            long long S = p2x + 11LL * (1LL << y);
            if (S >= max_N) break;
            
            long long max_p = max_N - S;
            auto it = lower_bound(primes.begin(), primes.end(), max_p);
            long long idx = distance(primes.begin(), it);
            for (long long i = 0; i < idx; ++i) {
                long long N = primes[i] + S;
                long long n = (N + 1) / 2;
                if (n <= limit) {
                    has_rep[n] = true;
                }
            }
        }
    }
    
    cout << "Checking for zeros..." << endl;
    for (long long n = 1; n <= limit; ++n) {
        if (!has_rep[n]) {
            if (!is_known_zero(n)) {
                cout << "COUNTEREXAMPLE FOUND: n = " << n << endl;
            }
        }
    }
    
    auto t1 = chrono::high_resolution_clock::now();
    cout << "Total time: " << chrono::duration_cast<chrono::seconds>(t1 - t0).count() << " seconds." << endl;
    return 0;
}
