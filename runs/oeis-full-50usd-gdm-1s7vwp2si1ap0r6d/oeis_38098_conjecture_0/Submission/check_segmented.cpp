#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>

using namespace std;

int main() {
    long long max_n = 3000;
    long long limit = max_n * max_n * max_n;
    cout << "Checking k=3 up to n=" << max_n << " (limit=" << limit << ")" << endl;

    // We want to find pi(n^3) for all n <= max_n.
    vector<long long> targets(max_n + 1);
    for (long long n = 0; n <= max_n; ++n) {
        targets[n] = n * n * n;
    }

    vector<long long> pi_vals(max_n + 1, 0);

    // Segmented Sieve
    long long sqrt_limit = sqrt(limit) + 1;
    vector<bool> is_prime_small(sqrt_limit + 1, true);
    is_prime_small[0] = is_prime_small[1] = false;
    for (long long p = 2; p * p <= sqrt_limit; ++p) {
        if (is_prime_small[p]) {
            for (long long i = p * p; i <= sqrt_limit; i += p) {
                is_prime_small[i] = false;
            }
        }
    }

    vector<long long> primes;
    for (long long p = 2; p <= sqrt_limit; ++p) {
        if (is_prime_small[p]) {
            primes.push_back(p);
        }
    }
    cout << "Number of small primes: " << primes.size() << endl;

    long long segment_size = 10000000; // 10M
    vector<bool> segment(segment_size);

    long long pi_count = 0;
    long long target_idx = 2; // Start from 2^3 = 8

    for (long long low = 0; low <= limit; low += segment_size) {
        long long high = min(low + segment_size - 1, limit);
        fill(segment.begin(), segment.end(), true);

        if (low == 0) {
            segment[0] = segment[1] = false;
        }

        for (long long p : primes) {
            if (p * p > high) break;
            long long start = (low + p - 1) / p * p;
            if (start < p * p) start = p * p;
            for (long long i = start; i <= high; i += p) {
                segment[i - low] = false;
            }
        }

        for (long long i = low; i <= high; ++i) {
            if (segment[i - low]) {
                pi_count++;
            }
            while (target_idx <= max_n && targets[target_idx] == i) {
                pi_vals[target_idx] = pi_count;
                target_idx++;
            }
        }

        if (low % 1000000000 == 0 && low > 0) {
            cout << "Processed up to " << low << "..." << endl;
        }
    }

    cout << "Sieve completed. Checking conjecture..." << endl;
    for (long long n = 2; n < max_n; ++n) {
        long long pi_n3 = pi_vals[n];
        long long pi_np13 = pi_vals[n+1];
        
        // Check if pi(n^3) / n^3 <= pi((n+1)^3) / (n+1)^3
        // pi_n3 * (n+1)^3 <= pi_np13 * n^3
        __int128 lhs = (__int128)pi_n3 * (n+1) * (n+1) * (n+1);
        __int128 rhs = (__int128)pi_np13 * n * n * n;
        if (lhs <= rhs) {
            cout << "COUNTEREXAMPLE FOUND!" << endl;
            cout << "k=3, n=" << n << endl;
            cout << "pi(n^3) = " << pi_n3 << ", ratio = " << (double)pi_n3 / (n*n*n) << endl;
            cout << "pi((n+1)^3) = " << pi_np13 << ", ratio = " << (double)pi_np13 / ((n+1)*(n+1)*(n+1)) << endl;
            return 0;
        }
    }

    cout << "No counterexamples found up to n=" << max_n - 1 << endl;
    return 0;
}
