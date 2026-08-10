#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>

using namespace std;

int main() {
    long long limit = 200000000000LL; // 2 * 10^11
    cout << "Checking all k>=3, n>=2 with (n+1)^k <= " << limit << endl;

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

    // We want to find pi(n^k) for all n, k of interest.
    // Let's gather all targets.
    struct Target {
        long long val;
        int k;
        int n;
        long long pi;
    };
    vector<Target> targets;
    for (int k = 3; k <= 35; ++k) {
        for (int n = 2; ; ++n) {
            long long val1 = 1;
            bool overflow = false;
            for (int i = 0; i < k; ++i) {
                if (val1 > limit / n) {
                    overflow = true;
                    break;
                }
                val1 *= n;
            }
            if (overflow) break;
            targets.push_back({val1, k, n, 0});
        }
    }

    // Sort targets by value
    sort(targets.begin(), targets.end(), [](const Target& a, const Target& b) {
        return a.val < b.val;
    });

    cout << "Number of targets: " << targets.size() << endl;

    long long segment_size = 10000000; // 10M
    vector<bool> segment(segment_size);

    long long pi_count = 0;
    size_t target_idx = 0;

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
            while (target_idx < targets.size() && targets[target_idx].val == i) {
                targets[target_idx].pi = pi_count;
                target_idx++;
            }
        }
    }

    cout << "Sieve completed. Checking conjecture..." << endl;
    // We want to check if for any k, n:
    // pi(n^k) / n^k <= pi((n+1)^k) / (n+1)^k
    // Let's build a map/lookup for pi(n^k)
    // Since targets is sorted by value, we can just find the targets for n^k and (n+1)^k.
    auto find_target = [&](int k, int n) -> long long {
        long long val = 1;
        for (int i = 0; i < k; ++i) val *= n;
        for (const auto& t : targets) {
            if (t.k == k && t.n == n) {
                return t.pi;
            }
        }
        return -1;
    };

    for (int k = 3; k <= 35; ++k) {
        for (int n = 2; ; ++n) {
            long long val_n = 1;
            bool overflow = false;
            for (int i = 0; i < k; ++i) {
                if (val_n > limit / n) { overflow = true; break; }
                val_n *= n;
            }
            if (overflow) break;

            long long val_np1 = 1;
            for (int i = 0; i < k; ++i) {
                if (val_np1 > limit / (n+1)) { overflow = true; break; }
                val_np1 *= (n+1);
            }
            if (overflow) break;

            long long pi_n = find_target(k, n);
            long long pi_np1 = find_target(k, n+1);

            if (pi_n == -1 || pi_np1 == -1) continue;

            __int128 lhs = (__int128)pi_n * val_np1;
            __int128 rhs = (__int128)pi_np1 * val_n;

            if (lhs <= rhs) {
                cout << "COUNTEREXAMPLE FOUND!" << endl;
                cout << "k=" << k << ", n=" << n << endl;
                cout << "n^k=" << val_n << ", pi=" << pi_n << ", ratio=" << (double)pi_n/val_n << endl;
                cout << "(n+1)^k=" << val_np1 << ", pi=" << pi_np1 << ", ratio=" << (double)pi_np1/val_np1 << endl;
                return 0;
            }
        }
    }

    cout << "No counterexamples found under the limit!" << endl;
    return 0;
}
