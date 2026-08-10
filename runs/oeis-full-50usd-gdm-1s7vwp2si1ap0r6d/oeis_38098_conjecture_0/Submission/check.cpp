#include <iostream>
#include <vector>
#include <cmath>

using namespace std;

int main() {
    // We want to check k=3 up to n=100000.
    // (n+1)^3 for n=100000 is 100001^3 = 10^15, which is too large for a simple sieve.
    // But we can check up to where we can.
    // Let's do a sieve up to 10^9, which allows checking n up to 1000 for k=3.
    // For n up to 1000, 1000^3 = 10^9.
    long long limit = 1000000000LL; // 10^9
    cout << "Allocating sieve up to " << limit << "..." << endl;
    vector<bool> is_prime(limit + 1, true);
    is_prime[0] = is_prime[1] = false;
    for (long long p = 2; p * p <= limit; ++p) {
        if (is_prime[p]) {
            for (long long i = p * p; i <= limit; i += p) {
                is_prime[i] = false;
            }
        }
    }
    cout << "Sieve completed." << endl;

    // Now compute prefix sums of primes (primeCounting)
    // To save memory, we can compute primeCounting on the fly or keep a smaller array.
    // Since we only need primeCounting at n^k and (n+1)^k, let's just do a single pass over the sieve
    // and record the values of primeCounting at the required points.
    // For k=3, the points are n^3 for n=2, 3, ..., 1000.
    vector<long long> targets;
    for (long long n = 2; n <= 1000; ++n) {
        targets.push_back(n * n * n);
    }
    // Sort targets (they are already sorted)
    vector<long long> pi_vals(targets.size(), 0);
    long long count = 0;
    size_t target_idx = 0;
    for (long long i = 0; i <= limit; ++i) {
        if (is_prime[i]) {
            count++;
        }
        while (target_idx < targets.size() && targets[target_idx] == i) {
            pi_vals[target_idx] = count;
            target_idx++;
        }
    }

    // Now check the inequality for k=3
    for (size_t i = 0; i < targets.size() - 1; ++i) {
        long long n = i + 2;
        long long pi_n3 = pi_vals[i];
        long long pi_np13 = pi_vals[i+1];
        // We want to check if pi_n3 / n^3 > pi_np13 / (n+1)^3
        // i.e., pi_n3 * (n+1)^3 > pi_np13 * n^3
        double val1 = (double)pi_n3 / (n * n * n);
        double val2 = (double)pi_np13 / ((n+1) * (n+1) * (n+1));
        if (val1 <= val2) {
            cout << "Counterexample found for k=3, n=" << n << endl;
            cout << "pi(n^3) = " << pi_n3 << ", pi((n+1)^3) = " << pi_np13 << endl;
            return 0;
        }
    }
    cout << "No counterexample for k=3, n up to 999" << endl;
    return 0;
}
