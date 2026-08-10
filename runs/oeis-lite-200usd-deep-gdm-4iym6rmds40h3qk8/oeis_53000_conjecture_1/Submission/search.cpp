#include <iostream>
#include <vector>
#include <cmath>
#include <numeric>

using namespace std;

const int MAX_N = 10000000;

int main() {
    cout << "Allocating memory..." << endl;
    vector<int> phi(MAX_N + 1);
    for (int i = 0; i <= MAX_N; ++i) phi[i] = i;
    for (int i = 2; i <= MAX_N; ++i) {
        if (phi[i] == i) {
            for (int j = i; j <= MAX_N; j += i) {
                phi[j] -= phi[j] / i;
            }
        }
    }
    cout << "Phi table computed." << endl;

    // We will check in chunks to avoid allocating a huge prime sieve
    const long long CHUNK_SIZE = 100000000; // 10^8
    cout << "Searching..." << endl;
    
    // We only need to find the next prime after n^2
    // Let's do a segment sieve for primes
    for (int n = 1; n <= MAX_N; ++n) {
        long long n2 = (long long)n * n;
        // Find next prime after n2
        // Since we expect the next prime to be very close, we can just test primality of n2+1, n2+2, ...
        long long p = n2 + 1;
        while (true) {
            bool is_prime = true;
            if (p < 2) is_prime = false;
            else {
                for (long long d = 2; d * d <= p; ++d) {
                    if (p % d == 0) {
                        is_prime = false;
                        break;
                    }
                }
            }
            if (is_prime) break;
            p++;
        }
        long long an = p - n2;
        long long limit = 1 + phi[n];
        if (an > limit) {
            cout << "COUNTEREXAMPLE FOUND: n=" << n << ", an=" << an << ", phi=" << phi[n] << endl;
            return 0;
        }
        if (n % 100000 == 0) {
            cout << "Checked up to n=" << n << endl;
        }
    }
    cout << "Finished search up to " << MAX_N << ", no counterexamples found." << endl;
    return 0;
}
