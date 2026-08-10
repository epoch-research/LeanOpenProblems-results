#include <iostream>
#include <vector>
#include <numeric>
#include <cmath>
#include <algorithm>

using namespace std;

const long long LIMIT = 10000000000LL; // 10 billion
const int BLOCK_SIZE = 20000000; // 20 million

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

int main() {
    cout << "Optimized search for missing numbers up to " << LIMIT << " using block sieve..." << endl;
    
    vector<int> missing = {1680, 2226, 3432, 3570, 3744, 4488};
    vector<long long> found_i(5001, 0);
    int found_count = 0;
    
    vector<long long> sig(BLOCK_SIZE);
    
    for (long long start = 1; start < LIMIT; start += BLOCK_SIZE) {
        long long end = min(start + BLOCK_SIZE, LIMIT);
        long long sieve_limit = (end - 1) / 2;
        
        // Initialize sieve block to 1
        fill(sig.begin(), sig.begin() + (end - start), 1);
        
        // Sieve for divisors up to sieve_limit
        for (long long d = 2; d <= sieve_limit; ++d) {
            long long first = ((start + d - 1) / d) * d;
            if (first < start) first += d;
            for (long long j = first; j < end; j += d) {
                sig[j - start] += d;
            }
        }
        
        // Check candidates in the block
        for (long long g = start; g < end; ++g) {
            long long s = sig[g - start];
            if (g > sieve_limit) {
                s += g;
            }
            
            long long gc = gcd_calc(s, g);
            long long val = (s - g) / gc;
            long long b = g / gc;
            long long a = s / gc;
            
            for (int n : missing) {
                if (found_i[n] == 0 && val > 0 && (n - 1) % val == 0) {
                    long long k = (n - 1) / val;
                    long long p = k * b - 1;
                    if (p > 1 && g % p != 0 && gcd_calc(k * a, p) == 1 && is_prime(p)) {
                        found_i[n] = g * p;
                        found_count++;
                        cout << "FOUND for " << n << ": g = " << g << ", p = " << p << ", i = " << g * p << endl;
                        if (found_count == missing.size()) {
                            cout << "All missing found!" << endl;
                            return 0;
                        }
                    }
                }
            }
        }
        if (start % (BLOCK_SIZE * 5) == 1) {
            cout << "Processed up to " << start << endl;
        }
    }
    
    cout << "Finished. Found: " << found_count << "/" << missing.size() << endl;
    return 0;
}
