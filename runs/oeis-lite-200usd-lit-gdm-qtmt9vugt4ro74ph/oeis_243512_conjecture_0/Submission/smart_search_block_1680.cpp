#include <iostream>
#include <vector>
#include <numeric>
#include <cmath>

using namespace std;

const long long LIMIT = 500000000LL; // 5 * 10^8
const int BLOCK_SIZE = 10000000; // 10 million

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
    cout << "Searching for 1680 up to " << LIMIT << " using block sieve..." << endl;
    
    // sig[i] will store sum of divisors for i in the current block
    // sig_block[i] corresponds to g = start + i
    vector<long long> sig(BLOCK_SIZE);
    
    for (long long start = 1; start < LIMIT; start += BLOCK_SIZE) {
        long long end = min(start + BLOCK_SIZE, LIMIT);
        
        // Initialize sieve for the current block
        // Every number i has divisor 1 (and itself, but we add that on the fly)
        for (int i = 0; i < BLOCK_SIZE; ++i) {
            sig[i] = 1;
        }
        
        // Sieve for divisors up to end
        for (long long d = 2; d < end; ++d) {
            long long first = ((start + d - 1) / d) * d;
            if (first < start) first += d;
            for (long long j = first; j < end; j += d) {
                sig[j - start] += d;
            }
        }
        
        // Check candidates in the block
        for (long long g = start; g < end; ++g) {
            long long s = sig[g - start];
            long long gc = gcd_calc(s, g);
            long long val = (s - g) / gc;
            long long b = g / gc;
            long long a = s / gc;
            
            if (val > 0 && 1679 % val == 0) {
                long long k = 1679 / val;
                long long p = k * b - 1;
                if (p > 1 && g % p != 0 && gcd_calc(k * a, p) == 1 && is_prime(p)) {
                    cout << "Found for 1680: g = " << g << ", p = " << p << ", i = " << (long long)g * p << endl;
                    return 0;
                }
            }
        }
    }
    cout << "No Case 1 preimage found for 1680." << endl;
    return 0;
}
