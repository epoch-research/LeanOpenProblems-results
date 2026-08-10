#include <iostream>
#include <vector>
#include <numeric>
#include <cmath>
#include <algorithm>
#include <omp.h>

using namespace std;

const long long LIMIT = 5000000000LL; // 5 billion
const int BLOCK_SIZE = 5000000; // 5 million

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
    int num_threads = omp_get_max_threads();
    cout << "Superfast parallel search for 630 up to " << LIMIT << " using " << num_threads << " threads..." << endl;
    
    // Divisors of 629 are 17, 37
    vector<int> divs = {17, 37};
    
    #pragma omp parallel
    {
        vector<long long> sig(BLOCK_SIZE);
        
        #pragma omp for schedule(dynamic, 1)
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
                
                long long s_prime = s - g;
                if (s_prime <= 0) continue;
                
                for (int d : divs) {
                    if (s_prime % d == 0) {
                        long long gc = s_prime / d;
                        if (g % gc == 0) {
                            if (gcd_calc(d, g / gc) == 1) {
                                long long b = g / gc;
                                long long a = s / gc;
                                long long k = 629 / d;
                                long long p = k * b - 1;
                                if (p > 1 && g % p != 0 && gcd_calc(k * a, p) == 1 && is_prime(p)) {
                                    #pragma omp critical
                                    {
                                        cout << "FOUND for 630: g = " << g << ", p = " << p << ", i = " << g * p << endl;
                                        exit(0);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            
            int tid = omp_get_thread_num();
            if (tid == 0 && (start / BLOCK_SIZE) % 100 == 0) {
                cout << "Thread 0 processed up to " << start << endl;
            }
        }
    }
    
    cout << "Finished parallel search." << endl;
    return 0;
}
