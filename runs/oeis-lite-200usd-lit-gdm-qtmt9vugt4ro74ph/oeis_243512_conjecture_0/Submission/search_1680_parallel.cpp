#include <iostream>
#include <vector>
#include <numeric>
#include <cmath>
#include <algorithm>
#include <omp.h>

using namespace std;

const long long LIMIT = 100000000000LL; // 100 billion
const int BLOCK_SIZE = 40000000; // 40 million

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

struct MissingInfo {
    int n;
    vector<int> divs;
};

int main() {
    int num_threads = omp_get_max_threads();
    cout << "Superfast parallel search up to " << LIMIT << " using " << num_threads << " threads..." << endl;
    
    vector<MissingInfo> missing = {
        {1680, {23, 73, 1679}},
        {4488, {7, 641, 4487}}
    };
    
    vector<int> all_divs = {7, 23, 73, 641, 1679, 4487};
    sort(all_divs.begin(), all_divs.end());
    
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
                
                // Fast filtering using divisors
                for (int d : all_divs) {
                    if (s_prime % d == 0) {
                        long long gc = s_prime / d;
                        if (g % gc == 0) {
                            if (gcd_calc(d, g / gc) == 1) {
                                long long b = g / gc;
                                long long a = s / gc;
                                for (const auto& mi : missing) {
                                    if (find(mi.divs.begin(), mi.divs.end(), d) != mi.divs.end()) {
                                        long long k = (mi.n - 1) / d;
                                        long long p = k * b - 1;
                                        if (p > 1 && g % p != 0 && gcd_calc(k * a, p) == 1 && is_prime(p)) {
                                            #pragma omp critical
                                            {
                                                cout << "FOUND for " << mi.n << ": g = " << g << ", p = " << p << ", i = " << g * p << endl;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            
            int tid = omp_get_thread_num();
            if (tid == 0 && (start / BLOCK_SIZE) % 50 == 0) {
                cout << "Thread 0 processed up to " << start << endl;
            }
        }
    }
    
    cout << "Finished parallel search." << endl;
    return 0;
}
