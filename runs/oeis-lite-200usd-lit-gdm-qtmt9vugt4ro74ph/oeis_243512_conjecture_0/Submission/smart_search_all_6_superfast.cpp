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

struct MissingInfo {
    int n;
    vector<int> divs;
};

int main() {
    cout << "Superfast search for missing numbers up to " << LIMIT << " using block sieve..." << endl;
    
    // We only care about n in our missing list and their divisors > 1
    vector<MissingInfo> missing = {
        {1680, {23, 73, 1679}},
        {2226, {5, 25, 89, 445, 2225}},
        {3432, {47, 73, 3431}},
        {3570, {43, 83, 3569}},
        {3744, {19, 197, 3743}},
        {4488, {7, 641, 4487}}
    };
    
    // All unique divisors > 1
    vector<int> all_divs = {5, 7, 19, 23, 25, 43, 47, 73, 83, 89, 197, 445, 641, 1679, 2225, 3431, 3569, 3743, 4487};
    // Sort descending so we check larger ones (less likely to divide s_prime) first, or ascending?
    // Actually, checking larger ones is faster if we want to rule them out, but s_prime is often small.
    // Let's just keep them sorted.
    sort(all_divs.begin(), all_divs.end());
    
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
            
            long long s_prime = s - g;
            if (s_prime <= 0) continue;
            
            // Fast filtering using divisors
            for (int d : all_divs) {
                if (s_prime % d == 0) {
                    long long gc = s_prime / d;
                    if (g % gc == 0) {
                        // Double check with gcd to be 100% mathematically correct
                        if (gcd_calc(d, g / gc) == 1) {
                            long long b = g / gc;
                            long long a = s / gc;
                            // Now find which missing n this d belongs to
                            for (const auto& mi : missing) {
                                if (found_i[mi.n] == 0) {
                                    if (find(mi.divs.begin(), mi.divs.end(), d) != mi.divs.end()) {
                                        long long k = (mi.n - 1) / d;
                                        long long p = k * b - 1;
                                        if (p > 1 && g % p != 0 && gcd_calc(k * a, p) == 1 && is_prime(p)) {
                                            found_i[mi.n] = g * p;
                                            found_count++;
                                            cout << "FOUND for " << mi.n << ": g = " << g << ", p = " << p << ", i = " << g * p << endl;
                                            if (found_count == missing.size()) {
                                                cout << "All missing found!" << endl;
                                                return 0;
                                            }
                                        }
                                    }
                                }
                            }
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
