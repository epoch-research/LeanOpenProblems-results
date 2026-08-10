#include <iostream>
#include <vector>
#include <numeric>
#include <cmath>
#include <algorithm>
#include <omp.h>

using namespace std;

typedef unsigned __int128 u128;

u128 power(u128 base, u128 exp, u128 mod) {
    u128 res = 1;
    base %= mod;
    while (exp > 0) {
        if (exp % 2 == 1) res = (res * base) % mod;
        base = (base * base) % mod;
        exp /= 2;
    }
    return res;
}

bool miller_rabin(u128 n) {
    if (n < 2) return false;
    if (n == 2 || n == 3) return true;
    if (n % 2 == 0) return false;
    u128 d = n - 1;
    int s = 0;
    while (d % 2 == 0) {
        d /= 2;
        s++;
    }
    static const u128 bases[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47};
    for (u128 a : bases) {
        if (n <= a) break;
        u128 x = power(a, d, n);
        if (x == 1 || x == n - 1) continue;
        bool composite = true;
        for (int r = 1; r < s; r++) {
            x = (x * x) % n;
            if (x == n - 1) {
                composite = false;
                break;
            }
        }
        if (composite) return false;
    }
    return true;
}

long long gcd_calc(long long a, long long b) {
    return b == 0 ? a : gcd_calc(b, a % b);
}

const long long primes[] = {
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 
    211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 
    337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 
    461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541
};
const int num_primes = 100;

const long long LIMIT = 1000000000000000LL; // 1 quadrillion

struct State {
    int prime_idx;
    long long g;
    long long s;
    int num_distinct;
};

vector<State> initial_states;

void generate_initial_states(int prime_idx, long long current_g, long long current_s, int num_distinct) {
    if (num_distinct > 5) return;
    
    if (prime_idx == 5) {
        initial_states.push_back({prime_idx, current_g, current_s, num_distinct});
        return;
    }
    
    // Branch 1: do not use primes[prime_idx]
    generate_initial_states(prime_idx + 1, current_g, current_s, num_distinct);
    
    // Branch 2: use powers of primes[prime_idx]
    long long p = primes[prime_idx];
    long long next_g = current_g;
    long long next_s = current_s;
    long long pk = 1;
    long long sum_pk = 1;
    while (true) {
        if (next_g > LIMIT / p) break;
        next_g *= p;
        pk *= p;
        sum_pk += pk;
        generate_initial_states(prime_idx + 1, next_g, next_s * sum_pk, num_distinct + 1);
    }
}

long long processed_states = 0;

void dfs(int prime_idx, long long current_g, long long current_s, int num_distinct) {
    if (num_distinct > 5) return;
    
    // no atomic
    // processed_states++;
    
    long long s_prime = current_s - current_g;
    if (s_prime > 0) {
        long long gc = gcd_calc(s_prime, current_g);
        long long val = s_prime / gc;
        if (1679 % val == 0) {
            long long k = 1679 / val;
            long long b = current_g / gc;
            u128 p = (u128)k * b - 1;
            if (p > 1 && current_g % p != 0 && miller_rabin(p)) {
                long long a = current_s / gc;
                if (gcd_calc(k * a, p) == 1) {
                    #pragma omp critical
                    {
                        cout << "FOUND! g = " << current_g << ", p = " << (long long)p << ", i = " << (long long)(current_g * p) << endl;
                        exit(0);
                    }
                }
            }
        }
    }

    for (int i = prime_idx; i < num_primes; ++i) {
        long long p = primes[i];
        if (current_g > LIMIT / p) continue;
        
        long long next_g = current_g;
        long long next_s = current_s;
        long long pk = 1;
        long long sum_pk = 1;
        while (true) {
            if (next_g > LIMIT / p) break;
            next_g *= p;
            pk *= p;
            sum_pk += pk;
            dfs(i + 1, next_g, next_s * sum_pk, num_distinct + 1);
        }
    }
}

int main() {
    int num_threads = omp_get_max_threads();
    cout << "Generating initial states with first 5 primes..." << endl;
    generate_initial_states(0, 1, 1, 0);
    cout << "Generated " << initial_states.size() << " initial states." << endl;
    
    cout << "Starting parallel DFS up to " << LIMIT << " (num_distinct <= 7) using " << num_threads << " threads..." << endl;
    
    #pragma omp parallel for schedule(dynamic)
    for (size_t i = 0; i < initial_states.size(); ++i) {
        dfs(initial_states[i].prime_idx, initial_states[i].g, initial_states[i].s, initial_states[i].num_distinct);
    }
    
    cout << "DFS complete. No preimage found." << endl;
    return 0;
}
