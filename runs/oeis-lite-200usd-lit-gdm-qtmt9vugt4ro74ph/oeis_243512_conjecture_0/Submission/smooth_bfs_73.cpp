#include <iostream>
#include <vector>
#include <queue>
#include <algorithm>
#include <cmath>

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

struct Node {
    long long g;
    long long s;
    int last_idx;
    
    bool operator>(const Node& other) const {
        return g > other.g;
    }
};

const long long primes[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97};
const int NUM_PRIMES = 25;

struct Missing {
    int n;
    vector<int> divs;
};

int main() {
    long long LIMIT = 500000000000LL; // 500 billion (5 * 10^11)
    cout << "Starting smooth BFS search with 25 primes up to " << LIMIT << "..." << endl;
    
    vector<Missing> missing = {
        {1680, {23, 73, 1679}},
        {4488, {7, 641, 4487}}
    };
    
    vector<long long> found_i(5001, 0);
    int found_count = 0;
    
    priority_queue<Node, vector<Node>, greater<Node>> pq;
    pq.push({1, 1, 0});
    
    long long count = 0;
    
    while (!pq.empty()) {
        Node curr = pq.top();
        pq.pop();
        
        count++;
        if (count % 10000000 == 0) {
            cout << "Processed " << count << " smooth numbers, current g = " << curr.g << endl;
        }
        
        long long g = curr.g;
        long long s = curr.s;
        long long s_prime = s - g;
        
        if (s_prime > 0) {
            for (const auto& m : missing) {
                if (found_i[m.n] == 0) {
                    for (int d : m.divs) {
                        if (s_prime % d == 0) {
                            long long gc = s_prime / d;
                            if (g % gc == 0) {
                                if (gcd_calc(d, g / gc) == 1) {
                                    long long b = g / gc;
                                    long long a = s / gc;
                                    long long k = (m.n - 1) / d;
                                    u128 p = (u128)k * b - 1;
                                    if (p > 1 && g % p != 0 && gcd_calc(k * a, p) == 1 && miller_rabin(p)) {
                                        found_i[m.n] = g * p;
                                        found_count++;
                                        cout << "FOUND for " << m.n << ": g = " << g << ", p = " << (long long)p << ", i = " << (long long)(g * p) << endl;
                                        if (found_count == missing.size()) {
                                            cout << "All found!" << endl;
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
        
        for (int i = curr.last_idx; i < NUM_PRIMES; ++i) {
            long long p = primes[i];
            if (curr.g > LIMIT / p) continue;
            
            long long next_g = curr.g * p;
            long long temp = curr.g;
            long long pe = 1;
            while (temp % p == 0) {
                pe *= p;
                temp /= p;
            }
            long long next_s = curr.s * (pe * p * p - 1) / (pe * p - 1);
            
            pq.push({next_g, next_s, i});
        }
    }
    
    cout << "Finished BFS. Found " << found_count << "/" << missing.size() << endl;
    return 0;
}
