#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>

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
    static const u128 bases[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
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

const int MAX_G = 150000000; // 150 million
int spf[MAX_G];
long long sig[MAX_G];

// Find all divisors of a number using its prime factorization
void get_divisors(int x, vector<int>& divs) {
    divs.clear();
    divs.push_back(1);
    while (x > 1) {
        int p = spf[x];
        int count = 0;
        while (x % p == 0) {
            count++;
            x /= p;
        }
        int sz = divs.size();
        int pk = 1;
        for (int i = 1; i <= count; i++) {
            pk *= p;
            for (int j = 0; j < sz; j++) {
                divs.push_back(divs[j] * pk);
            }
        }
    }
}

int main() {
    cout << "Initializing Sieve..." << endl;
    vector<int> primes;
    sig[1] = 1;
    for (int i = 2; i < MAX_G; i++) {
        if (spf[i] == 0) {
            spf[i] = i;
            primes.push_back(i);
            sig[i] = i + 1;
        }
        for (int p : primes) {
            if (p > spf[i] || i * p >= MAX_G) break;
            spf[i * p] = p;
        }
    }
    
    // Compute sigma using SPF
    cout << "Computing Sigma..." << endl;
    for (int i = 2; i < MAX_G; i++) {
        int p = spf[i];
        int temp = i;
        long long pk = 1;
        long long sum_pk = 1;
        while (temp % p == 0) {
            pk *= p;
            sum_pk += pk;
            temp /= p;
        }
        sig[i] = sig[temp] * sum_pk;
    }
    
    cout << "Searching..." << endl;
    vector<int> divs;
    for (int g = 2; g < MAX_G; g++) {
        long long s_g = sig[g] - g;
        if (s_g == 0) continue;
        
        get_divisors(g, divs);
        for (int d : divs) {
            long long m = g / d;
            if (1680 - m > 0) {
                long long num = (1680 - m) * d;
                if (num % s_g == 0) {
                    long long p = num / s_g - 1;
                    if (p > 1 && miller_rabin(p)) {
                        if (gcd_calc(g, p) == 1) {
                            long long val_check = sig[g] * (1680 - m) / s_g;
                            if (gcd_calc(val_check, m) == 1) {
                                cout << "FOUND preimage for 1680! g = " << g << ", p = " << p << ", i = " << g * p << endl;
                                return 0;
                            }
                        }
                    }
                }
            }
        }
        if (g % 10000000 == 0) {
            cout << "Processed " << g << endl;
        }
    }
    cout << "Finished up to " << MAX_G << endl;
    return 0;
}
