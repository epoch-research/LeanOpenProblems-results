#include <iostream>
#include <vector>

using namespace std;

int main() {
    int N = 1000000;
    vector<int> A(N + 1, 0);
    // This is slow, O(N^2). We can compute A(n) much faster using prime factorization!
    // But wait, it's just A(p^k).
    vector<int> min_prime(N + 1, 0);
    for (int i = 2; i <= N; ++i) {
        if (min_prime[i] == 0) {
            for (int j = i; j <= N; j += i) {
                if (min_prime[j] == 0) min_prime[j] = i;
            }
        }
    }
    
    A[1] = 1;
    for (int i = 2; i <= N; ++i) {
        int p = min_prime[i];
        int k = 0, temp = i, pk = 1;
        while (temp % p == 0) {
            temp /= p;
            k++;
            pk *= p;
        }
        if (temp == 1) { // i = p^k
            if (p == 2) {
                if (k == 1) A[i] = 2;
                else if (k == 2) A[i] = 2;
                else A[i] = (1 << (k - 3)) + A[i/4]; // wait, what is the recurrence?
                // actually, for 2^k, A(2^k) is known.
            } else {
                if (k == 1) A[i] = (p + 1) / 2;
                else A[i] = (pk - (pk / p)) / 2 + A[i / (p * p)];
            }
        } else {
            A[i] = A[pk] * A[temp];
        }
    }
    
    for (long long n = 2; n <= N; ++n) {
        if (min_prime[n] == n) continue; // skip primes
        long long a = A[n];
        long long M = a * (a - 1);
        if (M == 0) continue;
        if ((n * n - 1) % M == 0) {
            cout << "Match: " << n << endl;
        }
    }
    cout << "Done" << endl;
    return 0;
}
