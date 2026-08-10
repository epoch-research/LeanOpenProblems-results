#include <iostream>
#include <vector>
#include <chrono>
#include <gmp.h>
#include <gmpxx.h>

using namespace std;

int main() {
    int LIMIT = 150000;
    vector<bool> is_prime(LIMIT, true);
    is_prime[0] = is_prime[1] = false;
    for (int i = 2; i * i < LIMIT; ++i) {
        if (is_prime[i]) {
            for (int j = i * i; j < LIMIT; j += i) {
                is_prime[j] = false;
            }
        }
    }

    mpz_class L = 1;
    mpz_class an = 0;
    mpz_class g, term1, term2, n_mpz, pow2;

    auto start = chrono::high_resolution_clock::now();

    for (int n = 2; n < LIMIT; ++n) {
        n_mpz = n;
        mpz_gcd(g.get_mpz_t(), L.get_mpz_t(), n_mpz.get_mpz_t());

        term1 = (n_mpz / g) * an;

        mpz_ui_pow_ui(pow2.get_mpz_t(), 2, n - 1);
        pow2 -= 1;
        term2 = (L / g) * pow2;

        an = term1 + term2;
        L = (L * n_mpz) / g;

        if (n > 3 && !is_prime[n]) {
            mpz_class n3 = n_mpz * n_mpz * n_mpz;
            mpz_class rem;
            mpz_mod(rem.get_mpz_t(), an.get_mpz_t(), n3.get_mpz_t());
            if (rem == 0) {
                cout << "FOUND COUNTEREXAMPLE: n = " << n << endl;
                break;
            }
        }

        if (n % 20000 == 0) {
            auto end = chrono::high_resolution_clock::now();
            chrono::duration<double> elapsed = end - start;
            cout << "Processed up to n = " << n << " in " << elapsed.count() << " s" << endl;
        }
    }
    cout << "Finished!" << endl;
    return 0;
}
