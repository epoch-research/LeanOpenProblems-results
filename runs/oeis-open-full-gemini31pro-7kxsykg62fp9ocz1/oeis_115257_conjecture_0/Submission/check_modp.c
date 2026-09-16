#include <flint/fmpz_poly.h>
#include <flint/nmod_poly.h>
#include <flint/fmpz.h>
#include <stdio.h>
#include <stdlib.h>

int is_prime(int p) {
    if (p < 2) return 0;
    for (int i = 2; i * i <= p; i++)
        if (p % i == 0) return 0;
    return 1;
}

int main() {
    fmpz_poly_t P, Q;
    fmpz_poly_init(P);
    fmpz_poly_init(Q);
    fmpz_t binom, term;
    fmpz_init(binom); fmpz_init(term);
    
    int primes[100];
    int num_primes = 0;
    for (int p = 2; p < 300; p++) {
        if (is_prime(p)) primes[num_primes++] = p;
    }
    
    for (int n = 1; n <= 1000; n++) {
        fmpz_poly_zero(P);
        fmpz_poly_zero(Q);
        fmpz_set_ui(binom, 1);
        fmpz_poly_set_coeff_fmpz(P, 0, binom);
        fmpz_poly_set_coeff_fmpz(Q, 0, binom);
        
        for (int k = 1; k <= n; k++) {
            fmpz_mul_ui(binom, binom, 2 * (2 * k - 1));
            fmpz_divexact_ui(binom, binom, k);
            fmpz_mul(term, binom, binom);
            fmpz_poly_set_coeff_fmpz(P, k, term);
            fmpz_divexact_ui(term, term, k + 1);
            fmpz_poly_set_coeff_fmpz(Q, k, term);
        }
        
        int p_irred = 0, q_irred = 0;
        for (int i = 0; i < num_primes; i++) {
            int p = primes[i];
            
            nmod_poly_t P_mod, Q_mod;
            nmod_poly_init(P_mod, p);
            nmod_poly_init(Q_mod, p);
            fmpz_poly_get_nmod_poly(P_mod, P);
            fmpz_poly_get_nmod_poly(Q_mod, Q);
            
            if (!p_irred && nmod_poly_degree(P_mod) == n) {
                if (nmod_poly_is_irreducible(P_mod)) p_irred = 1;
            }
            if (!q_irred && nmod_poly_degree(Q_mod) == n) {
                if (nmod_poly_is_irreducible(Q_mod)) q_irred = 1;
            }
            
            nmod_poly_clear(P_mod);
            nmod_poly_clear(Q_mod);
            if (p_irred && q_irred) break;
        }
        
        if (!p_irred) printf("P_%d is reducible mod all p < 300\n", n);
        if (!q_irred) printf("Q_%d is reducible mod all p < 300\n", n);
    }
    return 0;
}
