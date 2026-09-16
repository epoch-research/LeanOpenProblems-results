#include <flint/fmpz_poly.h>
#include <flint/nmod_poly.h>
#include <flint/fmpz.h>
#include <stdio.h>

int is_prime(int p) {
    if (p < 2) return 0;
    for (int i = 2; i * i <= p; i++)
        if (p % i == 0) return 0;
    return 1;
}

int main() {
    fmpz_poly_t P; fmpz_poly_init(P);
    fmpz_t binom, term; fmpz_init(binom); fmpz_init(term);
    
    int n = 31;
    fmpz_poly_zero(P);
    fmpz_set_ui(binom, 1);
    fmpz_poly_set_coeff_fmpz(P, 0, binom);
    
    for (int k = 1; k <= n; k++) {
        fmpz_mul_ui(binom, binom, 2 * (2 * k - 1));
        fmpz_divexact_ui(binom, binom, k);
        fmpz_mul(term, binom, binom);
        fmpz_poly_set_coeff_fmpz(P, k, term);
    }
    
    for (int p = 2; p < 10000; p++) {
        if (!is_prime(p)) continue;
        nmod_poly_t P_mod;
        nmod_poly_init(P_mod, p);
        fmpz_poly_get_nmod_poly(P_mod, P);
        if (nmod_poly_degree(P_mod) == n && nmod_poly_is_irreducible(P_mod)) {
            printf("P_31 is irreducible mod %d\n", p);
            return 0;
        }
        nmod_poly_clear(P_mod);
    }
    printf("P_31 is reducible mod all p < 10000\n");
    return 0;
}
