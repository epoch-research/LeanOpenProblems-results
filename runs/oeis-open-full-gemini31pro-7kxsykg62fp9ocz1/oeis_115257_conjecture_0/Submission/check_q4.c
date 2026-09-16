#include <flint/fmpz_poly.h>
#include <flint/fmpz_poly_factor.h>
#include <flint/fmpz.h>
#include <stdio.h>
#include <stdlib.h>

int main() {
    fmpz_poly_t P, Q;
    fmpz_poly_init(P);
    fmpz_poly_init(Q);
    fmpz_t binom, term;
    fmpz_init(binom); fmpz_init(term);
    fmpz_poly_factor_t fac;
    fmpz_poly_factor_init(fac);
    
    for (int n = 800; n <= 3000; n++) {
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
        
        fmpz_poly_factor(fac, P);
        if (fac->num > 1) { printf("P_%d is reducible!\n", n); exit(0); }
        fmpz_poly_factor(fac, Q);
        if (fac->num > 1) { printf("Q_%d is reducible!\n", n); exit(0); }
        if (n % 100 == 0) { printf("Checked %d\n", n); fflush(stdout); }
    }
    return 0;
}
