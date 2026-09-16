#include <flint/fmpz_poly.h>
#include <stdio.h>

int main() {
    fmpz_poly_t P; fmpz_poly_init(P);
    fmpz_t binom, term; fmpz_init(binom); fmpz_init(term);
    
    int n = 4;
    fmpz_poly_zero(P);
    fmpz_set_ui(binom, 1);
    fmpz_poly_set_coeff_fmpz(P, 0, binom);
    
    for (int k = 1; k <= n; k++) {
        fmpz_mul_ui(binom, binom, 2 * (2 * k - 1));
        fmpz_divexact_ui(binom, binom, k);
        fmpz_mul(term, binom, binom);
        fmpz_poly_set_coeff_fmpz(P, k, term);
    }
    
    fmpz_poly_print(P);
    printf("\n");
    return 0;
}
