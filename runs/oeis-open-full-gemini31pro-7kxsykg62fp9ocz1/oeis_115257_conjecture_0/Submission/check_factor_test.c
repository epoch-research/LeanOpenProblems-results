#include <flint/fmpz_poly.h>
#include <flint/fmpz_poly_factor.h>
#include <stdio.h>

int main() {
    fmpz_poly_t P;
    fmpz_poly_init(P);
    
    // P = (2x+1)(3x+1) = 6x^2 + 5x + 1
    fmpz_poly_set_coeff_ui(P, 0, 1);
    fmpz_poly_set_coeff_ui(P, 1, 5);
    fmpz_poly_set_coeff_ui(P, 2, 6);
    
    fmpz_poly_factor_t fac;
    fmpz_poly_factor_init(fac);
    
    fmpz_poly_factor(fac, P);
    
    printf("Number of factors: %ld\n", fac->num);
    return 0;
}
