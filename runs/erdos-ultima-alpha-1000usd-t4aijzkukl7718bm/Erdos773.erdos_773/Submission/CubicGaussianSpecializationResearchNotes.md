# Cubic and all-degree carry obstructions

This does NOT settle Erdős 773. Spec.lean is unchanged, with its sole
admission for 0 < epsilon <= 1/3. No incomplete proof has been submitted.

`CubicGaussianSpecialization.lean` imports the independently proved
`FormalGaussianSidon.lean`, not the admitted main file. Its printed audits
use only propext, Classical.choice, and Quot.sound. It builds without errors
or warnings and has a built .olean.

## Cubic obstruction with monotone lower digits

For every integer t >= 6, put B=132t. In the order 0,1,2,3, take

    P0 = 1+(6t+7)X+(20t-1)X^2,
    P1 = 1+(6t+4)X+( 8t-6)X^2,
    P2 = 1+(6t+6)X+(20t-6)X^2,
    P3 = 1+(6t+5)X+( 8t+1)X^2,
    Ej = X^3+6Pj.

All four Pj are admissible for the exact proved formal Gaussian family.
The Ej are monic of degree 3 with constant coefficient exactly 6. Their
three lower coefficients are positive, strictly increasing, divisible by
6, and less than B. The leading coefficient is 1, not part of that
increasing triple.

The exact polynomial identity is

    E0^2+E1^2-E2^2-E3^2 = 24 X^4 (B-X).

The discrepancy is nonzero. Evaluation at B produces positive, distinct
roots with equal square sums. Their order is value(1)<value(3)<value(2)<value(0).
Evaluation is injective on these four roots, and their formal squares are
Sidon. Their integer squares are not Sidon.

At t=6, B=792, the root values in the displayed order are

    944863926, 655053702, 926041254, 681403542.

Primality is NOT claimed for these bases. They are multiples of 132, and
hence in particular divisible by the inert Gaussian prime 3. A theorem
`bases_unbounded` explicitly verifies unboundedness of the base family.

## Every degree at least three

The namespace `AllDegrees` gives a separate family. For k>=0, t>=7,
again B=132t, put

    P0 = 1+9X+13X^2+6t X^(k+1)+20t X^(k+2),
    P1 = 1+6X+ 4X^2+6t X^(k+1)+ 8t X^(k+2),
    P2 = 1+8X+ 8X^2+6t X^(k+1)+20t X^(k+2),
    P3 = 1+7X+11X^2+6t X^(k+1)+ 8t X^(k+2),
    Ej = X^(k+3)+6Pj.

The checked identity is

    E0^2+E1^2-E2^2-E3^2 = 24 X^(k+4) (B-X).

Every Ej is monic of degree k+3, with constant coefficient 6. Every
coefficient is nonnegative and less than B, and every coefficient below
the leading one is divisible by 6. This includes k=0 and k=1, where some
of the displayed terms overlap. Thus these are genuine canonical digits,
not signed or oversized coefficients.

The four evaluations are positive, distinct, and have a nontrivial
square-sum collision, although the four formal squares are Sidon.
There is NO monotonicity claim for this all-degree family: some intermediate
digits are zero. Its public APIs include `admissible`, `canonical_digits`,
`monic_degree`, `norm_difference`, `collision`, `value_injective`,
`formal_square_sidon`, and `specialization_not_sidon`.

## Algebraic source

For B=132t, let u=5B+1 and v=7B+1. Set

    j=B(5s-6)+s+4,
    i=B(7s-6)+s+6.

Direct expansion gives

    [6(B(i+u)+1)]^2 - [6(Bi+1)]^2
      = [6(B(j+v)+1)]^2 - [6(Bj+1)]^2.

Taking s=6t gives the monotone cubic family. Taking s=6t B^k+2 gives
the all-degree family after the leading carry. The final Lean proofs
verify the polynomial discrepancies directly by ring normalization; no
computer-algebra output is trusted.

## Scope and current gap

These results refute a blanket integer-specialization rule even for
constant digit 6, canonical digits, and (in the cubic case) increasing
lower digits. The all-degree result means merely choosing a larger degree
does not make the full canonical family Sidon at these bases.

They do not bound the largest Sidon SUBSET of those families, do not rule
out other bases, and do not disprove the original conjecture. No
near-linear low-collision subfamily has been constructed. The arithmetic
sieve reconsideration also yielded no fixed exponent upper loss for the
actual maximum. The best proved original lower exponent remains 2/3-o(1).

Logs:

    /tmp/cubic-gaussian-specialization.log
    /tmp/spec-cubic-continuation-check.log
