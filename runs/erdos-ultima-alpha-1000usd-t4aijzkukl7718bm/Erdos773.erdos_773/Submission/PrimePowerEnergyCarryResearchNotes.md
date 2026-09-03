# Prime energy at a power-of-three base: combined carry obstruction

This is NOT a settlement of Erdős 773. Spec.lean has not been changed and
still has its sole admission for 0<epsilon<=1/3. No proof was submitted.

## Verified module

`PrimePowerEnergyCarryObstacle.lean` imports only the clean, independently
proved `FormalGaussianSidon` module. It does not import Spec.lean. Its olean
is built. There are no errors, warnings, or admissions. All five printed
axiom audits use only propext, Classical.choice, and Quot.sound.

Log: `/tmp/prime-power-energy-carry-final.log`.

## Exact combined example

The module supplies four 21-digit words at

    B = 4782969 = 3^14,   u=v=2187.

All words have:

* leading digit 1 at position 20;
* constant digit exactly 24;
* every lower digit divisible by 6;
* all digits nonnegative and less than B/2;
* identical complete digit histograms;
* common digit sum 145207 < B;
* common squared-digit norm 3769070293, which Lean proves prime.

The lower polynomial after subtracting X^20 and dividing its coefficients
by 6 has constant coefficient 4 = 1 modulo 3 and degree below 20. Thus the
existing Gaussian-Eisenstein theorem applies. `formal_sidon` verifies that
the four formal polynomial squares are Sidon over Z[X]. `poly_eval` verifies
the connection between these polynomials and the integer digit evaluation.

Nevertheless the four evaluated roots are pairwise distinct and their
squares have a nontrivial equal sum. `not_sidon` and
`combined_conditions_do_not_suffice` give the formal counterexample to this
blanket sufficient criterion. The common gcd of the roots is exactly 3,
proved by `roots_gcd`. Do NOT assert pairwise coprimality: after dividing all
roots by 3, the zeroth and third roots still have gcd 5.

The words have a zero digit at position 19 and some repeated digits. Do NOT
claim that all digits are positive, all digits are distinct, or that the
constant digit occurs only once. The example does not prove failure at every
large base or at infinitely many prime energy levels.

## Symbolic certificate

For general u,v the four words have

    digit sum = 865 + 48u + 18v,
    squared-digit norm = 90721 + 648u^2 + 140v^2.

Writing P_j(X) for their digit polynomials, the exact identity is

    P0^2 + P1^2 - P2^2 - P3^2
      = 96 X^25 (uv-X)(X-1)(X^5-1).

Hence evaluation collides whenever B=uv. The Lean theorem
`norm_difference_factor` verifies this over the integers, and `collision`
transfers it to natural-number square sums.

The algebraic source is

    q = 12 + (12+6i)X + (12-6i)X^2 + 12X^3,
    r = 2 + (8+2i)X^5 + (8-2i)X^10,
    Q = X^5 + u q,   R = X^16 + v r.

Compare the real and imaginary parts of (1+i)QR and (1+i)conj(Q)R. Replace
uv by X at evaluation and divide the resulting expressions by X. The occupied
coefficient blocks remain disjoint, preserving their histograms and fixed
constant. This is an integer-evaluation identity, not a formal norm identity.

## Main-gap review

Small-prime Hensel lifting was reconsidered. Matching square residues modulo
a small prime does not identify the root labels, and it does not supply the
mixed-residue compatibility needed at the next level. No near-linear lift or
new actual Sidon exponent was proved.

The combined example closes a potential gap between previously separate
prime-power-base and prime-energy tests. It does NOT show that every digit
class is bad, nor exclude a large Sidon subclass. No actual lower or upper
exponent for the original maximum improved.
