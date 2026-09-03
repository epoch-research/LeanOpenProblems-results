# Specialization at powers of the Eisenstein prime

This does NOT settle Erdős 773. Spec.lean is unchanged and still has its
sole admission for 0 < epsilon <= 1/3. No proof has been submitted.

## Verified family

`InertPrimePowerSpecialization.lean` imports only the independently proved
`FormalGaussianSidon` module. For each integer t>=2, put

    B=(6t+3)^2, u=3t^2+3t,
    P0=1+(6t+3)X+u X^2,
    P1=1+(6t+5)X+(u+6t+4)X^2,
    P2=1+(6t+4)X+(u+3t+2)X^2,
    P3=1+(6t+4)X+(u+3t+3)X^2,
    Ej=X^3+6Pj.

All parameters are admissible for the Gaussian-Eisenstein formal Sidon
construction. All four E polynomials are monic cubics, have constant
coefficient exactly 6, and have positive canonical base-B digits. Every
coefficient below the leading term is divisible by six.

Their exact discrepancy is

    E0^2+E1^2-E2^2-E3^2=12 X^4 (B-X).

Consequently the evaluated square sums collide, and the positive integer
root values satisfy

    value(0)<value(2)<value(3)<value(1).

`formal_square_sidon` and `specialization_not_sidon` verify both sides of
this distinction. No irreducibility-preservation claim under evaluation is
used.

## Unbounded powers of 3

The natural recurrence

    index(0)=4, index(k+1)=3 index(k)+1

has

    6 index(k)+3=3^(k+3),
    B(index(k))=3^(2k+6).

`prime_power_failure` packages the admissibility, positive canonical digits,
formal Sidon property, and failure after specialization at every one of
these bases. `prime_power_bases_unbounded` proves the bases are unbounded.
Thus restricting the base to powers of the very same inert prime 3 does
not repair the blanket specialization assertion.

At t=4, B=729, the four evaluated roots are

    578857353, 668148189, 623502771, 626691417.

These illustrative numbers are not needed for the symbolic Lean proof.

## Algebraic derivation

Take lower parameter coefficients (c,c+2,c+1,c+1) and upper ones

    (u,u+c+1,u+v,u+c+2-v).

Set c=2v-1 and u=v(v-1)-(B+3)/6. The norm discrepancy becomes
12 X^4 (B-X). Choosing v=3t+2 gives the integral family above.

The original exact computational check also found a cubic collision at
B=243=3^5, with (low,high) pairs (13,1), (15,15), (14,8), (14,9).
That initial check was exploratory; the submitted scratch theorem proves
the unbounded even-exponent family symbolically, not via trusted numerical
search.

## Remaining main gap

Reexamining the bounded-difference-multiplicity construction did not supply
a conversion to Sidonness. The existing near-linear relaxed sets can have
capacity g>1, whereas the conjecture requires capacity one. No new exponent
for actual Sidon subsets was obtained in this continuation. The new family
above concerns a sufficient construction criterion, not all subsets of the
squares and not the negation of the conjecture.

## Verification

The module compiles without errors, warnings, admissions, or extra axioms.
All eight printed audits use only propext, Classical.choice, Quot.sound.

    /tmp/inert-prime-power-specialization.log

A built .olean is available under .lake/build/lib/lean/Submission/.
