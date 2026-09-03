# Prime-power scaling of the original coefficients

Verified auxiliary arithmetic, NOT a settlement of Erdős 68. The original
Spec.lean is unchanged with its sorry. No proof or disproof has been submitted.

`LambertPrimePowerScaling.lean` compiles without warnings and has a built
olean. Its three principal printed axiom audits contain only propext,
Classical.choice, and Quot.sound.

Let a_n be the original Lambert coefficients and F_n=a_n+n! for n>0,
including singleton blocks. Iterating the existing prime-scaling congruence
proves, for every prime p, m>0, and r>=0,

    F_(p^r*m) = F_m                         modulo p,
    a_(p^(r+1)*m) = a_m+m!                  modulo p.

The second statement retains the necessary singleton correction. In
particular,

    a_(p^(r+1)) = 1                         modulo p,
    p divides a_(p^(r+1))-1.

This is an elementary iterated consequence of LambertPrimeScaling, not a
new small-tail estimate. It is NOT asserted for any carried coefficient
sequence. No inheritance result that combines this congruence with the
existing small-tail bounds has been obtained.

The polynomial positive-kernel construction was also reviewed. A fixed
positive certificate remains different from a family of integral forms
with errors tending to zero. No such new family or height bound was found,
and no numerical search was run in this review.

The conjecture remains unresolved in this workspace.
