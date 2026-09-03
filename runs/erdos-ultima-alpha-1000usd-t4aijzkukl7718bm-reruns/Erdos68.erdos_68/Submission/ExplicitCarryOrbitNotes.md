# Explicit residual dynamics for the actual carried series

This is verified auxiliary progress, not a settlement of Erdős 68.
`Submission/Spec.lean` is unchanged with its original `sorry`.

`ExplicitCarryOrbit.lean` compiles without warnings and has a built olean.
All six printed principal axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`.

## Recurrence with no Lambert coefficients

In original indices, let z_n be the residual from
`CongruencePreservingCarry`, starting at z_3=16/5. Put

    v_n = n*z_(n-1) + 1/(n!-1).

The new file proves exactly

    z_n = v_n                                      if n is prime,
    z_n = v_n-(n-1)*floor(v_n/(n-1))                otherwise.

It defines a rational recursive function `orbit` by these formulas and
proves `orbit r = z r` in the existing Lean indexing (original n=r+3).
Thus no large Lambert coefficient or recursively accumulated integer carry
is needed to define the residual itself.

The corresponding composite coefficient is exactly

    c_n = 1+(n-1)*floor(v_n/(n-1)).

The proof uses the already verified coefficient identity, the predecessor
congruence, and the interval 0<=z_n<n-1 at composite indices. These identify
the quotient uniquely through the floor inequalities; no unproved extra
congruence is transferred into the carried coefficients.

## Fractional parts and the remaining arithmetic step

For all n>=3, with X_n=n!*sum_(k=2)^n 1/(k!-1), the file verifies

    frac(z_n)=frac(X_n),
    frac(z_n)=frac(n*z_(n-1)+1/(n!-1))       for n>=4.

If alpha=q is rational and q.den<=n, then

    1-3/(n+1) <= frac(z_n) < 1.

Consequently, arbitrarily late indices with frac(z_n)<=1/2 would imply
irrationality. This is the conditional theorem
`irrational_of_frequent_small_fraction`.

**That infinite-occurrence hypothesis has not been proved.** The recurrence
simplifies an existing rounding problem; it is not a new exclusion of
rationality. No assertion of equidistribution or of an unconditional
fractional-part limit is made, and no finite numerical test is used as a
substitute for the missing infinite statement.

Principal declarations:

* composite_quotient
* residual_composite
* orbit_eq_residual
* orbit_fractional_part
* orbit_fractional_step
* rational_fractional_interval
* irrational_of_frequent_small_fraction

## Other routes reviewed in this continuation

The prime-successor floor identity still reduces to rounding the original
partial sums. Existing Lambert congruences are not silently inherited by a
small-tail carry. The positive physical-domain kernel still gives the single
integral form 4*alpha-5, but no operation producing a growing family with
integral retained coefficients and nonzero errors tending to zero was found.
No new positive-kernel construction or numerical search was run in this
continuation.

No complete proof or disproof has been obtained or submitted.
