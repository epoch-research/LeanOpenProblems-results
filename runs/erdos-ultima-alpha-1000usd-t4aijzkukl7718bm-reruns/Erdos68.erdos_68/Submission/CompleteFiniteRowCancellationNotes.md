# Complete row cancellation inside a finite sampling window

This is verified auxiliary work, NOT a settlement of Erdos 68. Spec.lean
is unchanged and still contains its original sorry. Nothing has been
submitted as a proof or disproof of that conjecture.

`CompleteFiniteRowCancellation.lean` compiles without warnings and has a
built olean. Its three printed principal axiom audits contain only propext,
Classical.choice, and Quot.sound.

## Exact identity

Let S_n be the Lambert prefix sum_(m=0)^n a_m/m!, and let

    r_d(n)=1/((d!)^floor(n/d)*(d!-1)).

Choose arbitrary finitely many sample indices n_i<=N+1 and arbitrary REAL
weights w_i. Suppose all visible rows are cancelled:

    sum_i w_i*r_d(n_i)=0,     d=2,...,N+1.

Write A=sum_i w_i. The new theorem `boundary_eq_original_partial` proves

    sum_i w_i*S_(n_i) = A*sum_(d=2)^(N+1) 1/(d!-1).

Thus `error_eq_original_tail` identifies the resulting error exactly as

    A*alpha-sum_i w_i*S_(n_i)
        = A*sum_(d>N+1) 1/(d!-1).

For A!=0 this is nonzero (`error_ne_zero`), since the original omitted tail
is strictly positive. But it is exactly the ordinary partial-sum error
scaled by A, not a new rational approximation.

The theorem `boundary_integral_iff` consequently says that integrality of
the aggregate boundary is equivalent to integrality of A times this
ordinary partial sum. It makes NO assertion that individual denominators
survive reduction. The weights themselves need not be integral or rational.

## Proof mechanism

For any n<=N+1, rows d>N+1 have floor(n/d)=0. The verified infinite-row
identity therefore gives the finite-prefix formula

    S_n=sum_(d=2)^(N+1) [1/(d!-1)-r_d(n)].

Finite summation with the weights and the cancellation hypotheses proves
the result. No unproved exchange of infinite sums or sign condition on the
weights is used.

## Consequence for the interpolation investigation

A determinant or cofactor construction that cancels EVERY row through its
largest sampled index cannot evade ordinary partial-sum denominator costs
by merely replacing the constant-coefficient operator with interpolation.
This does not rule out partial row cancellation, uncancelled rows within the
window, rational weights, signed combinations, or other determinants.
Those possibilities still require a simultaneous arithmetic-height and
nonvanishing argument.

The most recent operator improvement remains the separate verified bound

    |Q_K(E)(alpha-S_H)|
       <= 2*exp(12)*exp(1)^H/(K+1)^(H-1),  K>=4, H>=2,

from FactorialGeometricProductBound.lean. It has not been combined with an
unconditional construction of nonzero cleared forms tending to zero.
No complete proof or disproof of the original conjecture was obtained.
