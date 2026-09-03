# Exact zero pairs in enlarged quadratic windows

Verified auxiliary work, NOT a proof or disproof of Erdos 68. Spec.lean
remains unchanged with its original sorry. No proof or disproof has been
submitted.

`LambertZeroPairWindow.lean` (136 lines) compiles without warnings and has
a built olean. It contains no proof holes. Both printed principal axiom
audits use only `propext`, `Classical.choice`, and `Quot.sound`.

## General difference construction

Suppose D+1 real boundaries B_i have a common positive integral clearing
factor C, and each lies within eta of the same A*x, where A is integral.
If

    C < (Q+1)^D,       2*D*Q*eta < 1,

then `zero_pair_of_difference_clearing` supplies integer weights w_i with

    w != 0,
    |w_i| <= D*Q,
    sum_i w_i = 0,
    sum_i w_i*B_i = 0.

Apply the existing bounded modular pigeonhole theorem to the D differences
B_(i+1)-B_0. Their absolute values are at most 2*eta. The resulting integral
boundary has absolute value less than one, so it is zero. For its nonzero
weights v_i, set w_0=-sum_i v_i and w_(i+1)=v_i.

This is an unconditional zero-pair construction, not a nonvanishing theorem.

## Lambert specialization

For every K>=32, use

    ds=[2,...,K+1],
    H=K^2,
    sample indices H,...,H+K^2,
    Q=(4*K^2)^4.

The endpoint for common clearing is 2*K^2, and the sum of the operator
shifts is at most 2*K^2. Consequently

    C <= (4*K^2)! <= Q^(K^2) < (Q+1)^(K^2).

The existing analytic bound gives

    K^2*Q*eta <= 256/K^2,

so 2*K^2*Q*eta<1 for K>=32. The theorem `quadratic_zero_pair` therefore
provides nonzero integer weights on K^2+1 samples with

    |w_i| <= K^2*(4*K^2)^4 = 256*K^10,
    sum_i w_i=0,
    sum_i w_i*boundary(ds,K^2+i)=0.

These forms vanish identically at every real endpoint, not merely under
hypothetical rationality of the target.

## Scope and further review

This rules out asserting that every short nonzero cleared vector in these
windows is useful. It does NOT rule out selecting other vectors with
nonzero coefficient pairs or values. It also does NOT contradict the
verified d-phase detector: only one output phase is asserted zero here.
No simultaneous-zero claim or impossibility theorem for all multi-row
height extensions is proved.

An explicit-lift route using consecutive raw boundary differences was also
reviewed. A gcd or a surjective pair image alone still leaves the size of
the first/lifted coefficient uncontrolled. Congruences of the original
Lambert coefficients do not immediately give the analogous gcd bounds after
the raw operator. No all-index useful-lift bound was established, and no
complete informal argument for the original irrationality conjecture was
obtained.

No numerical experiment or submission check was run. All compilation and
axiom checks have completed; nothing is pending.
