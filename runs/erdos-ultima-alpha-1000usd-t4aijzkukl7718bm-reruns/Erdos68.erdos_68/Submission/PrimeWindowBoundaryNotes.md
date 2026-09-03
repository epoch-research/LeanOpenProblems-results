# Short-window Lambert annihilators and prime boundary shifts

This is auxiliary work, not a settlement of Erdős 68. Spec.lean is unchanged
with its original sorry. No complete proof or disproof has been submitted.

## Verified prime-index identity

`Submission/PrimeWindowBoundary.lean` compiles without warnings and has a
built olean. All three printed principal axiom audits list only `propext`,
`Classical.choice`, and `Quot.sound`.

Write

    S_n = sum_(m=0)^n A_m/m!,
    r_x(n) = x-S_n,
    J_p(r) = p! r(p)-p (p-1)! r(p-1).

For every prime p, `primeJump_affine_tail` proves

    J_p(r_x) = -1

for every real x. This uses A_p=1, not a rationality hypothesis on x.
The coefficient of x is zero (`primeJump_const`).

For every 2<=d<p, `primeJump_geometricRowTail` proves

    J_p(n -> 1/((d!)^floor(n/d)*(d!-1))) = 0.

Indeed d does not divide p, so floor(p/d)=floor((p-1)/d).

Thus if a finite operator kills all rows below p, adding z*J_p preserves
those cancellations and changes a form A*x-B into A*x-(B+z) for any integer
z. This is `shift_affine_boundary` together with
`add_primeJump_preserves_row`.

The identity explains why row cancellation and a nonzero coefficient vector
alone do not provide nonvanishing of the resulting series value. It proves
no impossibility theorem for all annihilator families.

## Completed exact finite test (not Lean-verified)

The script `/tmp/short_window_annihilator.py` computed rational nullspaces of

    M_(d,t) = t!/(d!)^floor(t/d),
    d=2,...,K, t=n,...,n+width.

Every integral nullspace vector z gives a form

    A*x-B = sum_t z_t t! (x-S_t),
    A = sum_t z_t t!, B = sum_t z_t t! S_t.

Here B is integral by multinomial divisibility. The row factor d!-1 does
not affect the nullspace calculation. The script converted individual
rational basis vectors to primitive integer vectors, discarded those with
A=0, then reduced each pair (A,B) by its gcd. This last reduction need not
preserve integrality of the original operator weights, but does produce an
integer linear form. No search over general combinations of basis vectors
was performed.

Parameters:

    K=2,...,15,
    n in {0,floor(K/2),K,2K,4K},
    width in {K-1,K,2K}.

There were 106 parameter groups with a nonzero-A basis form. The script
saved the basis form with smallest certified upper bound on absolute error
in each such group. Of these saved forms, 95 had absolute error strictly
above one; 11 had error strictly between zero and one. Every saved form
with K>=5 had error above one.

For the interval bounds, alpha was enclosed between the exact original
partial sum through 199 and that sum plus 2/(200!-1). The classifications
used exact rational arithmetic. Logarithms in the log are diagnostics only.

Artifacts:

    /tmp/short_window_annihilator.py
    /tmp/short_window_annihilator.log
    /tmp/short_window_annihilator.json

The computation completed; nothing is pending. These finite tests do not
establish asymptotic growth or exclude other integer combinations, other
windows, or other families. Neither the finite tests nor the verified prime
identity settles the original irrationality conjecture.
