# Past accuracy does not guarantee a next-window extension

## Original task status

The conjecture in `Submission/Spec.lean` is still neither proved nor
disproved. Its sole import, statement, and original `sorry` are unchanged.
No valid final proof has been submitted.

## Checked finite-prefix obstruction

`Erdos66PrefixLookahead.accurate_history_does_not_ensure_extension`:

For any c>0, epsilon>0, multiplicative length R>=1 and starting bound N0,
there are N>=N0, L>=R*N, and a finite C subset [0,L) such that

    |r_C(z)/log(z)-c| < epsilon          (N<=z<L),

but NO superset A of C can satisfy even

    r_A(z)/log(z) <= c+epsilon          (L<=z<2L).

This is an existential statement about specially constructed bad prefixes.
It does not say that every accurate prefix is bad, and does not negate the
original existential conjecture. A finite bad peak can also be ignored by
moving a limit threshold beyond it; the obstruction concerns extension
with the prescribed accuracy/upper bound retained in the next window.

The stronger underlying theorem
`exists_accurate_prefix_with_future_peak` allows an arbitrary peak height
M>=0. It produces C subset [0,2*R*N+2), good on [N,2*R*N+2), with

    r_C(3*R*N)/log(3*R*N) > M,

and the global upper bound r_C(z)/log(z)<c+epsilon at EVERY other target.
The large future peak is already forced by points inside the finite prefix.
Thus adding later points cannot remove it.

## Construction

Start with the existing finite upper-bounded accurate annulus. Add one
symmetric repair packet with center n=3*R*N, requesting floor((M+1)*log(n))
pairs. The packet's points all lie below 2*R*N+2. Its self count at n is
exactly twice the number of requested pairs, while its collateral at every
other z is at most (epsilon/4)*log(z+2).

Truncate the union at 2*R*N+2. This does not change any past representation
count, and retains every point of the packet, hence retains its future
self peak. For z>=2, log(z+2)<=2*log(z) controls the collateral. The cases
z=0,1 use Lean's zero denominator convention directly.

## Localized repair result

`Submission/LocalizedRepairExplore.lean` refines the previously established
one-target global repair theorem, without changing that older theorem.
The new `eventually_localized_repair` additionally records

    n <= 4*a,    3*a <= 2*n+3            for every new point a,
    r_F(n) = 2*m.

These facts follow from the same candidate interval floor(n/3)+[0,n/12)
and its reflection. The selection, disjointness, exact union increment,
and uniform logarithmic collateral are inherited by reusing the checked
proof with the stronger output recorded.

## Scope relative to previous extension theorems

This does NOT refute `Erdos66UpperExtension.exists_upper_extension`: the bad
prefix here deliberately violates the desired global upper envelope at its
future peak. It demonstrates why past accuracy alone cannot replace that
lookahead hypothesis. Even with the global upper invariant, the previously
identified missing lower bounds in transition gaps remain unresolved.

## Verification

Both production files compile and have built oleans:

* `Submission/LocalizedRepairExplore.lean`
* `Submission/PrefixLookaheadExplore.lean`

`Submission/PrefixLookaheadAxiomCheck.lean` audits all three principal
results. Only propext, Classical.choice and Quot.sound occur.
