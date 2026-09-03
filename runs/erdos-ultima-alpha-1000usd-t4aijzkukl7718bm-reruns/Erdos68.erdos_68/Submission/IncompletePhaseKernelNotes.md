# An obstruction to omitting a geometric-row phase

Verified auxiliary progress, NOT a proof or disproof of Erdős 68.
`Submission/Spec.lean` is unchanged and retains its original `sorry`.

`IncompletePhaseKernel.lean` (283 lines) compiles without warnings and has a
built olean. Its three printed principal axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`. It contains no proof holes.

## New unconditional theorem

For every d>=12, every starting index H, and every finite raw-filter list ds,
there are L>0 and integer weights w_(j,k), 0<=j<d, 0<=k<L, such that

    w is not identically zero,
    |w_(j,k)| <= floor(d!/4),
    sum_(j,k) w_(j,k) * rawApply_ds(r_d)(H+i+j+d*(L-1-k)) = 0
        for every 0<=i<d-1,

where

    r_d(n) = 1/[(d!)^floor(n/d)*(d!-1)].

The sample map (j,k) -> j+d*(L-1-k) is injective; its injectivity is separately
verified. Thus the nonzero weights are not merely duplicate samples that
cancel each other. The support length is not bounded independently of d or
the filter. The coefficient bound satisfies the original detector's
restriction 4*Q<=d!.

This concerns a SINGLE geometric row. It does NOT assert that these weights
annihilate the full target tail, which sums infinitely many different rows.
It also makes no assertion about integral aggregate boundaries. In particular
it does not contradict the existing full-period or full-target detectors.

The theorem prevents simply replacing a full d-phase window by d-1 phases in
an arbitrary-support first-row detection argument with the same height bound.
It does not rule out a genuinely multi-row argument or an additional
restriction on the support or coefficient pattern.

## General finite counting result

For arbitrary integers a_(i,j), with m output coordinates and d initial
columns, let B>=2 and suppose

    B^m < (Q+1)^d.

The theorem `bounded_geometric_kernel` produces L>0 and bounded nonzero
integer weights satisfying exactly

    sum_(j,k) w_(j,k) * a_(i,j) * B^k = 0   for every i<m.

Choose a positive bound A on all |a_(i,j)|. The geometric sum bound
sum_(k<L) B^k <= B^L bounds every output in magnitude by d*Q*A*B^L.
Modular pigeonholing into m copies of ZMod C, where

    C=(2*d*Q*A+1)*B^L,

gives a bounded nonzero relation once C^m<(Q+1)^(d*L). The strict base
inequality guarantees such an L. Since each resulting divisible output has
absolute value below C, it is zero as an integer, not just modulo C.

`rational_periodic_kernel` clears a finite rational matrix and applies this
to any rational sequence f satisfying B*f(n+d)=f(n). Multiplication by
B^(L-1) identifies the displayed geometric sums with the sampled responses.
This recurrence is preserved by every raw filter.

Finally, `four_pow_lt_factorial` proves 4^d<d! for d>=12. Together with
B<=4*(floor(B/4)+1), this implies

    (d!)^(d-1) < (floor(d!/4)+1)^d,

which supplies the strict base inequality for m=d-1.

## Construction diagnostics, not proof premises

An exact Sage calculation examined the primitive kernel of e-1 phases of
row e after filtering rows 2,...,e-1, first with only e consecutive input
weights. Those primitive vectors can have very large coefficients. For
example, the smallest phase-rotated primitive height at e=12 has 240 bits.
This does NOT give a lower height bound for arbitrary supports: extending
the support allows geometric-base encoding and the counting theorem above.

Artifacts are `/tmp/omitted_phase_kernel.py`, `.json`, and `.log`.
These finite calculations are not used by the Lean proof. The new theorem
is a general counting argument, not an extrapolation from those calculations.

## Status

The consecutive-phase boundary-clearing approach still lacks a controlled
small nonzero integral form. The positive-kernel construction was also
reviewed, but no growing family with controlled integral boundaries and
vanishing errors was obtained. There is no complete informal settlement
awaiting formalization. No proof or disproof has been submitted, and no
computation or compilation is pending.
