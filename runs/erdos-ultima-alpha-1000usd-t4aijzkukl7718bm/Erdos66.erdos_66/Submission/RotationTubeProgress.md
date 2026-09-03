# Single shrinking rotation windows are not witnesses

## Original task status

The conjecture in `Submission/Spec.lean` is still neither proved nor disproved.
Its import, statement, and original `sorry` are unchanged. No proof has been
submitted. The results below exclude a restricted construction class only.

## New checked obstruction

Define

    tube(alpha,p) = {n : Nat | fract(n alpha) <= p(n)}.

`Erdos66MonotoneRotationTube.monotone_tube_no_nonzero_limit` proves:
for every antitone p with 0 <= p(n) <= 1, and every nonzero real c,

    r_tube(sqrt(2),p)(n) / log(n)

cannot tend to c.

No single-window, antitonicity, or rotation hypothesis has been derived for
an arbitrary witness of the original conjecture. In particular this is NOT
an exact-negation theorem for Erdos66.erdos_66.

## Finite spike estimate

`ShrinkingRotationTubeExplore.lean` proves the floor-window/cardinality
identity and a reflection lower bound, retaining both endpoint conditions.
If theta <= p(k) for all k <= 2N, 0 < theta <= 1, and

    30 + 50 log(N theta/2 + 1) < N theta/2,

then some n in [N,2N) satisfies

    r_tube(n) >= N theta/2 - 30 - 50 log(2N theta + 1).

The target is selected so that fract(n sqrt(2)) lies in [theta/2,theta).
Every endpoint a <= n with fract(a sqrt(2)) < theta/2 then yields a valid
pair (a,n-a). The already checked expected-mass rotation discrepancy supplies
the target and counts those endpoints.

There is consequently one T>0, before p,N,theta, such that N theta >= 2T
forces a target in [N,2N) with r_tube(n) >= N theta/4.

## Contradiction within this class

`MonotoneRotationTubeExplore.lean` also proves

    count_tube(L+K) <= count_tube(L) + 51 K p(L) + 81   (K>0).

The closed endpoint is handled by widening the window by 1/K; no claim that
all boundary hits can be ignored is made. The coarse estimate uses
log(X+1) <= X and works for widths greater than one as well.

If a nonzero logarithmic limit existed, its global logarithmic upper cap,
together with the finite spike theorem at N=q^2, would give

    q^2 p(2q^2) <= 2T + 4q

for all sufficiently large q. The interval estimate and antitonicity then
bound the number of selected points in [4q^2,8q^2) by

    408T + 816q + 81.

This contradicts the necessary square-annulus counting theorem for witnesses,
which requires more than any fixed linear function of q in this window.

## Verification

Both production files compile without warnings, with current oleans:

* ShrinkingRotationTubeExplore.lean
* MonotoneRotationTubeExplore.lean

`RotationTubeAudit.lean` checks nine principal declarations. The saved log
contains only `propext`, `Classical.choice`, and `Quot.sound`. Neither
production file contains a placeholder or a new axiom.

`RotationTubeChecks.lean` is an API-search scratch file containing an
intentionally failed name check; it is not a production dependency.

## Consequence for the search

Expected-mass-sensitive rotation sampling alone does not construct a witness.
A single shrinking window has correlated membership under reflection and
produces the proved spikes. Multiple changing finite patterns, more general
acceptance sets, and unrelated construction/disproof approaches remain outside
this result. No compatible changing-scale construction or universal logarithmic
fluctuation contradiction was obtained in this continuation.
