# Mixed counts from residue balance, and the resolution cost

The original conjecture remains unresolved. Spec.lean is unchanged.
No proof or disproof has been submitted.

## Exact natural mixed counts

PeriodicMixedDiscrepancyExplore.lean defines the residue histogram of a
finite natural set S, preserving multiplicities of congruent endpoints.
For D subset ZMod M, let P be its periodic realization clipped to [L,U).
If every a in S satisfies a<=n and L<=n-a<U, then exactly

    pairs(S,P;n) = sum_(z in D) hist(S,n-z).

Therefore a residue discrepancy bound

    |hist(S,z)-|S|/M| <= E

implies the actual natural mixed-count bound

    |pairs(S,P;n)-|S||D|/M| <= E|D|.

If A has prefix residue discrepancy at most E, every interval of A has
histogram discrepancy at most 2E. This is proved by exact cutoff-difference
identities. It yields a mixed estimate against an independently chosen
periodic interval; D need not be in the old palette. The eligibility
hypothesis retains the natural interval endpoints rather than counting
mere congruences as representations.

For the occurrence-phased old set of the preceding development, the
explicit bound is

    2 (|alpha|+2) M |D|.

## Why this bound does not close the transition

PeriodicMixResolutionExplore.lean checks the scale limitation of this
particular certificate. For real x,m,s,C,epsilon,l with x,m,C,l>=0 and s>=1,

    x s^2 <= C l m^2,     m s <= epsilon l

imply

    x <= C epsilon^2 l^3.

Using (log n)^3/n -> 0, it follows that for every fixed C>=0 and epsilon,
eventually, UNIFORMLY over positive integers M,s,

    n s^2 <= C log(n) M^2  ==>  epsilon log(n) < M s.

The antecedent is the logarithmic sparse-density upper scale for a
nonempty periodic template of size s in modulus M. Consequently the
reported phased-prefix certificate 2(t+2)Ms exceeds every fixed multiple
of log n on that scale. Increasing M alone does not make this certificate
sublogarithmic.

This is NOT a lower bound on actual mixed error. A sharper, structure-aware
estimate might be much smaller. It does not exclude phased constructions,
all periodic transition methods, or arbitrary witnesses.

## Verification

Both production files compile with current oleans. PeriodicMixAudit.lean
checks eleven declarations; its saved log contains only propext,
Classical.choice, and Quot.sound. No production sorry or axiom was added.
Natural-number binders in the residue histograms are explicitly typed to
avoid accidentally coercing a finite set to its residue image and losing
multiplicities.
