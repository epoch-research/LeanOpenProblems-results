# Conditional all-target upper clipping with exact brackets

## Status

The original conjecture remains unproved and undisproved. Spec.lean is
unchanged, including its original sorry. No final proof was submitted.

CertifiedGlobalUpperClippingExplore.lean compiles, has a current olean,
and has no warnings or placeholders. All four lemma/theorem declarations
are audited in CertifiedGlobalUpperClippingAudit.lean and its saved log;
only propext, Classical.choice, and Quot.sound occur.

## Certified restoration of the full deletion set

exists_certified_full_restoration extends the simultaneous sparse restoration
result by retaining SmallBoundary and SublogCentral. Input: exact-bracket A
with both invariants, D subset A, and

    count(D,N)/sqrt(N log N) -> 0.

Output: one B containing A minus D, satisfying every original exact bracket,
both qualitative invariants, and

    (r_B(n)-r_(A minus D)(n))/log n -> 0.

The existing certified menu treats only a remote part E of D. Its untouched
initial part is the finite set cutoff(D,N0). The exact identity

    A minus E = (A minus D) union cutoff(D,N0)

bounds the extra representation count by twice that finite cardinality.
This finite-prefix contribution vanishes after division by log n.

## One simultaneous upper clipping, not separate local swaps

Let q:Nat->Nat satisfy q(n)>=1. Put

    excess(r,q) = if q<r then floor((r-q+1)/2) else 0.

Assume the explicit original-host budget

    [sum_(n<2N) excess(r_A(n),q(n))]/sqrt(N log N) -> 0.

Then exists_certified_upper_clipping_under_budget produces ONE core C and
ONE restored B with:

* C subset A and C subset B;
* r_C(n)<=q(n) for EVERY n;
* every original exact harmonic bracket for B;
* SmallBoundary(B) and SublogCentral(B);
* (r_B(n)-r_C(n))/log n -> 0;
* max(r_B(n)-q(n),0)/log n -> 0.

The monotone clipping theorem supplies C and the deletion-count estimate.
The displayed budget makes A minus C negligible, so the certified full
restoration theorem applies to the entire deletion set at once. There is
no iteration of separate rank-relocation swaps and no sum of their errors.

upper_limit_of_excess_limit additionally proves that q(n)/log n -> c
implies, for every epsilon>0, eventually r_B(n)/log n <= c+epsilon.
This is an asymptotic upper bound, not a two-sided limit theorem.

## Missing input and remaining main gap

The budget is NOT established for caps q(n)/log n -> 1 on the constructed
coefficient-one hosts. Weak power-saving exceptions may have counts of
order N^(1-alpha) with alpha much smaller than 1/2; multiplying those
counts by a logarithmic envelope does not give the required budget at the
sqrt(N log N) scale. Density zero alone is insufficient as well.

Even if the budget were established, the theorem supplies no pointwise lower
asymptotic. The clipped core may lose representations at previously good
targets, and no adequate weighted lower-exception estimate is known. No
compatible finite-algebraic changing-period construction was obtained in
this review. Nothing in this file settles the original existential claim.
