# Simultaneous upper clipping and the exact prefix deletion budget

## Original task status

The conjecture in `Spec.lean` remains unresolved. No proof or disproof has
been submitted, and the original file is unchanged.

## Why switch to monotone deletion?

The preceding continuation proved that exhaustive restore-then-upper-delete
resets recover their host outside a finite prefix. Deletion only does not
have that absorption defect: every upper bound established at a target
persists through all subsequent deletions. It does not automatically preserve
any lower bound.

## New unconditional theorem

`Erdos66MonotoneClipping.exists_simultaneous_upper_clipping` proves:

For every A subset of the natural numbers and every integer cap q(n)>=1,
there is C subset A such that

    r_C(n) <= q(n)                         for every n,

and

    count(A\C,N)
      <= sum_(n<2N) excess(r_A(n),q(n)),

where

    excess(r,q) = 0                       if r<=q,
                  floor((r-q+1)/2)       if r>q.

The proof clips targets in increasing order, deleting only larger endpoints
of distinct representation pairs. At a single target this deletes exactly
excess(r,q) points and leaves the count between min(r,q-1) and q. The number
needed at each stage is no greater than the original host excess because
all preceding steps are deletions.

The infinite final set is the intersection of the decreasing sequence.
An endpoint a can be deleted at target n only if n<2a. Hence every point below
N is already final after stage 2N. This gives both an explicit stabilization
cutoff and the finite prefix budget. No central-boundary or triple-intersection
hypothesis is required for this theorem.

The lower single-step bound is NOT asserted for the final set.

## New conditional counting transfer

`Erdos66ClippingBudgetTransfer.clipping_preserves_count_limit_under_budget`
proves that if R(N)>0 eventually,

    count(A,N)/R(N) -> d,
    sum_(n<2N) excess(r_A(n),q(n))/R(N) -> 0,

then a clipped subset C can be chosen with the same counting limit d and all
the pointwise upper bounds r_C(n)<=q(n).

The supporting finite estimate is

    sum_(n<N) excess(r_A(n),q(n)) <= count(E,N)*V,

if r_A(n)<=V for n<N and E={n:r_A(n)>q(n)}.

These are conditional on the actual deletion-budget estimate. No such
estimate has been proved for a cap with the desired exact asymptotic
coefficient on the existing rounded profiles.

## Remaining obstruction

The known positive power saving for each fixed tolerance may be smaller
than one half. Thus bounding the clipping budget by an exceptional count
times a logarithmic envelope does not supply a negligible budget at the
square-root-logarithmic counting scale for all shrinking tolerances.

Moreover, even a proved sharp counting profile and the exact upper envelope
would not give the missing all-target lower limit. The previously checked
dyadic-deletion example preserves the counting profile while creating
infinitely many representation holes. Neither the monotone clipping theorem
nor its count-transfer corollary removes this issue.

The high-coefficient host is also not a density-preserving way to enforce
coefficient one: clipping from its >=448 log n lower envelope requires
macroscopic changes. The coefficient-one host is the more relevant possible
input, but no small-budget and lower-exception estimate is available for it.

## Files and verification

* MonotoneClippingExplore.lean
* ClippingBudgetTransferExplore.lean
* MonotoneClippingAudit.lean

Both production files compile, have oleans, contain no sorries, and their
principal results pass the allowed-axiom audit. The audit reports only
propext, Classical.choice, and Quot.sound.

No assertion in these files settles the existential proposition in Spec.lean.
