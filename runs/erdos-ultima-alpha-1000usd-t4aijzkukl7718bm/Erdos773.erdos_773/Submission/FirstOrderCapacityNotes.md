# Conditional first-order lifting bound

This does not settle Erdos 773. The main conjecture in `Spec.lean` still has
one admission, for 0 < epsilon <= 1/3, and was not changed in this continuation.

## Verified numerical lemmas

`MethodBarrier.lean` now contains:

* `first_order_capacity_bound`: if N,M >= 0, M <= p, and M^2 p <= N^2,
  then M <= N^(2/3).
* `first_order_capacity_bound_with_constants`: if N,M >= 0, M <= 2p, and
  M^2 p <= 4N^2, then M <= 2N^(2/3).

Both compile. Their printed axiom audits contain only propext,
Classical.choice, and Quot.sound. Log: `/tmp/method-barrier-new.log`.

The proofs multiply the capacity inequality by M^2, bound M^3, and compare
with the cube of the stated real-power bound.

These are conditional numerical bounds, NOT upper bounds on arbitrary
Sidon subsets of squares. A combinatorial lifting theorem supplying their
hypotheses has not been formalized. In particular, disjoint nonzero
scaled difference sets normally give M <= p + number_of_fibers - 1,
not exactly M <= p. One must account for that correction and for the
range of p before applying either lemma to an actual construction.

## Why the remaining quadratic information matters

For two residues r,s, replacing roots r+p*x and s+p*y by r+p*x' and
s+p*y' in an equal-square-sum relation gives

  2*r*(x-x') + 2*s*(y-y')
    + p*(x^2+y^2-x'^2-y'^2) = 0.

The first-order condition is only

  r*(x-x') + s*(y-y') = 0 mod p

(for odd p). Demanding disjoint scaled difference sets rules out these
first-order coincidences regardless of the quadratic term. The capacity
calculation diagnoses that restrictive strategy; it does not rule out
using the quadratic term to resolve overlaps.

## Further research, no positive theorem obtained

A growing collection of digit constraints was reconsidered. Fixed
histograms and fixed low-order position statistics already have exact
counterexamples in the other research files. Increasing the number of
constraints might change that, but there is presently no proof that a
sufficiently large statistic class avoids collisions.

The distinction between formal polynomial identities and equality after
integer evaluation remains essential. Gaussian Eisenstein arguments can
exclude formal identities while the evaluated integer squares still
collide. Controlling carries by a straightforward coefficient-size bound
loses a power in the root count. No improvement that closes the main gap
was obtained here.
