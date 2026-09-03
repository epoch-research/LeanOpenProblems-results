# Polynomially sparse completion

The original theorem in `Spec.lean` is still unresolved.

## Checked result

`Erdos66PolynomialSparseCompletion.polynomial_sparse_completion`:
for c>0 and K,C>=0, let A satisfy r_A(z)<=K+C log(z+2). Suppose its
asymptotic upper coefficient is at most c, and its asymptotic lower
coefficient is at least c away from a strictly increasing exceptional
sequence n_k with (k+1)^12<=n_k eventually. Then there is B containing A
with r_B(z)/log z -> c.

`dyadic_exception_completion` specializes the exceptions to n_k=2^k.
The exponent 12 is convenient, not asserted optimal.

## Construction and pipeline

* `SummableSpikesExplore.lean`: use q_i=n_i+1, a_i=0 in the joint engine.
  Summability of (i+1)^4/(n_i+1), sqrt(log(n_i+2))/sqrt(n_i+1), and
  1/sqrt(n_i+1) allows discarding a finite initial coordinate segment to
  meet the engine's prefix-cost bounds. This preserves all sufficiently
  late prescribed target multiplicities. No support-growth condition is
  needed.
* `RepeatedCentersExplore.lean`: enumerate target n_k with positive finite
  multiplicity r_k via the sigma type of its finite blocks. If S_{k+1} is
  the total multiplicity through block k, the required block costs are
  r_k S_{k+1}^4/(n_k+1), r_k sqrt(log(n_k+2))/sqrt(n_k+1), and
  r_k/sqrt(n_k+1).
* `SparseGrowthCostsExplore.lean`: if r_k<=D log(n_k+2) and n_k is
  monotone with polynomial growth of exponent 12, these costs are summable.
  Bound S_{k+1} by (k+1)D log(n_k+2), absorb logarithmic powers into square
  roots, and compare with (k+1)^(-2) or (k+1)^(-3).
* `PolynomialSparseCompletionExplore.lean`: choose the clipped deficit
  r_k=correction(r_A(n_k),c log(n_k+2))+1. The extra one avoids zero-sized
  enumeration blocks and costs only an additive two in the upper profile.
  The corrected profile is above c log(n_k+2) at exceptional targets and
  below max(r_A(z),c log(z+2))+2 everywhere. The engine's o(log z)
  collateral and the normalization log(z+2)/log z -> 1 finish the proof.

All four files compile and have built oleans. The audit in
`PolynomialSparseCompletionAxiomCheck.lean` reports only propext,
Classical.choice, and Quot.sound.

## Missing step

No base A satisfying the required eventual lower bound outside such sparse
exceptions has been constructed. The existing annulus constructions leave
dense uncontrolled transition intervals. This completion theorem is not a
proof or disproof of the original conjecture.


## Subsequent strengthening

The matching-based pipeline now proves completion for every fixed separation
exponent p>2, and more generally under a weighted reciprocal-square-root
summability condition. See `MatchingRepairProgress.md`. These are still
conditional completion results, not a construction of the required base.
