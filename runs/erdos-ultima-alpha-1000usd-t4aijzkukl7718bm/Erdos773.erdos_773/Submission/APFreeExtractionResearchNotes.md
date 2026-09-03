# Near-linear AP-free extraction from the squares

`APFreeExtraction.lean` imports only `FormalConjecturesUtil` and is independent
of the admitted main theorem. Namespace: `Erdos773.APFreeExtraction`.

## Verified results

* `reflected_extraction`: if S,T are subsets of `[0,L)` and T is three-AP-free,
  there is a three-AP-free B contained in S with

      |B| >= |S| |T| / (2L).

  Proof: average the fibers of `(s,t) -> s+t`, and project a largest fiber to
  its first coordinate. Projection is injective on a fiber; reflection in
  its fixed sum preserves three-AP-freeness.

* `behrend_extraction`: applying Mathlib's `rothNumberNat_spec` and
  `Behrend.roth_lower_bound` gives

      |B| >= (|S|/2) exp(-4 sqrt(log L)).

* `square_ap_free_finite`: with S the first N positive squares and L=N^2+1,

      |B| >= (N/2) exp(-4 sqrt(log(N^2+1))).

* `square_ap_free_near_linear`: for every real epsilon>0, eventually there
  is B contained in the first N positive squares, ThreeAPFree B, and
  `N^(1-epsilon) <= B.card`.

  The asymptotic step is elementary: for N>=2, log(N^2+1)<=3 log N.
  Once log N is at least both 2 log(2)/epsilon and 192/epsilon^2, the
  exponential loss is bounded by N^epsilon.

* `four_distinct_of_collision`: in a ThreeAPFree set of natural numbers,
  every nontrivial equality a+b=c+d has all four entries pairwise distinct.

The three printed audits (the finite square theorem, the near-linear square
theorem, and the four-distinct lemma) use only propext, Classical.choice,
and Quot.sound. There are no admissions in this module.

## Scope and remaining gap

This is an actual integral subset construction, not a fractional relaxation.
However, ThreeAPFree is strictly weaker than IsSidon. The construction does
not control four-distinct-value square-sum collisions, and neither proves nor
disproves Erdos 773. No bound improving the main exponent 2/3 was obtained.
The auxiliary result has not been copied into Spec.lean.

Compile/audit log: `/tmp/ap-free-extraction.log`.
Main-file compile log: `/tmp/spec-ap-free-check.log`.
