# Exact finite-gap experiment — not a settlement

Spec.lean is unchanged and still contains its original sorry. No new Lean
proof of the conjecture or its negation was obtained.

An auxiliary Python experiment (`/tmp/prime_floor_gaps.py`) uses integer
sieving and `fractions.Fraction`, not floating-point interval comparisons.
It subtracts the strict intervals (q/p,(q+1)/p), for prime p,q and
100 < p <= N, from [1,4]. Only positive-width remaining components are
tracked; isolated rational boundary points are discarded. Thus the
experiment is aimed at irrational points and is not a classification of
all rational boundary points. This computation has not been certified in
Lean and is not part of the final proof.

At N=100000 its two remaining positive-width intervals have endpoints

    [2, 199679/99839]
    [299882/99961, 299969/99989].

The second interval contains 3. Already at N=1000 only components
containing 2 and 3 survived. These finite observations do not imply that
no other component can arise at a later cutoff, nor that a surviving
component has an irrational limiting point.

The right endpoint of the first interval is 2+1/99839, coming from the
actual finite prime pair p=99839, q=2p+1. If p and 2p+1 are prime, their
success interval is (2+1/p,2+2/p). Obtaining infinitely many appropriately
placed such intervals is an additional unproved prime-pair assertion;
it cannot be inferred from the finite experiment.

No counterexample mechanism preserving a compact set of irrational slopes
was found. No incomplete proof was submitted.
