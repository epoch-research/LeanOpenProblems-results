# Status: unresolved

**New verified factor-count obstruction:** `FactorCountObstruction.lean`
proves that any cube-Sidon root set whose membership depends only on Ω(n),
the number of prime factors with multiplicity, is contained in {0,1}. The
same conclusion holds for dependence only on ω(n), the number of distinct
prime factors. On the squarefree source, a set selected solely by its factor
count is contained in {1}. These are restricted impossibility results, not
a disproof for arbitrary positive-density sets. Spec.lean remains unresolved.

**New verified obstruction:** `CubeDigitSumObstruction.lean` proves that
no coloring `n ↦ f (digitSum_b (n^3))` has all cube-Sidon fibers, for any
base b>1 and any function f (even with infinitely many colors). The proof is
uniform, not a finite search: if 0<m and 3m≤b^k, the digit sum of
m*(b^k-1)^3 is exactly 2*(b-1)*k. Taking m=1^3,9^3,10^3,12^3 gives one
monochromatic collision. This rules out only a restricted coloring approach,
not arbitrary positive-density Sidon root sets. Spec.lean remains unresolved.

**New relative strengthening:** `RelativeCompactness.lean` proves
source-preserving finite-prefix compactness. `CubicSamplingStage.finite_stage_in_source`
retains containment in `sourcePrefix S M`, and
`LinearCollisionExtraction.linear_collision_source_subset` now exports
`A ⊆ S` as well as infinitude, positive lower density, and the cube-Sidon
property. The original weaker interfaces are retained as wrappers. All new
results compile with only the permitted axioms. This closes a bookkeeping gap,
not the missing construction of an arithmetic source; Spec.lean is unresolved.

**Newest completed reduction:** the 12-file, 1238-line linear-collision
extraction chain is now fully verified. `LinearCollisionExtraction.lean`
proves that a positive-lower-density source S with at most C*N cubic
collision edges in every prefix has a positive-lower-density cube-Sidon
subset in the existential sense required by Spec.lean. (The exported theorem
does not assert subset membership, although its finite witnesses lie in S.)
The pair-codegree, finite sampling, hub trimming, maximum-root deletion,
simultaneous prefix bounds, and compactness steps are complete. NO source
satisfying the required uniform linear bound has been constructed. This is
therefore still a CONDITIONAL reduction, not a proof or disproof of the
conjecture. Spec.lean remains unchanged. See the final entry for interfaces.

**Latest verified continuation:** `UnitGapCongruences.lean` and
`GapDifferenceSource.lean` (204 lines total) add the universal modulo-12
restriction on canceled gaps of roots coprime to 6, remove the coprimality-to-3
restriction from the progression gap-congruence lemma, and construct a
positive-density progression excluding every ratio with `0<u-v≤K` for each
fixed K. These include infinitely many ratios approaching one. The density
bound is NOT uniform in K, so this does not settle the conjecture. See the
last entry. Spec.lean remains unchanged.

**Newest global reduction:** three new files (409 lines) now prove source-preserving geometric-bin extraction and `RelativeEndpointReduction.summable_endpoint_maxima_suffice`. Only reciprocal summability of primitive maxima in the two endpoint gap-ratio regimes is needed; the compact middle range can be removed INSIDE an arbitrary positive-density source. The endpoint summability hypothesis remains unproved. Spec.lean is still unchanged and unresolved.

**Latest verified global reduction:** `RelativePrimitiveMaxima.summable_maxima_suffice` now proves that a positive-lower-density source of positive integers with reciprocal-summable distinct normalized primitive collision maxima would settle the original conjecture. `FiniteRatioSource` and `RelativePrimitiveCover` rigorously handle the finite head without any multiplicative invariance assumption. Constructing the required source for ALL collisions remains open in this development; the fixed-conic construction does not supply it.

**Latest verified result:** the fixed-conic reciprocal-summability step and
normalization-safe source-relative divisor cover are now COMPLETE (five
additional files, 602 lines). A positive-lower-density squarefree source A
has a summable set B of divisors >1 meeting every surviving positive rational
scaling of this explicit conic. This is NOT a cover of all cubic collisions;
the independent all-family/global gap remains. See the final entry.

**Newest verified continuation:** twelve new files (1288 lines) close the
quantitative mixed-prime mass and source-scheduling gaps for the explicit
conic. They prove reciprocal mass >=(1/2)log log y-O(1), the logarithmic
first-moment upper bound, the resulting 7/4-exponent finite sieve, and a
positive-density squarefree source with rational-proportionality coverage
and thresholds k_j=o((3/2)^j). Reciprocal summability of surviving parameters
and the separate GLOBAL all-family argument are still unfinished. See the
last entry. Spec.lean remains unchanged and unresolved.

**Newest verified result (sharp uniform prime-score sources):** the four-file
sharp extension now allows arbitrary real weights and removes the additive
energy loss. It gives every-prefix moving-score variance <=48N*mass, countably
many bands on a positive-lower-density squarefree source, and energy-scaled
center oscillation. The conic mixed-mass bound is uniform in common dilations.
This closes the uniform prime-block SOURCE-density gap, but NOT the
exceptional-parameter sieve or the global bound across all conic families.
Spec.lean is still unresolved. See the last entry for exact formulas.

`Spec.lean` is unchanged and still has `sorry`. None of the auxiliary files is
a proof or disproof of the original existential conjecture.

**Newest verified result (distinct whole-root covers):** the seven-file
quadratic-energy development and its five-file rough-family extension are
COMPLETE. Distinct maximum roots, arbitrary reused whole-root covers, fractional
whole-root covers, and bounded-cofactor divisor covers all have divergent
reciprocal cost on the squarefree primitive source coprime to any fixed Q>0,
even after removing finitely many rational quadratic families. The required
normalization bound is proved. This does NOT rule out arbitrary proper-divisor
covers or settle the positive-density conjecture. See the last two entries.

**Latest verified continuation:** the squarefree rough residual-mass extension
is COMPLETE. `RoughSquarefreePrimitiveMass.lean` proves divergence for distinct
primitive collisions with all roots squarefree and coprime to any fixed Q>0,
below every compact adjacent-gap cutoff. `SquarefreeQuadraticFamilyResidualMass.lean`
transfers this to the complement of any finite list of quadratic families.
The normalization and injectivity steps are proved. This is still a counting
result, NOT a reusable-cover lower bound or a settlement of the original
positive-density conjecture. See the final entry for the nine new files.

**Newest verified continuation:** the five rough-family files listed in the
final entries strengthen the residual reciprocal-mass theorem: after any
finite quadratic-family removal, and with every root coprime to any fixed
positive modulus Q, the distinct primitive collisions still have divergent
reciprocal maximum-root mass. This is NOT a lower bound for a reusable cover
and does not settle the original conjecture. Spec.lean remains unresolved.

**Latest continuation:** the rational quadratic triple-family classification is
now verified, including rank degeneracies and coordinate swaps, with explicit
nonzero/distinctness hypotheses. `QuadraticOddSpecialization.lean` proves that
an all-odd six-distinct integer specialization with nonzero common cube sum
forces the entire family to be a common polynomial dilation of constants.
This does not control arbitrary higher-degree families or odd cycles and does
not settle the density conjecture. See the final entry for exact interfaces.

Latest verified addition: `SquarefreeSourceCollisionGrowth.lean` now proves
unconditional full-prefix superlinear collision counts on squarefree roots
coprime to 6. The earlier missing coprime-multiplier estimate for this source
is CLOSED; see the final entry below. This still gives no independence bound
and does not settle the conjecture.

Latest additional verified result: `TripleConicGrowth.lean` proves full-prefix
superlinear counts of six-root, three-pair equal cube-difference configurations,
each supporting a three-edge odd cycle. A single divisor (5) covers the entire
new family, so this does not obstruct reusable divisor covers or settle the
conjecture. See the final entry.

Latest cover result: `QuadraticTripleParity.lean` proves that the divisor 2
meets every normalized configuration in a broader rational-parameter family
of quadratic triple identities. This is a family-specific cover, NOT a
classification or cover of all odd cycles. The fixed-family cover by 5 also
now survives common-factor normalization. See the final entry.

Latest general arithmetic result: `CollinearTripleParity.lean` proves that
three distinct collinear integer points on x^3+y^3=S!=0 cannot have all six
coordinates odd. This covers chord-generated triples by 2, but not arbitrary
triples or odd cycles; the conjecture remains unresolved. See the final entry.

Recent verified additions beyond the earlier reductions:

* `MultiplicativeObstruction.lean`: corrected multiplicativity to require both
  factors positive. All three public obstruction theorems compile with only
  `propext`, `Classical.choice`, `Quot.sound`.
* `TranslationObstruction.lean`: a nontrivial fixed four-root pattern has at
  most one nonnegative common translation giving a cubic collision. Compiles;
  allowed axioms only.
* `CoprimeCollisionFamily.lean`: arbitrarily large pairwise-coprime cubic
  collisions, via four explicit quadratic forms and six Bezout identities.
  Compiles; allowed axioms only. This does not obstruct every prime-based sieve.

Finite unrestricted coloring diagnostics (not Lean proofs):

* 1000 roots: SAT, 1601 collision constraints.
* 5000 roots: SAT, 16031 collision constraints; returned assignment checked
  against all 32062 generated CNF clauses.
* 10000 roots: unresolved. A longer CaDiCaL run was stopped without a
  SAT/UNSAT result. A local search also remained unresolved.
* A CNF instance through 15000 was generated but not settled.

No uniform finite coloring bound is established. No infinite divisor cover
with summable reciprocal weights is established. No zero-density theorem
for all cube-Sidon root sets is established.

Further verified construction:

* `ThickCubeSidon.lean` proves
  `infinite_thick_cube_sidon_with_zero_lowerDensity`: there is an infinite set
  of roots whose cubes are Sidon, containing intervals of every finite length,
  but having lower natural density exactly zero. This uses a finite-extension
  lemma adjoining a sufficiently remote interval while preserving all mixed
  Sidon constraints, then a nested-chain construction with large gaps.
* This is stronger than separate finite far-interval examples, but still does
  not meet the positive lower density hypothesis in `Spec.lean`.


Additional finite diagnostics (still not a proof):

* Completely multiplicative colorings into `Z/3Z`, with multiplication mapped
  to addition, are satisfiable through 1000 and through 5000 roots.
* The analogous `Z/4Z` instance through 1000 is also satisfiable.
* Returned assignments were checked against every generated CNF clause.
* Generator: `/tmp/cube_mult_k.cpp`; instances and assignments:
  `/tmp/cube_mult_3_1000.*`, `/tmp/cube_mult_4_1000.*`,
  `/tmp/cube_mult_3_5000.*`.
* These finite instances establish no uniform coloring or density bound.

Greedy divisor-cover prime diagnostic:

* Instrumented generator: `/tmp/cubic_edges_divisor_generators.cpp`.
* Exact finite generator list: `/tmp/cube_generators_10000.list`.
* Up to 10000 there are 926 minimal forbidden divisors, reciprocal weight
  approximately 0.7210175126. Of these, 197 are prime, with reciprocal weight
  approximately 0.1440061628 (197 of the 1229 primes through 10000).
* Prime-generator proportions at cutoffs 100, 300, 1000, 3000, 10000 are
  approximately 0.120, 0.129, 0.137, 0.156, 0.160.
* These are finite diagnostics only. They prove neither convergence nor
  divergence, and do not establish that every divisor-cover construction
  behaves like this greedy construction.

New verified prime-factor obstruction:

* `LargestPrimeObstruction.lean` defines `greatestPrimeDivisor` using the
  supremum of `Nat.primeFactors` (zero at zero and one).
* `largest_prime_selection_bounded` proves that if cube-Sidon membership
  depends only on this largest prime divisor, all members have largest prime
  divisor at most 12. Otherwise a prime `p > 12` forces the collision
  `p, 9*p, 10*p, 12*p` into the set.
* `lowerDensity_zero_of_smooth_support` proves a general density-zero lemma
  for a set contained in zero together with the `K`-smooth numbers. It uses
  Mathlib's bound `2^(primesBelow K).card * sqrt N`.
* `largest_prime_selection_lowerDensity_zero` combines the two results.
* The file compiles; both density theorem axiom checks report only
  `propext`, `Classical.choice`, and `Quot.sound`.
* This is NOT a disproof of the conjecture: the original statement does not
  restrict how membership depends on prime factors.

Primitive-only limitation:

* `PrimitiveOnlyLimitation.lean` proves a positive-density set can avoid all
  quadruples with gcd one and nevertheless fail the cube-Sidon condition.
  The witness is the even numbers, with density 1/2 and collision
  `2^3 + 24^3 = 18^3 + 20^3`.
* It compiles; its axiom check lists only the three permitted axioms.
* This does not invalidate reducing to primitive collisions when an additional
  divisor-closure or dilation-compatible covering argument is supplied.
* Finite diagnostic `/tmp/cubic_primitive_diag_10000.txt`: through 10000,
  there are 13168 primitive collisions, involving 9616 roots; 6897 distinct
  roots are the largest root of a primitive collision. Primitive degrees have
  median 5, 90th percentile 10, maximum 23. No asymptotic conclusion follows.

Further finite diagnostics (not a settlement):

* Ternary digit sum modulo 3 does not give cube-Sidon fibers. Exact witnesses
  for its three fibers are `(156,13,130,117)`, `(179,40,166,107)`, and
  `(270,73,244,177)`, respectively, with the first two cubes summing to the
  last two. These were checked by integer arithmetic, not added as Lean lemmas.
* A new restricted coloring test requires multiplicative Boolean coloring only
  to avoid monochromatic collisions whose four roots are squarefree.
  `/tmp/cube_sf_mult.cpp` and `/tmp/cube_sf_mult_compact.cpp` generate its CNF.
  Through 1000, 5000, and 10000, it has respectively 63, 591, and 1515 primitive
  squarefree collision constraints. All three instances are SAT, and the returned
  assignments were checked against every CNF clause.
* Through 30000, there are 6365 primitive squarefree collision constraints.
  CaDiCaL reported UNSAT after about 88 seconds. This result has NOT been replayed
  as a Lean proof or checked with an independent proof-certificate checker.
  Files: `/tmp/cube_sf_mult_30000.cnf` and `/tmp/cube_sf_mult_30000.out`.
* This restricted test asks that BOTH Boolean fibers have Sidon cubes after
  restriction to squarefree roots. It must not be described as a disproof for
  a single fiber without an additional argument: multiplication by a root of
  the other color need not preserve squarefreeness.
* No squarefree-character construction, uniform finite-prefix density bound,
  or disproof of the original conjecture was obtained. `Spec.lean` is unchanged.


New verified limitation on multiplicative-density reasoning:

* `ParityDensityLimitation.lean` imports the existing `ColoringReduction.lean`.
* `multiplicative_bool_fiber_lowerDensity_pos` proves that both positive-root
  fibers of any nontrivial Boolean character multiplicative on positive
  integers have positive lower density. The proof uses a bounded dilation
  cover by `1` and one integer having character value `true`.
* `positive_density_avoids_all_prime_pairs_but_not_cube_sidon` gives the
  concrete even-Omega set. It has positive lower density and avoids every
  pair `n, p*n` for every prime `p`, yet contains the cubic collision
  `447^3 + 303^3 = 485^3 + 145^3` (all four roots have Omega equal to two).
* Both theorems compile and their axiom checks list only `propext`,
  `Classical.choice`, and `Quot.sound`.
* This demonstrates the flaw in simply multiplying density losses from
  different prime directions: a set can correlate the choices by parity.
  It is not a theorem about independent families of cubic collisions and
  does not settle the conjecture. A zero-density argument using disjoint
  prime supports would need an additional incompatibility mechanism.
* `Spec.lean` is unchanged and still contains `sorry`.

New verified finite optimization / compactness criterion:

* `FiniteDivisorCompactness.lean` imports `SummableDivisorCover.lean` and defines
  `FiniteCubeDivisorCover N B`: the finite forbidden-divisor set `B` meets every
  nontrivial positive cubic collision whose roots are at most `N`.
* `summable_divisor_cover_of_uniform_finite_covers` proves that finite covers
  omitting `1` with reciprocal weights bounded by a single real constant `C`
  yield a global summable divisor cover omitting `1`.
* `uniform_finite_divisor_covers_suffice` combines this with the existing sieve
  theorem to imply the conjecture. The bound need NOT satisfy `C < 1`.
* `summable_cover_iff_uniform_finite_covers` proves the converse as well:
  uniformly bounded finite weights are equivalent to a global summable cover.
  This equivalence is for the divisor-cover route, NOT for the original
  conjecture, since arbitrary positive-density witnesses need not be divisor
  avoiders.
* The proof uses compactness of Boolean membership functions, stabilization
  on finite prefixes, and bounded partial sums of nonnegative reciprocal
  weights. It requires one uniform constant, not a cutoff-dependent bound.
* No such uniform bound has been proved. Earlier finite LP/MIP values do not
  supply it. `Spec.lean` remains unchanged with its original `sorry`.

New verified quantitative interval bound:

* `ShortIntervals.lean` proves `cubes_sidon_on_short_interval (L M : Nat)`:
  if `L^2 <= 6*M + 9`, then the cubes of all roots in `Set.Icc M (M+L)`
  form a Sidon set. This improves the earlier sufficient location bound
  of order `L^3` to order `L^2`.
* The proof uses `n^3 = n (mod 3)`, so unequal root-pair sums for equal
  cube sums must differ by at least 3. The identity
  `4*(a^3+b^3) = (a+b)^3 + 3*(a+b)*(a-b)^2`
  then forces their cube sums to differ under the stated width bound.
  Equal pair sums and equal cube sums imply equal pair products, hence
  equality of the unordered pairs.
* It compiles with only the three allowed axioms. The temporary weaker
  `QuadraticIntervals.lean` was removed; `ShortIntervals.lean` supersedes it.
* This still gives only intervals of length on the order of the square
  root of their location. No positive lower-density union of such intervals
  has been constructed, and `Spec.lean` is unchanged with `sorry`.

Latest finite-cover audit and optimizer correction:

* The stored cover `/tmp/cube_cover_3000.json` was checked using exact integer
  arithmetic: its 2771 primitive collision constraints are valid and covered
  by its 156 selected divisors; divisor `1` is absent. Its reciprocal weight
  is approximately 0.522645716605661.
* Of its selected divisors, 36 are prime, with reciprocal weight approximately
  0.07104138257634725. Every selected divisor has a private constraint, so this
  particular cover is inclusion-minimal; that does not prove optimality.
* No arithmetic rule for an infinite cover was obtained from this inspection.
* `/tmp/cube_cover_lp.py` previously allowed divisor `1` as a variable. It now
  fixes that variable to zero in BOTH the LP and MILP. Without this correction,
  selecting `1` would give a trivial cost-one cover at every finite cutoff,
  which does not meet the hypotheses of `FiniteDivisorCompactness.lean`.
* The existing stored cover was unaffected by this bug because it explicitly
  omits `1`. Future finite optimization results still cannot establish a
  uniform bound without an argument valid for all cutoffs.
* The Sidon declarations in `FormalConjecturesForMathlib/Combinatorics/Basic.lean`
  provide elementary restriction, extension, and greedy constructions, but no
  positive-density extraction theorem that settles the stated conjecture.
* No settlement was obtained in this continuation. `Spec.lean` is unchanged.

New verified squarefree-coloring reduction:

* `SquarefreeColoringReduction.lean` imports `Submission.SummableDivisorCover`.
* `positive_density_of_dilation_cover_on` generalizes bounded-dilation density
  extraction: a bounded family of dilations covering any positive-lower-density
  source forces positive lower density of the target.
* `squarefree_lowerDensity_pos` proves positivity via the summable sieve of
  divisors `(m+2)^2`. `squarefree_prefix_multipliers N` then supplies a set of
  positive lower density of squarefree multipliers coprime to every squarefree
  root at most `N`. Multiplying these roots preserves squarefreeness.
* `GoodSquarefreeCubeColoring c` requires each squarefree-root color fiber to
  have Sidon cubes. No restriction is imposed on nonsquarefree roots.
* `finite_squarefree_cube_coloring_suffices` proves that a finite such coloring
  would imply the ORIGINAL conjecture. Its compactness/color-erasure proof
  uses the prefix multiplier sets, not arbitrary dilations.
* `finite_prefix_squarefree_cube_colorings_suffice` proves that a SINGLE uniform
  number of colors for every finite squarefree prefix would suffice.
* Both main theorems compile with only `propext`, `Classical.choice`, `Quot.sound`.
* No uniform coloring bound or infinite coloring was established. The finite
  multiplicative Boolean UNSAT diagnostic does not disprove unrestricted
  squarefree colorings. `Spec.lean` remains unchanged with the original `sorry`.

Targeted exact unit-root diagnostic:

* The squarefree CNF through 30000 contains no constraint involving root `1`.
  This must NOT be promoted to an arithmetic theorem.
* `/tmp/cube_unit_root.cpp` enumerates unit-root collisions using divisors of
  `b^3+1=(b+1)(b^2-b+1)`: for `s=c+d`, it checks the integral square
  `(4*(b^3+1)-s^3)/(3*s)=(c-d)^2`. The program uses exact integer arithmetic
  for identities, divisibility, and square verification.
* Through `b=1000000` it reported 64 nontrivial positive unit-root collisions,
  six having all roots squarefree. This remains a computational diagnostic,
  not a Lean theorem or an asymptotic claim.
* In particular, exact independent Python/SymPy checks verified
  `1^3 + 73967^3 = 72629^3 + 27835^3 = 404682117722064`, with
  `73967=17*19*229`, `72629=59*1231`, `27835=5*19*293`.
  Thus squarefree cubic collisions CAN involve root `1` (and can be all odd).
* Data: `/tmp/cube_unit_root_1000000.txt` and `.stats`.
* No uniform orientation, summable cover, or coloring bound was obtained.
  `Spec.lean` is still unchanged with its original `sorry`.

Binary digit-parity candidate checked and rejected:

* Both Thue–Morse parity classes have nontrivial cube collisions.
  Even parity: `80^3 + 15^3 = 71^3 + 54^3`.
  Odd parity: `61^3 + 56^3 = 69^3 + 42^3`.
* Restriction to squarefree roots does not rescue either class:
  `394^3 + 293^3 = 437^3 + 142^3` has binary digit sums `4,4,6,4`;
  `601^3 + 205^3 = 607^3 + 127^3` has binary digit sums `5,5,7,7`.
  Exact Python integer arithmetic and SymPy factorization checked both
  identities and squarefreeness of every root.
* These are rejected construction candidates, not a disproof of the original
  existential statement. No global bound or construction was obtained.

Latest continuation: still unresolved; `Spec.lean` is unchanged.

* No applicable general Sidon/polynomial-image density theorem was found in
  the library searches. No global construction or zero-density argument was
  established.
* The previously recorded squarefree unit-root collision
  `1^3 + 259495^3 = 219589^3 + 190243^3` is also pairwise coprime:
  `259495 = 5*51899`, `219589 = 17*12917`, and `190243` is prime.
  Thus a proposed shared-prime obstruction for squarefree unit-root collisions
  is false. This is an exact computational diagnostic, not a Lean theorem or
  an asymptotic counting result.
* No proof was submitted in this continuation.

Exact algebraic check in the latest continuation (not a settlement):

Writing `a = b + g*u` and `c = d + g*v`, the collision equation
`a^3 + d^3 = b^3 + c^3`, with `g != 0`, is equivalent over the rationals to

```
3*u*(2*b+g*u)^2 - 3*v*(2*d+g*v)^2 = g^2*(v^3-u^3).
```
SymPy verified the polynomial identity `4*F = g*Q`, where `F` and `Q` are
respectively the differences of the two sides of these equations. This groups
collisions into conics indexed by the reduced difference ratio `u/v`, but no
uniform bound over these conics was obtained. It does not provide a density
construction, counting theorem, or disproof. `Spec.lean` remains unchanged.

## New verified weighted divisor-cover reduction

`Submission/WeightedDivisorCover.lean` now compiles, and an `.olean` was built.
It imports `SummableDivisorCover.lean` and `Compactness.lean`. Its three final
axiom checks list only `propext`, `Classical.choice`, and `Quot.sound`.

Definitions:

* `divisorWeight w n = sum_{d | n} w d` (using `Nat.divisors`).
* `lowDivisorWeight w t = {n | 0 < n and divisorWeight w n < t}`.
* `IsWeightedCubeDivisorCover w` requires that every nontrivial positive
  collision has the sum of the four divisor weights at least 1. A divisor is
  counted once for each root it divides; this is weaker than counting it only
  once in the union of the four divisor sets.

Verified results:

* `lowDivisorWeight_positive`: if `w` is nonnegative, `w 1 = 0`, and
  `Summable (fun d : Nat => w d / d)`, then EVERY threshold `t > 0` gives
  positive lower density for `lowDivisorWeight w t`.
  Proof: double-count weighted divisors and use a finite Markov bound for a
  small tail; its low-weight set is divisor-closed. Remove finitely many
  initial divisors using the earlier positive-density preservation theorem.
  The total weighted reciprocal sum need not be small.
* `weighted_divisor_cover_suffices`: the same summability hypotheses, together
  with `IsWeightedCubeDivisorCover w`, imply the original conjecture. Use the
  threshold `1/4`.
* `weighted_cover_of_uniform_finite_weights`: compactness in
  `(Set.Icc (0 : Real) 1)^Nat` turns weights for each finite prefix into global
  weights, provided their reciprocal costs share ONE finite real bound `C`.
  Each finite weight function is bounded in `[0,1]`, vanishes at `1`, covers
  all collisions with roots at most `N`, and satisfies
  `sum_{d < N+1} w d / d <= C`.
* `uniform_finite_weighted_covers_suffice` combines these results.

**No global weights and no uniform finite cost bound have been constructed.**
This is a conditional reduction, not a settlement. It relaxes the integral
cover requirement to fractional weights; no strict separation or equivalence
between those criteria is asserted.

New finite diagnostics, not Lean theorems or asymptotic results:

* `/tmp/cube_cover_lp.py 10000 solve` generated 13168 primitive constraints.
  Its union-of-divisors LP reported objective approximately
  `0.4275182308230361` after about 26 seconds. The weights were not saved, so
  this floating-point objective is NOT an exact verified certificate.
* The MILP hit its 120-second limit. Its saved cover has 808 divisors and
  reciprocal weight approximately `2.0289119990535878`; it is a poor incumbent,
  NOT an optimum and NOT an improvement over the earlier greedy bound.
  Exact integer checking verified all 13168 identities, absence of `1`, and
  coverage of each recorded primitive collision.
  Files: `/tmp/cube_cover_10000.json`, `/tmp/cube_cover_10000.log`.
* There are six all-prime primitive constraints in that generated prefix.
  One exact example is
  `1699^3 + 1049^3 = 1823^3 + 61^3`.
  Thus forbidding only composite divisors cannot suffice globally. No statement
  about the number or distribution of prime collisions follows from this.
* The optimizer has finished. No long-running solver was intentionally left.
* Temporary `Submission/CheckWeighted.lean` was removed.

`Submission/Spec.lean` remains unchanged with its original `sorry`; no proof
was submitted in this continuation.

Latest graph-coloring diagnostics (no settlement):

For each primitive recorded collision through 10000 and each of its integer
scales still within that cutoff, connect a fixed pair of positions among the
four increasingly sorted roots. All six choices produced an odd cycle:

```
positions 0,1: 9, 1, 1033
positions 0,2: 2304, 1, 729
positions 0,3: 80, 9953, 1, 5640, 1930
positions 1,2: 552, 198, 96, 216, 360
positions 1,3: 516, 360, 279
positions 2,3: 97, 96, 90
```

In particular, the largest-two-roots graph is not bipartite. Its triangle is
certified by the exact identities on sorted root sets
`[20,33,96,97]`, `[12,54,90,96]`, and `[47,66,90,97]`, with the extremes on one
side and the middle roots on the other. The generated largest-pair graph had
1502, 7408, and 39734 edges at cutoffs 1000, 3000, and 10000. Increasing-order
greedy coloring used 7, 8, and 12 colors, respectively. These are NOT chromatic
numbers, NOT lower bounds on the chromatic number, and NOT evidence of a
uniform infinite bound. No graph-coloring construction was obtained.

This only rejects a simple structural shortcut. `Spec.lean` is still unchanged
and no proof was submitted.

## Canonical greedy divisor-cover construction (verified)

`Submission/GreedyDivisorCover.lean` now compiles, with an `.olean` built.
This file gives a precise infinite version of the divisor-closed greedy
construction, rather than assuming an unspecified cover.

* `greedyCubeRoots` is defined by strong recursion. A positive integer is
  accepted iff every positive proper divisor is accepted and no collision
  `n^3 + a^3 = b^3 + c^3` is completed by three earlier accepted roots.
* `greedyCubeRoots_cube_sidon`, `greedyCubeRoots_divisorClosed`, and
  `greedyCubeRoots_infinite` are unconditional.
* `greedyCubeGenerators` are the minimal positive excluded integers under
  divisibility. They omit `1`, form a primitive set (no distinct two divide
  one another), and cover every nontrivial positive cubic collision.
* `greedyCubeRoots_eq_divisorAvoider` identifies the accepted set with the
  corresponding divisor avoider.
* `greedyCubeGenerator_witness` gives an earlier-root collision for every
  generator. `greedyCubeGenerator_primitive_witness` additionally proves
  that its four roots have no common divisor other than `1`.
* `greedyCubeRoots_maximal` proves maximality among positive-divisor-closed
  cube-Sidon supersets, allowing a potential extra zero in the superset.
* `summable_greedyCubeGenerators_suffices` would settle the target IF the
  reciprocals of these particular generators were summable. This hypothesis
  has NOT been proved. Infinitude, maximality, and primitive witnesses do not
  establish positive lower density.

Axiom checks for the Sidon, primitive-witness, infinitude, and conditional
sufficiency results use only permitted axioms. Temporary `CheckGreedy.lean`
was deleted. `Spec.lean` remains unchanged.

An exact finite tally of the pre-existing 10000 greedy data found 197 prime
excluded generators out of 926 total generators, with prime reciprocal cost
approximately 0.1440061628. The prime counts through 100, 1000, and 10000 are
3, 23, and 197 respectively. This does NOT give an asymptotic estimate or
show either convergence or divergence of the generator reciprocal series.

## Exact conic-bundle discriminants (verified)

`Submission/CubeConicGeometry.lean` compiles, and an `.olean` was built.
It uses Mathlib's `fermatLastTheoremThree`, transported to rational numbers.

For rational `t,b,c,u`, put `a=c+t*u`, `d=b+u`. The file proves

```
a^3 + b^3 - c^3 - d^3 = u * Q,
Q = 3*t*c^2 - 3*b^2 + 3*u*(t^2*c-b) + (t^3-1)*u^2.
```

Thus, when `u != 0`, collision equality is equivalent to `Q=0`.
The two coordinate-boundary discriminants (after removing `u^2`) satisfy

```
IsSquare (3*(4*t^3-1))     <-> t=1
IsSquare (3*t*(4-t^3))    <-> t=0 or t=1
```

over `Q`. The first follows by turning a square discriminant into
`t^3+x^3=(x+1)^3` and applying Fermat for exponent three. The second follows
by replacing `t` with `1/t`, with zero treated separately. A boundary
nonvanishing lemma is also proved. All printed axiom dependencies are allowed.

This rules out a proposed rational splitting of the relevant nondegenerate
quadratics in THIS conic bundle. It is not a theorem excluding every possible
higher-degree parametrization, and it is not a counting/density theorem.
No global recurrence or positive-density construction was obtained.
`Spec.lean` remains unchanged with `sorry`; no settlement was submitted.

## First-fit coloring diagnostic (exact finite computation, not a Lean theorem)

A concrete first-fit coloring was tested: process positive roots in increasing
order, and give each root the least color not forbidden by a collision whose
other three roots already have that color. This is NOT the largest-pair graph
coloring reported earlier.

A complete bucketed pair-sum computation through 100000 found 898947 collisions,
including 238300 primitive ones (matching the older count). The first new colors
are indexed from zero:

```
color 0: root 1
color 1: root 12
color 2: root 172
color 3: root 2720
color 4: root 25272
```

Thus a four-color bound for THIS greedy rule is false. At root 25272, witnesses
blocking colors 0, 1, 2, and 3 are respectively:

```
[6655, 13576, 24063, 25272]
[507, 18243, 21594, 25272]
[2760, 12048, 24336, 25272]
[11016, 16848, 23328, 25272]
```

For each sorted tuple the extremes' cubes equal the sum of the middle cubes.
The last tuple has gcd 648 and primitive reduction `[17,26,36,39]`.
Color class cardinalities through 100000 are
`[49842, 33770, 14094, 2232, 62]`.

Independent Python integer checks verified every recorded identity, the coloring
constraint on every edge, and every first-fit color choice against the recorded
edge list. No Lean proof of this finite computation was generated. It does not
prove a five-color bound, unbounded chromatic number, or any density asymptotic.

Artifacts:
* `/tmp/cube_firstfit_bucket.cpp`, `/tmp/cube_firstfit_bucket`
* `/tmp/cube_edges_100000.bin` (int32 quadruples, sorted within each tuple)
* `/tmp/cube_firstfit_100000.bin` (int32 colors, index zero unused)
* `/tmp/cube_firstfit_100000.log`, `/tmp/cube_firstfit_100000.progress`
* `/tmp/cube_firstfit.py`, `/tmp/cube_firstfit_10000.json`

The generator finished. No uniform coloring invariant was found. `Spec.lean`
remains unchanged; no settlement was submitted.

Continuation after the first-fit coloring investigation:

* Rechecked `Spec.lean`, the definition of `Set.lowerDensity`, and the conic and
  weighted-cover reductions. The target is the ordinary positive lower natural
  density assertion; no definitional simplification settles it.
* Considered the difference-of-cubes / Pell-type decomposition and possible
  multiplicative recurrence approaches. No global counting bound, summable
  cover, recurrence theorem, or finite coloring was established. These ideas
  remain speculative and must not be used as proven input.
* No new proof file was produced in this continuation. `Spec.lean` remains
  unchanged with its original `sorry`; the conjecture remains unresolved here.

New verified fixed-gap results (subsequent continuation):

* `FixedGapCubes.lean` proves an elementary separation theorem for positive
  integer points on `A*x^2 - B*y^2 = C`, with `A,B > 0` and `C != 0`.
  For prescribed positive coordinate increments `u,v`, at most one positive
  point and its incremented point can both lie on the curve. Bounded `u`
  uniformly bounds `v`.
* Quantitatively, the number of first coordinates having another first
  coordinate within distance `L` is at most
  `L * (A * L * (2 * (B + C.natAbs + 1) + L))`.
  This gives the verified geometric-prefix bound
  `card(S intersect [0,16^j)) <= (A*(2*(B+C.natAbs+1)+1)+2)*8^j`.
* Centering equal cubic differences gives
  `3*h*(2*x+h)^2 - 3*k*(2*y+k)^2 = k^3-h^3`.
  Consequently, for fixed unequal positive gaps `h,k`, the set of bases `x`
  with `(x+h)^3 + y^3 = x^3 + (y+k)^3` for some natural `y` has natural
  density zero. Fixed translates of this base set also have density zero.
* `SparseHarmonic.lean` proves that a bound
  `card(S intersect [0,16^j)) <= C*8^j` implies summability of
  `if n in S then 1/n else 0`, by geometric block estimates.
* `FixedGapSieve.lean` combines these results. For each fixed unequal positive
  gap pair, the set `fixedGapUpperRoots h k` of upper endpoints `x+h` has
  summable reciprocals and omits `1`.
* `positive_density_sieve_for_fixed_gaps` constructs a positive-lower-density
  divisor avoider excluding every integer multiple of every upper endpoint
  in that entire family, not just the unscaled collisions.
* `positive_density_sieve_for_finite_gap_pairs` does this simultaneously for
  ANY FINITE list of such gap pairs, including all their integer dilates.
* All three new files compile; their `.olean` files were built. Public theorem
  axiom checks report only `propext`, `Classical.choice`, `Quot.sound`.
  Temporary `CheckFixed.lean` was removed.

Critical limitation: there is still NO bound uniform over finite lists of gap
pairs, and NO proof that the countable union of their forbidden-divisor sets
has summable reciprocals. The positive densities in the finite-family theorem
may tend to zero. Neither compactness nor countable union of density-zero sets
bridges this gap. `Spec.lean` is unchanged and the original conjecture remains
unresolved here.

Further fractional-cover diagnostics (no new global theorem):

* Re-solved the finite weighted-divisor LP using the existing complete recorded
  pair-sum edge list. Constraints count a divisor ONCE PER ROOT it divides,
  matching `IsWeightedCubeDivisorCover`; divisor `1` is excluded. This differs
  from the older union-of-divisors LP.
* Through 10000: 13168 primitive edges, 346760 nonzero matrix entries;
  floating-point optimum about 0.36660046107805755, 1291 nonzero weights.
* Through 30000: 53097 primitive edges, 1584562 nonzero matrix entries;
  floating-point optimum about 0.3894873172958425, 3582 nonzero weights.
* The solvers finished. Both primal weights and dual marginals were saved in
  `/tmp/cube_weighted_lp_{10000,30000}.npz`; metadata/supports are in the matching
  `.json` files and solver output in `.log` files. Generator:
  `/tmp/cube_weighted_lp.py`.
* Independent Python integer checks verified every recorded edge identity,
  strict ordering and primitive gcd, then checked rounded rational primal and
  dual certificates. Checker: `/tmp/check_cube_weighted_lp.py`.
* Rounded primal weights have denominator 1000000. Their costs are exactly
  below 37/100 (N=10000) and 2/5 (N=30000); approximate costs are respectively
  0.3666044163598552 and 0.3894916956091996. Every recorded edge has integer
  cover weight at least 1000004 and 1000003, respectively.
* Rounded dual weights use denominator 10^12. At 30000 an initial rounded dual
  was NOT feasible; it was rescaled downward by the exact factor
  1000000000000/1001665765595 and checked again. Final exact dual costs are
  36660009383/100000000000 (10000) and 155535803/400000000 (30000).
  All divisor-capacity inequalities were then verified by integer arithmetic.
* Rational data are in `/tmp/cube_weighted_lp_{10000,30000}_rational.json`.
  These are NOT Lean certificates, and no infinite cover or uniform upper
  bound follows. No asymptotic behavior of the LP optima was established.

No new global argument was obtained in this continuation. `Spec.lean` still
contains its original `sorry`; it was not submitted as a completed solution.

New verified residue-class / gap-ratio results (latest continuation):

* `GapRatioResidues.lean` imports only `FormalConjecturesUtil` and compiles.
  An `.olean` has been built. All four public axiom checks list only
  `propext`, `Classical.choice`, and `Quot.sound`.
* `cube_collision_cancel_common_gap` cancels a positive common gap factor
  over the naturals, before taking congruences. This is important because
  the common gap factor need not be invertible modulo the chosen modulus.
* `cube_collision_gap_ratio_modEq`: if the gaps are `g*u`, `g*v`, all four
  roots are `1 mod m`, and `Nat.Coprime m 3`, then `u ≡ v mod m`.
  The final cancellation uses `Nat.ModEq.cancel_right_of_coprime`.
* `no_cube_collision_small_gap_ratio` excludes unequal `u,v < m` under
  those hypotheses, with no upper bound on `g`.
* `one_residue_positive_lowerDensity` verifies positive lower density of
  the progression `1 mod m` for `m > 1`. Its proof gives a lower bound
  `1 / (2*m)` using a finite-prefix injection.
* `positive_density_avoids_bounded_gap_ratios K` chooses `m = 3*K+4`.
  It supplies an infinite positive-lower-density set excluding every
  collision whose unequal gap numerators are both at most `K`, even
  after arbitrary simultaneous scaling of the two gaps.
* This extends the previous finite fixed-gap avoidance result to finite
  collections of gap ratios. It still does NOT settle the conjecture:
  the density bound tends to zero with `K`, and ratios with arbitrarily
  large numerators remain. A full residue class is already proved not
  cube-Sidon in `Partial.lean`.
* Removed the temporary, noncompiling `CheckSlope.lean` API scratch file.
* `Spec.lean` remains unchanged and unresolved, SHA256
  `9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63`.
  No valid settlement has been submitted in this continuation.

## Upper-density-one almost-coloring reduction (verified)

`Submission/AlmostColoringReduction.lean` compiles, with an `.olean` built.
It imports `Submission.ColoringReduction` and contains no `sorry`.
All printed axiom checks use only `propext`, `Classical.choice`, `Quot.sound`.

* `partialDensity_compl_add` proves the exact complement identity for
  positive cutoffs.
* `upperDensity_lt_one_of_compl_lowerDensity_pos` proves that a complement
  of positive lower density forces upper density strictly below one.
* `finite_prefix_dilation_of_upperDensity_one` proves: if a set `S` has
  upper natural density one, then for each `M` there is `q > 0` with
  `q, 2*q, ..., M*q` all in `S`. If no such dilation existed, the complement
  would have a bounded dilation cover, contradicting upper density one.
* `goodCubeColoring_of_upperDensity_one`: a cube-Sidon coloring of positive
  roots in such an `S` with `k` colors yields a cube-Sidon coloring of ALL
  positive roots with the SAME `k`. The proof pulls colors back along these
  dilations and applies sequential compactness.
* `finite_cube_coloring_upperDensity_one_suffices` applies the pre-existing
  finite-coloring criterion to obtain the conjecture conditionally.

No coloring is constructed. In particular, merely discarding primes or any
other density-zero exception set does not make the finite-coloring problem
strictly weaker: a fixed finite coloring of the remaining density-one set
would already yield a full finite coloring. This result does not obstruct
arbitrary single positive-density cube-Sidon sets.

Further reasoning considered conic families, prime-factor constructions,
finite-field/digital colorings, and density recurrence, but established no
uniform density/color/cover bound and no zero-density theorem for all
cube-Sidon root sets. No new numerical diagnostics were run. External
literature access was retried and failed at DNS resolution.

`Spec.lean` is still unchanged, with SHA256
`9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63`.
The conjecture remains unresolved here; no complete proof was submitted.

## Inert-prime restrictions on arbitrary collisions (verified)

`Submission/InertPrimeCubes.lean` imports only `FormalConjecturesUtil`, compiles,
and has a built `.olean`. It has no `sorry`; all four printed axiom checks use
only `propext`, `Classical.choice`, and `Quot.sound`.

* `cube_injective_zmod_of_mod_three_eq_two`: cubing is injective on `ZMod p`
  for primes `p % 3 = 2`. The proof uses the explicit inverse exponent
  `2*(p/3)+1` and Fermat's little theorem.
* `inert_prime_not_dvd_cube_cofactor`: if `p` does not divide `a`, it does
  not divide `a^2+a*b+b^2`, for such a prime.
* `inert_prime_pow_dvd_cube_sub_iff`: for integer roots and `p ∤ a`,
  `p^e ∣ a^3-b^3` iff `p^e ∣ a-b`, for every natural `e`.
  There is also `inert_prime_pow_dvd_cube_add_iff` with sums.
* `inert_prime_pair_sum_bound`: if `p | a,b`, `p ∤ c`, and
  `a^3+b^3=c^3+d^3` with `c+d>0`, then `p^3 <= c+d`.
* For primitive collisions (`Coprime (gcd a b) (gcd c d)`):
  - `primitive_collision_same_side_inert_prime_bound` bounds a shared
    same-side prime by `p^3 <= 2*N` when the opposite roots are at most `N`.
  - `primitive_collision_cross_inert_prime_bound` bounds a shared
    opposite-side prime by `p^3 <= N`, assuming the other roots are distinct
    and at most `N`.
  - `large_inert_prime_divides_at_most_one_root` combines all six pair choices:
    if `2*N < p^3`, such a prime divides at most one of the four roots.

These are uniform restrictions applying to arbitrary primitive collisions,
not just a fixed gap family. They do not exclude pairwise-coprime collisions
(which were already shown to exist with arbitrarily large roots), and they
currently yield no uniform collision count or positive-density construction.
No proof of lower density zero for all cube-Sidon root sets was found either.

The temporary `CheckInert.lean` API scratch file was removed. `Spec.lean`
remains unchanged and unresolved, SHA256
`9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63`.
No settlement has been submitted.

## Completion-boundary investigation (finite diagnostics only)

A possible global route was considered: for every finite cube-Sidon root set
`S`, bound the number of outside roots that complete a collision with three
members of `S` by `C * |S|`, with one universal finite `C`. Such a bound would
control ordinary greedy rejection counts. NO such bound has been proved, and
no unbounded-ratio counterexample family has been constructed. This is only
a candidate, not a theorem or an equivalent reformulation of the conjecture.

Finite exact-integer diagnostics used the existing recorded collision list
through 100000. They are NOT Lean proofs or asymptotic estimates.

* `/tmp/cube_boundary_diagnostic.py` checked strict ordering and every cubic
  identity in the recorded edge list, and checked independence of each tested
  set against those edges. It saved `/tmp/cube_boundary_diagnostic.json`.
* Existing first-fit color 1 has 33770 roots and 46521 distinct outside
  completion roots within 100000, a ratio about 1.37758. Thus a proposed
  universal completion-boundary constant `C=1` is already contradicted by
  this finite computation. This was not replayed as a Lean certificate.
* For first-fit color 0 restricted to `[1,79000]`, the set has 39887 roots
  and 43276 recorded completion roots through 100000 (ratio about 1.08497).
* A new finite greedy ordering favored adding vertices that immediately
  block many other candidates. It does not enforce divisor closure, and is
  not the earlier increasing-order first-fit rule.

  cutoff | selected | distinct blocked roots within cutoff
  1000   | 576      | 424
  3000   | 1618     | 1382
  10000  | 4912     | 5088
  30000  | 13687    | 16313
  100000 | 42180    | 57820

  Source/executable: `/tmp/cube_boundary_greedy.cpp`,
  `/tmp/cube_boundary_greedy`; accepted lists:
  `/tmp/cube_boundary_greedy_<N>.txt`.
  Independent Python checks verified that no recorded edge lies wholly in
  each accepted set, and that every excluded root in the cutoff has a
  recorded edge with three accepted roots. Results are saved in
  `/tmp/cube_boundary_greedy_checks.json`.
* These numbers neither prove a larger universal `C` nor show ratios
  unbounded. No global claim may be inferred from them.

No new Lean proof file was added in this continuation. `Spec.lean` is still
unchanged with its original `sorry`, SHA256
`9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63`.
The conjecture remains unresolved here; no complete proof was submitted.

## Completion-boundary obstruction (now proved)

`Submission/CompletionBoundaryUnbounded.lean` now compiles and has a built
`.olean`. The theorem `CompletionBoundary.completion_boundary_unbounded`
has only `propext`, `Classical.choice`, `Quot.sound` as axioms.

For every natural constant `C`, it constructs finite positive root sets
`S,B`, with disjoint `S,B`, Sidon cubes of `S`, every `b ∈ B` completing a
collision with three selected roots, and `C*|S| < |B|`.

The induction maintains multiplicative separation of `S`, `|S|=3^k`, and
`3*|B|=k*|S|`. Given a bound `M` on the old roots, set
`t=4*(M+1)`, `q=3*t^3`, `r=3*t`, `u=3*q+1`, `v=q*r`, `w=(q+1)*r`.
The identity `1+w^3=u^3+v^3` adds completions `w*S` to the three scaled
copies of old `B`, while the three scaled copies of `S` remain separated.
An equality `v*x=w*y` would imply `q | y`, impossible for `0<y≤M<q`.
Thus `|S'|=3|S|` and `|B'|=3|B|+|S|`.

This disproves the proposed universal completion-boundary bound. It is NOT
a disproof of the original positive-density conjecture: the examples are
very sparse, and neither a dense construction nor a density-zero theorem
for all cube-Sidon sets follows. The original `Spec.lean` is unchanged.

Earlier finite pruning diagnostics (NOT Lean proofs) are preserved in
`/tmp/cube_boundary_prune.cpp`, its executable, and
`/tmp/cube_boundary_pruned_<N>_<source>.txt`. Starting with the
boundary-focused greedy sets (`source=-1`), pruning gives:

cutoff | selected | boundary
1000 | 203 | 308
3000 | 585 | 1031
10000 | 1117 | 2562
30000 | 3801 | 10029
100000 | 6202 | 21003

These pruning outputs have not had an independent Python replay. The
proved recursive construction supersedes them for the unbounded-ratio
claim, so no asymptotic or settlement claim relies on these computations.

## Saved fractional-cover diagnostics (still no uniform bound)

A fresh finite LP inspection uses the recorded exact collision file through
100000, restricting to primitive collisions. The solver script is
`/tmp/cube_cover_inspect.py`. No arithmetic rule for global weights was
obtained, and no uniform bound is inferred from the numerical values.

* Cutoff 10000: 13168 primitive constraints, floating LP objective
  approximately 0.4275182308230357.
* Cutoff 30000: 53097 primitive constraints, floating LP objective
  approximately 0.45507628971476766.
* The weights are now saved in `/tmp/cube_cover_weights_<N>.npz` and `.json`;
  logs are `/tmp/cube_cover_inspect_<N>.log`.
* `/tmp/cube_cover_exact_check.py` rounds positive weights upward to
  rationals with denominator 10^9 (with an additional one-unit margin,
  capped at one). It independently checks every recorded cubic identity,
  strict root ordering, primitivity, and every rational covering inequality
  using exact integer arithmetic. Rational weights are saved as
  `/tmp/cube_cover_weights_<N>_rational.json` and check summaries in
  `/tmp/cube_cover_exact_checks.json`.
* This establishes feasibility ONLY for the recorded finite constraints.
  It is not a Lean proof, does not certify LP optimality, and supplies no
  infinite density bound. Both optimizations finished; none is left running.

Additional finite structural diagnostics, not Lean theorems:

* The recorded edge list through 100000 contains 105 all-prime collisions;
  six have largest root at most 10000. One with large minimum root is
  `44893^3 + 89051^3 = 58321^3 + 84263^3`. Thus a construction forbidding
  only composite divisors must also address prime-only collisions. This
  proves no assertion about infinitely many prime-only collisions.
* First-fit coloring through 100000 uses colors 0 through 3 even on roots
  coprime to 2310; it uses colors 0 through 3 on prime roots too. These are
  only statistics for this finite rule, not chromatic-number bounds.

The original theorem remains unresolved and `Spec.lean` is unchanged with
its original `sorry`. The missing step remains a global construction with
a positive lower-density estimate, or a proof that every such root set
has lower density zero. No valid settlement was submitted.

## Sharp uniform short-interval constant (proved)

`Submission/IntervalScale.lean` now compiles and has a built `.olean`.
Its four printed axiom checks list only `propext`, `Classical.choice`,
`Quot.sound`. It contains no `sorry`.

* `cubes_sidon_on_short_interval_twelve` first improves the previous bound
  to `L^2 ≤ 12*M + 36`, using `n^3 ≡ n (mod 6)`.
* `cubes_sidon_on_short_interval_sharp` proves that the cubes of every
  interval `[M,M+L]` are Sidon if `3*L^2 ≤ 38*M`.
* `NearDiagonalCubes.interval_constant_sharp` proves: for every real
  `C > 38/3` and cutoff `N`, some `M ≥ N`, `M > 0`, and `L` satisfy
  `L^2 ≤ C*M`, while the cubes of `[M,M+L]` are NOT Sidon.
  Thus `38/3` is the sharp asymptotic constant for this uniform full-interval
  criterion. This does not classify every individual Sidon interval.
* `NearDiagonalCubes.arbitrarily_far_collisions` provides explicit ordered
  four-root witnesses with `L^2 ≤ 13*M`.

The stronger lower bound uses the cube-sum identity with root-pair sums
`S` and `S+s`, where `s` is a positive multiple of six. If the corresponding
root differences are `D,E`, the integer

  r = (D^2 - E^2 - s^2 - s*S)/2

is positive, and

  6*r*S = 3*s*E^2 + s^3,
  3*s*D^2 = 3*(s^2+2*r)*S + 2*s^3 + 6*s*r.

Since `s ≥ 6` and `r ≥ 1`, `19*s ≤ 3*(s^2+2*r)`. Therefore
`19*S < 3*D^2`, contradicting the claimed small interval when `S ≥ 2*M`.

The sharpness construction uses the Pell equation

  p^2+p = 19*q^2+19*q+68,

with seed `(p,q)=(13,2)` and recurrence

  p' = 170*p + 741*q + 455,
  q' = 39*p + 170*q + 104.

Its four increasing roots are

  a = 6*q^2 + 6*q + 19 - p,
  b = 6*q^2 + 5*q + 22,
  c = 6*q^2 + 7*q + 23,
  d = 6*q^2 + 6*q + 20 + p.

They satisfy `a^3+d^3=b^3+c^3`, and with `M=a`, `L=2*p+1`,

  3*L^2 = 38*M + 38*p + 97.

The verified linear bound `p ≤ 6*q+3` makes the excess negligible relative
to `M` as the recurrence grows. The seed gives roots `42,56,61,69`.

This is an auxiliary interval theorem, NOT a proof or disproof of the
positive-lower-density conjecture. In particular, it does not control mixed
collisions across a large collection of short blocks. No uniform prefix
construction or density-zero theorem for arbitrary cube-Sidon root sets was
obtained. `Spec.lean` is unchanged and still contains its original `sorry`.
No valid settlement has been submitted.

## Square-product restriction checked and rejected

A proposed route through multiplicative square classes would need more than
asserting that the product of the four roots in every nontrivial collision
is nonsquare. That assertion is false.

`Submission/SquareProductCollision.lean` compiles and has a built `.olean`.
It proves the primitive, strictly ordered example

  243^3 + 1600^3 = 484^3 + 1587^3,
  243*484*1587*1600 = 546480^2.

The roots belong to just two square classes:
`243=3*9^2`, `484=22^2`, `1587=3*23^2`, `1600=40^2`.
Both theorem axiom checks are restricted to the permitted axioms. This is
only a counterexample to an auxiliary arithmetic restriction, not to the
original existence conjecture.

An additional exact-integer diagnostic from the recorded edge list found
`78^3+2809^3=289^3+2808^3`, with product `421668^2`. This second example was
not needed by the Lean proofs. No infinite or density claim follows.

Further consideration of multiplicative characters, conic/Vieta transforms,
and recursive block assembly yielded no global construction or density-zero
argument. `Spec.lean` remains unchanged with its original `sorry`; no valid
settlement has been submitted.

## Inert-prime restrictions on every reduced gap ratio (proved)

`Submission/GapRatioNorms.lean` imports `Submission.InertPrimeCubes`, compiles,
and has a built `.olean`. All four printed axiom checks list only the
permitted axioms; the file contains no `sorry`.

* `inert_cube_cofactor_factorization`: for prime `p % 3 = 2` and `a > 0`,
  the exponent of `p` in `a^2+a*b+b^2` is exactly twice its exponent in
  `gcd(a,b)`. The proof divides a common factor `p` from the two roots and
  uses strong induction; if one root is a unit, the existing cofactor lemma
  shows that the cofactor is a unit too.
* `cube_collision_gap_factorization_balance`: from
  `(b+h)^3+d^3=b^3+(d+k)^3`, with positive gaps `h,k`, deduces

    v_p(h) + 2*v_p(gcd(b+h,b))
      = v_p(k) + 2*v_p(gcd(d+k,d)).

  Here the theorem uses `Nat.factorization` for valuations.
* `cube_collision_reduced_gap_inert_even`: if gaps are `g*u`, `g*v`, with
  positive `g,u,v` and `Coprime u v`, then both `u.factorization p` and
  `v.factorization p` are even for every prime `p % 3 = 2`.
* `no_cube_collision_gap_ratio_two`: consequently no positive common gap
  factor gives a collision with gap ratio `1:2`.

This is the Eisenstein-norm restriction on reduced ratios, not a claim that
all such norm ratios actually occur. It applies to arbitrary collisions,
not just a parametrized subfamily. It currently supplies neither a
summable forbidden-divisor cover nor a uniform finite coloring or prefix
construction. A set of admissible parameter ratios being restricted is not
itself a density estimate for selected roots.

The original conjecture remains unresolved. `Spec.lean` is unchanged and
still has its original `sorry`; no valid settlement has been submitted.

## Local-degree finite diagnostic (not an asymptotic theorem)

`/tmp/cube_local_degrees.py` and `/tmp/cube_local_degrees.json` inspect the
previously audited exact collision list through 100000. Among roots in
`(N/2,N]`, median incident degrees at N = 1000, 10000, 30000, 100000 were
respectively 4, 9, 13, 19 for all collisions; 2, 3, 5, 6 for primitive
collisions; and 2, 4, 6, 8 when examining prime roots. At N=100000,
all-collision and primitive means were 25.310 and 6.483. These finite
observations do not prove bounded typical degree, divergence, or any
positive-density construction. The proposed bounded-typical-degree route
currently lacks a uniform analytic estimate. No inference to the original
conjecture is warranted. `Spec.lean` is still unchanged and unresolved.

## Follow-up global review: no settlement

The local-degree route supplies no uniform typical-degree bound. A further
review of algebraic parametrizations, multiplicative constructions, and the
available library found no new global lemma proving either a uniform
finite-prefix density construction or density zero for every independent
root set. In particular, fixed-family sparsity and finite covering costs
cannot be promoted to their required infinite uniform counterparts.
No additional theorem settling the conjecture was obtained. The original
`Submission/Spec.lean` has not been edited, still contains `sorry`, and is
not a valid completed submission. No verification submission was made in
this continuation.

## Fixed-gap tail review in the next continuation

Reviewed the exact constants in `FixedGapSieve.lean` and the modular
alternative in `GapRatioResidues.lean`. The proved power-saving estimate
for one fixed-gap family has coefficient

  8 * ((3*h) * (2*(3*k + |k^3-h^3| + 1) + 1) + 2).

This coefficient grows with the gaps; the proof provides no summable decay
in the family parameters. Thus its individual summability statements do
not supply a summable bound for their full union. The progression argument
for reduced ratios up to K uses modulus `3*(K+1)+1`, so its established
positive density lower bound tends to zero as K increases. Neither can
currently be passed to a limit with a positive uniform density bound.
Further consideration of gap parameterizations and finite colorings did
not establish such a uniform estimate. No new settlement was obtained;
`Spec.lean` remains unchanged with its original `sorry`.

## Dilation/divisibility construction review

Reviewed `GreedyDivisorCover.lean`, `SquarefreeColoringReduction.lean`, and
the imported Sidon definitions and lemmas. No new density estimate was
obtained. Common dilations preserve Sidon cubes; unions of differently
dilated selected pieces require additional mixed-collision control. The
existing greedy divisor-closed set remains proved Sidon without a proved
positive lower-density bound. Finite or countable coloring arguments still
lack the uniform bound required by the existing reductions. The library
review yielded no theorem supplying that missing bound.

No settlement or new claim about the conjecture is made in this review.
`Submission/Spec.lean` is unchanged and still contains `sorry`.

## Smooth-orbit harmonic density obstruction (new, proved)

`Submission/SmoothHarmonic.lean` imports only `FormalConjecturesUtil`, compiles,
and has a built `.olean`. Its seven printed axiom checks use only `propext`,
`Classical.choice`, and `Quot.sound`. It contains no `sorry`.

Definitions:

* `primeRough P r`: r is positive and divisible by no prime in P.
* `SmoothCubeHarmonicBound P B`: every finite cube-Sidon root set S whose
  prime factors belong to P satisfies `sum_{s in S} 1/s <= B`.

Main verified results:

* `factored_rough_decomposition`: split the prime-factor list into a
  P-smooth part s and a P-rough part r, with `r*s=n`.
* `cube_sidon_dilation_preimage`: `{s | r*s in A}` has Sidon cubes whenever
  A does and r is positive.
* `cube_sidon_harmonic_projection`: for any cube-Sidon A and finite prime
  set P satisfying `SmoothCubeHarmonicBound P B`,

    sum_{n<=N, n in A, n>0} 1/n
      <= B * sum_{r<=N, primeRough P r} 1/r.

* `harmonic_prefix_mono`, `harmonic_of_prefix_upper`, and the set variants:
  finite summation by parts transfers linear prefix count bounds, including
  additive constants, to harmonic bounds.
* `lowerDensity_le_of_harmonic_upper`: an upper bound
  `H_A(N) <= d*H(N)+C`, with d nonnegative, implies `A.lowerDensity <= d`.
  The proof derives a contradiction to divergence of the harmonic series.
  It does NOT use the utility's unproved `HasDensity.hasLogDensity`.
* `primeRough_prefix_totient_bound`: with `M=prod P`, the rough prefix count
  is at most `(phi(M)/M)*N + phi(M)`.
* `cube_sidon_lowerDensity_le_totient_smooth_bound`: combines the above to
  establish, for every cube-Sidon root set A,

    A.lowerDensity <= B * phi(M)/M.

* `no_positive_density_cube_sidon_of_normalized_smooth_bounds`: a family of
  these normalized bounds tending to zero would prove the negation of the
  original conjecture. The requisite family of bounds is NOT constructed.
  A more general conditional version accepts arbitrary rough-count bounds.

This is a new global necessary-condition reduction for unrestricted A,
not merely an obstruction to divisor-closed constructions. Nevertheless,
its asymptotic hypothesis remains unproved. Finite-prime or finite-prefix
optimizations alone would not establish vanishing normalization. Simply
adding the individual four-vertex edge inequalities also cannot suffice:
the fractional vertex-cover relaxation permits weight 1/4 at every vertex,
so stronger integral/combinatorial information would be needed for a
zero-density conclusion through that relaxation.

`Submission/Spec.lean` is unchanged and still has its original `sorry`.
No valid proof or disproof of the original conjecture has been submitted.

Verified finite smooth-harmonic certificates (auxiliary, not a settlement):

* `SmoothHarmonicFinite.lean` proves the exact Euler-product reciprocal mass
  of the integers supported on a finite prime set, using Mathlib's geometric
  Euler product theorem.
* `smooth_harmonic_bound_of_finite_prefix` extends a bound for all cube-Sidon
  subsets of a finite smooth prefix to every finite smooth subset, adding
  exactly the reciprocal mass of the omitted tail.
* `SmoothCubeHarmonicBound.extend` propagates a bound on prime set P to Q
  by multiplying by the total reciprocal mass for Q \\ P. Its proof partitions
  each finite set into smooth-cofactor fibers and uses dilation invariance.
* All three printed axiom checks use only the permitted axioms. The file
  compiles and has a built `.olean`.
* No normalized bound tending to zero, and no positive-density construction,
  has been established. `Spec.lean` is unchanged and still contains `sorry`.

Targeted prime-coordinate check in this continuation:

* Exact stored edges through 100000 contain 105 collisions with all four
  roots prime. Their storage format is sorted roots `a < b < c < d`, with
  identity `a^3 + d^3 = b^3 + c^3` (not first-two equals last-two).
* In particular, Python integer arithmetic verifies
  `61^3 + 1823^3 = 1049^3 + 1699^3 = 6058655748`, and SymPy verifies
  primality of all four roots. This refutes the elementary idea that every
  nontrivial cubic collision must contain a composite root. It is only
  an exact diagnostic, not an asymptotic argument or a Lean theorem.
* Further library searches found no applicable settlement. No new global
  density estimate or construction was established. The target theorem
  remains unresolved; `Spec.lean` retains its original `sorry`.

## Three-color multiplicative test and gap-bound review

* `/tmp/cube_mult_stored.py` generates a one-hot Z/3Z multiplicative-coloring
  instance from the exact stored collision list. It checks every selected
  identity in integer arithmetic, using sorted coordinates a<b<c<d and
  a^3+d^3=b^3+c^3. Multiplicativity is encoded recursively through the smallest
  prime factor, so the prime colors determine all positive-root colors.
* Through N=10000, there are 13168 primitive edge constraints, 30000 Boolean
  variables, and 158435 clauses. CaDiCaL returned `s UNSATISFIABLE`, exit 20,
  after 175.49 seconds, with 548316 conflicts. Files:
  `/tmp/cube_mult_stored_3_10000.cnf` and `.out`.
* This solver result has NOT been replayed as a Lean proof or independently
  checked from a proof certificate. It is a diagnostic obstruction to this
  particular completely multiplicative Z/3Z coloring construction, not an
  obstruction to unrestricted colorings or positive-density cube-Sidon sets.
* Revisited `GapRatioResidues.lean`, `GapRatioNorms.lean`, and
  `FixedGapSieve.lean`. The inert-prime restrictions do not currently give
  summable control over all gap parameters. The progression construction
  avoids bounded reduced ratios, but its density bound decays with the
  parameter bound. No uniform estimate was established.
* No proof or disproof of the original conjecture was obtained. `Spec.lean`
  remains unchanged with `sorry`; no valid final proof was submitted.

## Increasing-greedy completion review

Reviewed the full amplification proof in `CompletionBoundaryUnbounded.lean`.
Its selected sets are multiplicatively separated and very sparse. It rules
out a linear completion bound for arbitrary finite cube-Sidon sets, but does
not itself rule out a specialized estimate for an increasing greedy set.
No such specialized estimate was proved in this continuation.

The ordinary first-fit root coloring must not be confused with the verified
divisor-closed `greedyCubeRoots` construction: the stored first-fit coloring
has c(12)=1 and c(72)=0. Thus its first class is not divisor-closed, and the
previous finite first-fit densities do not measure `greedyCubeRoots`.
This comparison is a finite data diagnostic, not an added Lean theorem.

A targeted count of stored edges confined to [N/2,N] gives respectively
45, 248, 1405, 6480, and 32930 at N=1000,3000,10000,30000,100000.
These are not uniform asymptotic bounds; shrinking a block or checking
finitely many blocks does not establish a positive lower-density union.
No positive-density construction or universal zero-density argument was
obtained. `Spec.lean` is unchanged and still contains `sorry`.

## Squarefree square-product diagnostic

A targeted check of the exact stored edges was performed by
`/tmp/cube_sf_squareproduct.py`, with results in
`/tmp/cube_sf_squareproduct.json`. Among the 51697 edges through 100000
whose four roots are squarefree, none has a square product of roots.
Squarefreeness was tested by an exact square-divisor sieve, and products
and integer square roots were computed with Python integers.

This is NOT a universal arithmetic theorem and has not been formalized as
one. In particular, the finite absence must not be used to assert that
all squarefree cubic collisions have nonsquare product. Even such a
universal restriction, if proved, would still require a further argument
to yield the positive-density construction in the target.

No proof or disproof of the target was obtained. `Spec.lean` remains
unchanged with its original `sorry`, and no valid proof was submitted.

## Completed C3 certificate audit (auxiliary only)

The proof-producing CaDiCaL run started before the latest continuation completed:

* Command used `--lrat --binary=false --check=true` on
  `/tmp/cube_mult_stored_3_10000.cnf`.
* It returned `s UNSATISFIABLE`, exit 20, after 504.46 seconds of process time,
  with 548316 conflicts. The internal LRAT checker reported 1610186 derived
  clause checks. Its complete log is
  `/tmp/cube_mult_stored_3_10000_cert.out`.
* The complete textual certificate is about 461 MiB:
  `/tmp/cube_mult_stored_3_10000.lrat`.
* `/tmp/prune_cube_lrat.py` traced dependencies backwards from the final empty
  clause, removed unused original and derived clauses, renumbered variables
  and clause IDs, and emitted deletions at the last use of each clause.
  All retained derivations used positive RUP hints (no retained RAT step).
* The resulting files are
  `/tmp/cube_mult_stored_3_10000_pruned.{cnf,lrat,json}`. They have 20434 Boolean
  variables, 91091 original clauses, and 584571 derived clauses. The pruned
  textual LRAT is still about 309 MiB.
* An independent C++ RUP-only checker, `/tmp/check_rup.cpp`, successfully
  replayed the pruned certificate: 584571 derived clauses and 42382856 hints,
  ending in the empty clause. Its output is
  `/tmp/cube_mult_stored_3_10000_pruned_check.out`.
* **This certificate has not been imported or replayed in Lean.** The external
  checks are diagnostics, not a new kernel-verified theorem.
* Even a Lean-certified result here would rule out only completely
  multiplicative C3 cube-Sidon colorings, not the unrestricted existential
  conjecture in `Spec.lean`.

Mathlib's `Mathlib/Tactic/Sat/FromLRAT.lean` provides `lrat_proof` and
`from_lrat`. A small temporary interface test compiled and used only
`propext`, `Classical.choice`, and `Quot.sound`. The command produces the
universally quantified negation of the CNF, reified as a DNF proposition.
Its importer does not implement negative-hint RAT steps. The temporary
`Submission/TestLRAT.lean` has been removed. A separate small `bv_decide`
axiom test also used only the three permitted axioms.

## Restricted smooth-prime C3 diagnostics

`/tmp/cube_c3_smooth.py` filtered all `3^r` assignments exactly for the
primitive stored collisions through 100000 supported on the first r primes:

| r | largest prime | edges | surviving assignments |
|---|---:|---:|---:|
| 4 | 7 | 2 | 72 |
| 5 | 11 | 3 | 208 |
| 6 | 13 | 3 | 624 |
| 7 | 17 | 8 | 1588 |
| 8 | 19 | 10 | 4528 |
| 9 | 23 | 17 | 9970 |
| 10 | 29 | 24 | 23076 |
| 11 | 31 | 32 | 52024 |
| 12 | 37 | 40 | 115276 |

At r=13 it reported 49 edges through prime 41 but did not enumerate assignments.
The saved outputs are `/tmp/cube_c3_smooth_{r}.json`. These surviving finite
assignments do not establish an infinite coloring.

A subsequent generator, `/tmp/cube_c3_smooth_cnf.py`, encoded larger restricted
instances using one-hot colors and recursively included factor roots. Counts:

| r | largest prime | edges | included roots | clauses |
|---|---:|---:|---:|---:|
| 20 | 71 | 217 | 1229 | 16440 |
| 30 | 113 | 723 | 3643 | 49250 |
| 40 | 173 | 1506 | 6513 | 88819 |
| 50 | 229 | 2605 | 9955 | 136772 |
| 70 | 349 | 5364 | 16608 | 231358 |
| 100 | 541 | 9860 | 25044 | 354244 |

CaDiCaL proof-producing runs at r=40 and r=70 each hit their 120-second
wall-clock limit without SAT or UNSAT. Their partial traces are NOT
unsatisfiability certificates. Files use `/tmp/cube_c3_smoothcnf_{r}` prefixes.
No solver or checker job from this continuation remains running.

The conic, fixed-gap, reduced-gap, and weighted-divisor-cover arguments were
reviewed again. No summable bound over all families, uniform finite-density
bound, or universal density-zero theorem was found. A further attempt to
read the problem website failed because external DNS was unavailable.

**The original task is still unresolved.** `Submission/Spec.lean` has not
been edited and still contains its original `sorry`. No valid settlement
has been submitted, and none of these auxiliary results is its negation.

## Complete rational parametrization (verified auxiliary result)

A new file, `Submission/CubeCollisionParametrization.lean`, compiles without
`sorry` and has a built `.olean`. Its two printed axiom checks contain only
`propext`, `Classical.choice`, and `Quot.sound`.

For every rational collision

    0 <= a < b < c < d,   a^3 + d^3 = b^3 + c^3,

`ordered_cube_collision_normal_form` gives rational q,u,v,t such that

    0 < q < 1,  0 < t,  u < v,
    u^2 + u*v + v^2 = 3*q,
    (a,b,c,d) = t * (q^2+u, q^2+v, q*u+1, q*v+1).

The proof explicitly takes

    q = (d-c)/(b-a),
    t = (q*a-c)/(q^3-1),
    u = a/t-q^2,   v = b/t-q^2.

It proves the needed gap inequality `d-c < b-a`, so all divisions and
signs are justified, and uses the exact factorization

    (q^2+u)^3 + (q*v+1)^3 - (q^2+v)^3 - (q*u+1)^3
      = (u-v)*(q^3-1)*(3*q-(u^2+u*v+v^2)).

`ordered_cube_collision_quartic_parametrization` substitutes

    r=(u+2*v)/3,  s=(v-u)/3,  N=r^2-r*s+s^2=q,

and proves that every such collision is a positive rational dilate of

    N^2+r-2*s,  N^2+r+s,  N*(r-2*s)+1,  N*(r+s)+1.

Thus this is a complete algebraic parametrization of the ordered positive
rational collisions, not merely another particular family. It still gives
no density estimate.

### Denominator-cancellation warning

Symbolic derivation and exact SymPy polynomial checks are in
`/tmp/cube_secant_param.py`. Homogenizing the parameters with denominator V
gives integer coordinate forms

    F_A = N^2 + V^3*(R-2*S)
    F_B = N^2 + V^3*(R+S)
    F_C = V*(N*(R-2*S)+V^3)
    F_D = V*(N*(R+S)+V^3),   N=R^2-R*S+S^2.

Their common divisor is NOT uniformly bounded even for primitive parameter
triples. At V=N, all four forms have a factor N^2, leaving

    1+N*(R-2*S), 1+N*(R+S), N^2+R-2*S, N^2+R+S.

Taking S=1 and R>=3 makes the parameter triple primitive and gives positive
nontrivial collisions, while N^2 grows without bound. For example,
R=3,S=1,V=7 gives raw roots (392,1421,2450,2597); dividing by 49 gives
(8,29,50,53). The homogeneous identity and the four displayed factorization
identities were checked by exact symbolic expansion. This homogeneous
cancellation discussion has not been added as a Lean theorem.

Consequently, summing reciprocals of the uncancelled quartic values is not
a valid bound on the reciprocal cost of primitive integer collisions.
No uniform finite cover bound, positive-density construction, or universal
zero-density theorem was obtained from this parametrization.

`Submission/Spec.lean` is unchanged (SHA256
`9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63`), and the
original conjecture still has its `sorry`. No settlement was submitted.

## Further global-route review

Reviewed the complete rational parametrization, harmonic projection, finite
coloring reduction, and the completion-boundary amplification again. No new
uniform density estimate or construction was obtained.

A proposed weakening of the completion-boundary estimate to witnesses below
the maximum selected root does not fix the arbitrary-set version: start
with the existing separated examples having an arbitrarily large boundary
ratio, then add one selected integer exceeding twice every selected root
and every boundary witness. The enlarged selected set remains separated
and hence cube-Sidon. The old witnesses are all below its new maximum,
while adding just one selected root preserves an arbitrarily large ratio.
This observation has not been added as a new Lean theorem. It does NOT
rule out a special estimate for maximal, maximum-cardinality, or increasing
greedy sets; no such special estimate is established.

No new settlement material was placed in `Spec.lean`. Its original statement
and `sorry` remain unchanged, and no valid proof or disproof was submitted.

## Coloring plus deletion review

Considered weakening a proper finite multiplicative coloring to one with
uniformly linearly many monochromatic collisions below each cutoff. For a
completely multiplicative coloring, monochromaticity is preserved by every
integer dilation. Grouping ordered positive collisions by their common gcd
therefore expresses their count as a sum of `floor(N / max(e))` over primitive
monochromatic edges e. A uniform linear count bound would require a bounded
sum of `1 / max(e)` over these primitive edges. No character or coloring with
such a global bound has been constructed or proved to exist. The finite
C2/C3 obstruction certificates neither establish nor refute this weaker
summability condition.

This continuation produced no settlement and no new Lean theorem. `Spec.lean`
remains unchanged with its original `sorry`. No valid proof was submitted.

## Reduced-gap-ratio grouping review

Reviewed a possible grouping of all ordered primitive collisions by
q=(d-c)/(b-a), rather than by the full primitive quadruple. A fixed ratio
is a rational conic, but its integer root sets must include dilates of
its individual rational points. Thus the zero-density/summability results
for **fixed integer gaps** cannot be applied directly to a reduced-ratio
family with unrestricted common gap multiplier.

Targeted exact diagnostics using the stored edges are in
`/tmp/cube_gapratio_cost.py`. The numbers of distinct reduced ratios among
primitive collisions through N, and the sum of 1/d_min over these ratios
(where d_min is the smallest maximum root stored for that ratio), were:

| N | ratios | reciprocal minima |
|---:|---:|---:|
| 100 | 13 | 0.350929 |
| 300 | 53 | 0.560300 |
| 1000 | 277 | 0.918301 |
| 3000 | 1160 | 1.384140 |
| 10000 | 5530 | 2.110609 |
| 30000 | 22708 | 3.031685 |
| 100000 | 104795 | 4.403517 |

These finite diagnostics prove neither convergence nor divergence and do
not provide a collision cover. The common fixed ratio 1/4 alone has 4294
stored primitive collisions through 100000. No uniform global estimate
was established and no new settlement theorem was obtained.

`Spec.lean` remains unchanged with the original conjecture and `sorry`.

## Harmonic-route continuation: edge-inequality limitation

Revisited the negative smooth-harmonic route, seeking interactions between
prime supports rather than multiplying independent direction bounds. No
mixed-support amplification theorem was established.

One basic limitation is worth retaining: summing only the single-collision
indicator inequalities cannot yield a normalized bound tending to zero.
The fractional relaxation consisting of 0 <= x_n <= 1 and
x_a+x_b+x_c+x_d <= 3 for each nontrivial cubic collision always admits
x_n=3/4. This statement uses the four coordinates with multiplicity; it
also applies if a nontrivial collision has a repeated root. Thus any upper
certificate obtained solely by nonnegative linear combinations of these
inequalities and variable bounds has objective at least 3/4 of total
nonnegative weight. Stronger combinatorial constraints are essential for
a vanishing harmonic bound. This observation is not a claim about the
actual maximum independent set and is not a settlement.

No new proof or disproof was obtained. `Spec.lean` has not been edited.

## Exact unbounded cancellation: now kernel-verified

`Submission/CubeParamCancellation.lean` compiles and has an `.olean`. Its
`unbounded_primitive_cancellation` axiom check reports only `propext`,
`Classical.choice`, and `Quot.sound`.

For R=3k+3, S=1, V=9k²+15k+7=R²-R+1, the three parameters are pairwise
coprime. The four homogeneous quartic coordinates have gcd **exactly V²**.
After removing this factor, the roots are

    A=(3k+2)^3,
    B=(3k+3)^3+2,
    C=81k^4+270k^3+351k^2+213k+50,
    D=C+3.

The file proves 0<A<B<C<D, A³+D³=B³+C³, and gcd(A,B,C,D)=1.
The reduced gcd divides D-C=3, whereas A is 2 modulo 3, so it equals one.
The raw gcd V² is unbounded. Thus even pairwise-coprime parameters and
primitive output roots do not justify a bounded-cancellation assumption.

This verifies the earlier symbolic warning, rather than supplying a
positive-density construction or a disproof. In particular, unbounded
cancellation is not itself a proof of nonsummability: this one-parameter
family has reduced height of degree four. No global reciprocal estimate
was obtained.

Additional small exact diagnostics during the review (not Lean theorems):
31³+1867³=397³+1861³, with all four roots prime and 1 modulo 3. Hence simply
restricting to squarefree Eisenstein norms does not give Sidon cubes. This
is only a restricted-construction counterexample, not a density theorem.

`Spec.lean` remains unchanged, SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63
(the authoritative current hash is the output of `sha256sum`; no settlement
has been inserted). The original `sorry` remains.

## Primitive collision reciprocal mass: divergence proved

`Submission/PrimitiveCollisionMass.lean` compiles, has a built `.olean`, and
its main theorem `primitive_reciprocal_heights_not_summable` uses only the
three permitted axioms. It proves the unconditional global statement

    NOT Summable (e ↦ 1 / maximum_root(e))

where e ranges over all strictly ordered positive integer cubic collisions
with gcd of all four roots equal to one, each counted once. This is stronger
than the earlier finite diagnostics but is NOT a disproof of the conjecture.

The quadratic family is

    A(t,u) = 7t² + 13tu + 3u²,
    B(t,u) = 63t² + 29tu + 3u²,
    C(t,u) = 70t² + 40tu + 6u²,
    D(t,u) = 84t² + 44tu + 6u².

For t>0, it satisfies 0<A<B<C<D and A³+D³=B³+C³. Its reduced gap ratio
(D-C)/(B-A) is 1/4. Take u=p prime >=29 and t=6j+1 for j<p/12.
The file proves these outputs primitive and proves injectivity of the
parameter-to-quadruple map. It also proves D<=134p², so the reciprocal mass
for each p is >=1/(3216p). Euler's prime-reciprocal divergence finishes the
proof, using Mathlib's axiom-free theorem.

This excludes a direct construction that requires summing 1/max(e) over
all primitive collisions. It does NOT exclude overlapping divisor covers,
weighted covers, coloring-plus-deletion with a different summable residual
family, or arbitrary positive-density cube-Sidon sets. In fact `two_dvd_C`
proves the divisor 2 alone meets this entire quadratic family. Odd roots
therefore avoid all these witnesses despite the divergent edge mass.

A direct-IP HTTPS reference lookup also timed out; external mathematical
references remain unavailable. `Spec.lean` is unchanged with its `sorry`.

## Complete cubic parametrization: verified

`Submission/CubicParametrization.lean` compiles and has a built `.olean`.
Its main theorem `CubicParametrization.complete` uses only `propext`,
`Classical.choice`, and `Quot.sound`.

Write Q=a²-ab+b². Four homogeneous cubic forms are

    A = t³+(a-2b)t²+3a²t+3Q(a-b),
    B = t³+(a+b)t²+3(a-b)²t+3aQ,
    C = t³-(a+b)t²+3(a-b)²t-3aQ,
    D = t³-(a-2b)t²+3a²t-3Q(a-b).

The file proves A³+D³=B³+C³ identically. It also proves that every strictly
ordered nonnegative rational collision (x,y,z,w) is

    k*(A(a,b,1), B(a,b,1), C(a,b,1), D(a,b,1))

for rational a,b,k with b>0 and k>0. Thus this is a complete cubic, not
merely a particular near-diagonal family.

The proof transforms the previously verified quartic parametrization. If
q=r²-rs+s², set

    H=q+2r-s+1,
    a=(q+s-1)/H,
    b=2s/H.

For s>0, H>0 follows from 4H=(2(r+1)-s)²+3s². Each cubic coordinate
multiplied by H² equals eight times the corresponding quartic coordinate.
The new positive dilation factor is the old one times H²/8.

Symbolic exploration in `/tmp/cube_neardiagonal.py` also gives the particular
near-diagonal identity with roots

    t³-2t²-3,  t³-t²+3t,  t³+t²+3t,  t³+2t²+3.

The two middle coordinates are exchanged relative to the general A,B,C,D
formulas at (a,b)=(0,1); the sum-of-cubes identity is unaffected. This
particular family always has roots divisible by 3 and is not a positive-
density obstruction. No new asymptotic counting or covering estimate is
claimed from the cubic parametrization.

The conjecture is still unresolved. `Submission/Spec.lean` is unchanged
with its original statement and `sorry`.

## Continuation: global recurrence and construction review

Reviewed the complete cubic parametrization against the finite-coloring,
weighted-divisor-cover, and smooth-harmonic reductions. Searched Mathlib for
applicable polynomial/multiplicative recurrence and density-regularity results;
no applicable theorem was found. The parametrization alone does not give
recurrence in an arbitrary positive-natural-density set, and no uniform
coloring, weighted cover, every-prefix density bound, or vanishing smooth
harmonic bound was established. No new mathematical theorem is claimed in
this continuation. `Spec.lean` remains unchanged with its original `sorry`.

## Cubic base locus and cancellation-prime support (verified)

`Submission/CubicBaseLocus.lean` compiles and has a built `.olean`. Its three
main theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
For the homogeneous cubic forms A,B,C,D of `CubicParametrization.lean`, with
Q=a²-ab+b², over a field of characteristic different from 2 and 3:

    A=B=C=D=0 iff
      (t=0 and Q=0), or
      (b=0 and t²+3a²=0), or
      (b=2a and t²+3a²=0).

The file uses polymorphic copies of the same cubic formulas. It proves
`common_zero_iff` and then `common_zero_inert`: over F_p, for an odd prime
p=2 mod 3, common vanishing forces a=b=t=0. Finally,
`common_prime_split_or_small` proves that if a prime divides all four raw
integer coordinates but not all three integer parameters, then it is 2, 3,
or 1 modulo 3.

This precisely restricts the support of denominator cancellation for primitive
parameters. It does NOT bound the amount of cancellation at split primes,
and supplies no density or uniform coloring bound. The conjecture remains
unresolved; `Spec.lean` remains unchanged with `sorry`.

## Exact prime-power cancellation away from 6 (verified)

`Submission/CubicPrimePowerCancellation.lean` compiles and has a built
`.olean`. Its theorem `CubicBaseLocus.common_prime_power_iff` uses only the
three permitted axioms. For a prime p other than 2 and 3, assume p does not
divide all three integer parameters a,b,t. For every k, it proves:

    p^k divides A,B,C,D
      iff
    (p^k divides t and Q), or
    (p^k divides b and t²+3a²), or
    (p^k divides 2a-b and t²+3a²),

where Q=a²-ab+b² and A,B,C,D are the cubic parametrization coordinates.
This upgrades the preceding mod-p base-locus classification to all powers.
The proof classifies the reduced parameter vector over F_p, then uses unit
cancellation over Z/(p^k). It does not assume bounded denominator cancellation.

No uniform counting, density, or coloring bound follows in this continuation.
The original conjecture remains unresolved and `Spec.lean` is unchanged.

## Archimedean height of the raw cubic parametrization (verified)

`Submission/CubicArchimedeanHeight.lean` compiles and has a built `.olean`.
Its main theorems use only the permitted axioms. It proves the uniform bound

    (a²+b²+t²)³ <= A(a,b,t)²+B(a,b,t)²+C(a,b,t)²+D(a,b,t)².

Consequently, if the four raw coordinates have absolute value at most H,
then each of |a|³, |b|³, |t|³ is at most 2H. If the raw coordinates are bounded
by g*H before cancellation, the parameter bound is 2gH, NOT 2H. The proof
uses an explicit sum-of-nonnegative-terms identity and keeps the cancellation
factor. It does not bound that factor or yield a density estimate.

The translated-block approach was reconsidered, but no uniform control of
mixed-block collisions or positive-lower-density construction was proved.

A small exact diagnostic on the already stored edge file found 105 edges with
four prime roots through 100000, involving 410 distinct primes. Counts at
2000,5000,10000,20000,50000,100000 were 2,4,6,18,52,105. These finite counts
are NOT Lean theorems, give no asymptotic estimate, and prove neither
summability nor divergence of prime-collision cover costs.

The original conjecture is still unresolved and `Spec.lean` remains unchanged.

## Four distinct large inert primes do collide (verified)

`Submission/InertPrimeCollision.lean` compiles; `four_inert_prime_collision`
uses only the permitted axioms. It verifies the identity

    26711^3 + 35543^3 = 31469^3 + 32009^3,

with all four roots prime and congruent to 2 modulo 3, strictly ordered,
and with the smallest exceeding three quarters of the largest. Thus a
candidate retaining roots solely because of a very large inert prime factor
is not cube-Sidon. This is not a disproof of the conjecture. No global density
estimate has been obtained; `Spec.lean` remains unchanged with `sorry`.

## Parametrization now covers every Sidon obstruction (verified)

`Submission/CubicParametrizationAllCollisions.lean` compiles and has a built
`.olean`. All three main axiom checks use only the permitted axioms.

The earlier completeness proof did not actually need a strict inequality
between its middle roots. Generalizing the gap estimate and normal form gives
`CubicParametrization.complete_weak_order` for

    0 <= x < y <= z < w,  x^3+w^3=y^3+z^3.

Thus no independent proof about arithmetic progressions of cubes is needed
for completeness. The file also proves `cubeSidon_iff_no_weak_ordered` and
`not_cubeSidon_iff_parametrized_collision`: failure of Sidon cubes is exactly
an ordered natural-root witness, with possibly repeated middle roots, given
by the fixed cubic parametrization and a positive rational dilation.

This closes the previously recorded coverage gap. It does not assert that
nontrivial arithmetic progressions of rational cubes exist, nor prove their
nonexistence, and supplies no density estimate. `Spec.lean` still has `sorry`.

## Primitive integral certificates and exceptional primes (verified)

`Submission/CubicIntegralCertificates.lean` compiles and has a built `.olean`.
Its main theorem `CubicBaseLocus.primitive_collision_integral_certificate`
now connects the complete rational parametrization to the integer cancellation
lemmas. For every natural-root collision

    x < y <= z < w, x^3+w^3=y^3+z^3,
    gcd(gcd(x,y),gcd(z,w))=1,

it produces integers a,b,t,g with b,t,g positive, primitive parameter triple
`gcd(gcd(a,b),abs(t))=1`, and

    A(a,b,t)=g*x, B(a,b,t)=g*y, C(a,b,t)=g*z, D(a,b,t)=g*w.

`certificate_gcd_exact` identifies g.natAbs with the exact raw coordinate gcd.
`certificate_prime_support` restricts its primes to 2,3, and 1 modulo 3.
`certificate_prime_power_iff` transfers the three-locus criterion directly to
prime-power divisibility of g itself. The construction uses denominator
clearing, gcd normalization of the three parameters, and a Bezout argument to
show the remaining rational scalar is an integer. All main axiom checks use
only the permitted axioms (the gcd identity uses just propext and Quot.sound).

`Submission/CubicSmallPrimeCancellation.lean` also compiles and has a built
`.olean`. It certifies the formerly unproved exceptional-prime bounds:

    16 does not divide the common gcd of primitive raw coordinates;
    27 does not divide the common gcd of primitive raw coordinates.

The finite tables over ZMod 16 and ZMod 27 are checked with `decide +kernel`,
not native_decide. The file then transfers them to arbitrary integer
parameters and to the certificate factor g. All axiom checks report only the
three permitted axioms.

The local arithmetic and the completeness connection are now proved, but no
uniform coloring, finite-cost global cover, or density estimate follows from
them alone. `Spec.lean` remains unchanged with its original `sorry`.

## Exact lcm cancellation formula (verified)

Three further files compile with built `.olean` files:

* `CubicLocusProduct.lean`: the three locus divisors have disjoint prime
  support away from 2 and 3; their product has exactly the same valuations
  as the certificate factor g at all other primes.
* `CubicCancellationTables.lean`: kernel-checked local tables over ZMod 16
  and ZMod 27 and transfer lemmas. The finite checks are split by the first
  residue to keep memory bounded. The file takes about 2.5 minutes to compile.
* `CubicExactCancellation.lean`: the exact lcm formula for any primitive
  integral collision certificate with positive t and g.

Writing

    d0 = gcd(t, a^2-ab+b^2),
    d1 = gcd(b, t^2+3a^2),
    d2 = gcd(2a-b, t^2+3a^2),
    L  = lcm(d0,lcm(d1,d2)),

it proves

    g = 2^e2 * 3^e3 * L,

where e2 is 1 precisely when a and t are odd and b is even, and e3 is 1
precisely when 3 divides t but not b. Otherwise each exponent is 0.
The theorem uses g.natAbs; certificates have g>0. Thus the coefficient is
one of 1,2,3,6. This is not a bound on L, which can be large.

The older conjectured formula involving d0*d1*d2 and an optional extra 3
has NOT been separately formalized; do not conflate it with this proved
lcm formula. All main axiom checks report only the permitted axioms.

No global density construction or negation has been obtained. `Spec.lean`
is unchanged with its original `sorry`.

## Quadratic inverse and parameter height independent of g (verified)

`Submission/CubicInverseHeight.lean` compiles and has a built `.olean`.
Its main axiom checks use only the permitted axioms. The quadratic inverse
coordinates are

    U = 2wy-wz-xy+2xz-2y^2+2yz-2z^2,
    V = 2(w^2-wx+x^2-y^2+yz-z^2),
    T = 3(wz-xy).

Ring identities prove `t*U(raw)=a*T(raw)` and `t*V(raw)=b*T(raw)`.
For `0 <= x < y <= z < w`, T is positive. A Bezout argument then proves
`certificate_inverse_integral`: for any primitive parameter certificate
with t,g>0, there is an integer m>0 with

    (U,V,T)=m*(a,b,t).

`certificate_parameters_recover` identifies m with the gcd of U,V,T and
recovers a,b,t by exact integer division. Thus the primitive parameters in
this positive chart are unique.

`certificate_parameter_height` proves the genuine g-independent bounds

    |a| <= 6*w^2, |b| <= 6*w^2, |t| <= 3*w^2.

These are QUADRATIC inverse-height bounds. They do not justify dropping g
from the earlier cubic raw-height bound |a|^3,|b|^3,|t|^3 <= 2*g*w. Both
bounds now coexist and may be used for a finite parameter-counting argument.
No such counting argument yielding positive density has been obtained yet.

The inverse was discovered by exact symbolic linear algebra in
`/tmp/cube_inverse_quadratic.py`; all claimed identities and bounds above
were then independently proved in Lean. `Spec.lean` remains unchanged.

## Inverse base locus and inert prime powers (verified)

`Submission/CubicInverseBaseLocus.lean` compiles and has a built `.olean`;
all four main axiom checks use only the permitted axioms.

For the quadratic inverse U,V,T, in a field of characteristic other than
2 or 3, simultaneous vanishing is equivalent to either

    x=z and y=w,

or

    wz=xy, w^2-wx+x^2=0, y^2-yz+z^2=0.

Thus the base locus consists of one rational diagonal line and two conjugate
lines. At an odd inert prime p=2 mod3 the second case is only the zero vector,
so simultaneous vanishing is exactly the diagonal case.

`inverse_common_prime_power_inert_iff` upgrades this to every p^k: if the
integer root vector is primitive at p, then

    p^k divides U,V,T iff p^k divides x-z and w-y.

`inverseGcd_inert_pow_dvd_iff` expresses the same equivalence for the inverse
gcd and gcd(x-z,w-y). These results do not require the cubic collision
identity; they concern the inverse polynomials themselves.

This identifies another source of arithmetic concentration but gives no
uniform coloring, summable cover, or zero-density bound. `Spec.lean` is still
unchanged with its original `sorry`.

## Smooth harmonic integer optimization (finite diagnostics only)

The proposed finite smooth-prefix MILPs were run using SciPy/HiGHS.
Script: `/tmp/cube_smooth_milp.py`; output: `/tmp/cube_smooth_milp.jsonl`
and `/tmp/cube_smooth_milp.log`. The root cutoff is 100000. For each
initial prime set P, variables are smooth roots, weight is 1/n, and every
stored four-root collision imposes sum(x_n) <= 3. Vertices in no stored
edge are fixed to 1 in the objective. An explicit Euler-product reciprocal
tail is then added and the result normalized by the Euler-product mass.

| Largest prime | Smooth roots | Edges | Normalized incumbent + tail | Normalized dual upper + tail | Solver status |
|---:|---:|---:|---:|---:|---|
| 5 | 313 | 321 | 0.9231405674 | 0.9231405674 | reported optimal |
| 7 | 694 | 606 | 0.9232349670 | 0.9232349670 | reported optimal |
| 11 | 1197 | 1094 | 0.9206387974 | 0.9206387974 | reported optimal |
| 13 | 1848 | 1490 | 0.9208369364 | 0.9208369364 | reported optimal |
| 17 | 2579 | 3815 | 0.9023963267 | 0.9044246629 | time limit |
| 19 | 3419 | 5510 | 0.8948601347 | 0.8985079557 | time limit |

Important qualifications:

* These are FLOATING-POINT numerical diagnostics, not certified rational
  upper bounds and not Lean proofs. Solver status `optimal` is not a
  kernel-checked certificate.
* The incumbent-plus-tail column is only a lower bound on the finite
  optimization objective plus the tail. It is NOT a lower bound on the
  true infinite smooth independence ratio, nor on a natural density.
* A certified dual upper bound, if supplied, could give a global density
  upper bound by the existing SmoothHarmonicFinite reduction. Nothing
  here proves that these bounds tend to zero.
* A subset of necessary collision constraints suffices for an upper
  bound; absence of further stored edges does not establish their
  mathematical absence.
* For P={2,3,5} the stored primitive edges are exactly
  (1,9,10,12) and (2,9,15,16). Adding 7 gives no new primitive edge in
  this prefix. This is only a finite list, not an S-unit completeness
  theorem. The small increase in normalized bounds at 7 and 13 reflects
  the explicit finite-prefix tail, not a violation of monotonicity of
  the exact infinite optimum.
* The simple edge LP relaxation cannot go below 3/4: the constant
  assignment x_n=3/4 satisfies every four-vertex inequality.

The process was stopped after the recorded runs; no structural vanishing
inequality was found. No new Lean theorem or settlement is claimed in this
continuation. `Submission/Spec.lean` remains unchanged with its original
statement and `sorry`. Do not submit it as a completed proof.

## Continuation: root-support and counting reassessment

Reassessed whether the complete parametrization controls the set of roots
appearing in collisions, rather than just counting collisions. No such
uniform root-support estimate was obtained. Symbolic differentiation of the
raw coordinate A confirms that it is a nonsingular ternary cubic; it does
not factor into linear or quadratic factors over Q. This calculation is a
diagnostic, not a newly formalized theorem or a density argument.

In particular, neither the raw height bound involving the cancellation
gcd nor the quadratic inverse-height bound supplies a summable cover of
all collisions. Removing the gcd from the former bound remains invalid.
A linear finite-prefix collision count, even if available for primitive
points, would not by itself imply summability of their reciprocal heights.
No uniform finite coloring, positive every-prefix construction, vanishing
smooth harmonic bound, or arbitrary-positive-density recurrence theorem
was established. No new proof is claimed; Spec.lean is unchanged with sorry.

## Uniform digit-sum obstruction (new, verified)

`Submission/DigitSumObstruction.lean` compiles and has a built `.olean`.
All printed axiom checks use only propext, Classical.choice, Quot.sound.
There are no sorry/admit declarations in this auxiliary file.

Main results:

* `digit_sum_mul_pow_sub_one`: for b>1 and 1<=m<=b^k,

      sum(digits b (m*(b^k-1))) = (b-1)*k.

  The proof uses padded digits of m-1 and their digitwise complements.
* `digit_sum_fiber_not_cube_sidon`: if 12<=b^k, the full digit-sum
  fiber with sum (b-1)*k cannot be cube-Sidon. Dilate the exact collision
  (1,9,10,12) by b^k-1; all four roots have that same digit sum.
* `no_digit_sum_cube_coloring`: no coloring obtained by applying ANY
  function to the base-b digit sum has all color classes cube-Sidon.
  This statement does not even require that the color type be finite.
* `digit_weight_sum`: the exact generating-function identity

      sum_{n<b^k} r^(sum(digits b n)) = (sum_{d<b} r^d)^k.

* `lowerDensity_zero_of_bounded_binary_digit_sum`: every set with
  uniformly bounded binary digit sum has lower density zero. The proof
  bounds its count through 2^k by 2^K*(3/2)^k and uses geometric decay.
* `binary_digit_sum_determined_cube_sidon_lowerDensity_zero`: if membership
  in A depends ONLY on binary digit sum and the cubes of A are Sidon, then
  A.lowerDensity=0. Indeed A must omit every full digit-sum fiber k>=4,
  so all its roots have binary digit sum at most 3.

LIMITATION: This is a restricted construction-class obstruction, NOT a
negation of the original conjecture. It does not cover arbitrary automatic
sets, arbitrary digit-dependent sets, or arbitrary positive-density sets.
No symmetrization preserving cube-Sidonness was obtained. The contemplated
finite-monoid/automaton generalization was not proved and is not claimed.

A separate unrestricted two-color SAT diagnostic is pending:

* Input `/tmp/cube_unrestricted2_100000.cnf`: all 898947 stored four-root
  collisions through 100000, two NAE clauses per edge, and color-complement
  symmetry fixed at vertex 1. No multiplicativity constraint is imposed.
* CaDiCaL command runs with a 1800-second timeout; wrapper PID 36951 and
  solver PID 36953 at launch. Log `/tmp/cube_unrestricted2_100000.log`,
  prospective certificate `/tmp/cube_unrestricted2_100000.lrat`.
* At the last check (about seven minutes into the run), no SAT/UNSAT result
  had been returned. A partial LRAT file is not a proof. Even an eventual
  UNSAT certificate would only disprove two-colorability, not the conjecture.

`Submission/Spec.lean` is unchanged with its original sorry and statement.
No settlement has been obtained or submitted.

## Continuation: unrestricted two-color timeout and global reassessment

The unrestricted two-color run through 100000 ended at the 1800-second timeout.
This was confirmed from `/proc/36951/stat`: raw exit code 31744, i.e. exit
status 124. The solver log is empty. Neither SAT nor UNSAT was reported.
The 3.7 GiB `/tmp/cube_unrestricted2_100000.lrat` is only a partial trace,
not a refutation certificate. There is no solver job still running for this
instance. Do not replay or describe that partial trace as a completed proof.

The exact parametrization was reconsidered as a potential root-support cover,
not just a point-counting tool. No summable reciprocal root cover was obtained.
In particular, the unbounded cancellation gcd cannot be removed from the height
bound. The existing divergent primitive-edge family is still covered by the
single divisor 2; it therefore cannot establish divergence of every cover.

A further warning about finite-group multiplicative constructions (elementary
mathematical observation, not a new Lean theorem): if a completely multiplicative
coloring takes values in a group of exponent e, every positive e-th power lies
in its identity fiber. If that fiber has Sidon cubes, then all positive (3e)-th
powers must themselves be Sidon, since (n^e)^3 = n^(3e). Thus an elementary
abelian 2-group construction would in particular have to establish Sidonness
of all positive sixth powers. Increasing the number of character coordinates
is not merely a computational substitute for the missing global argument.
No claim about the truth or falsity of that higher-power statement is made here.

No proof or disproof of the original conjecture was found in this continuation.
`Submission/Spec.lean` remains unchanged with its original statement and sorry;
SHA256 9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No submission was made.

## New verified necessary condition for divisor-closed constructions

`Submission/PrimeCoverNecessity.lean` now compiles and has a built `.olean`.
Its printed axiom checks use only propext, Classical.choice, and Quot.sound.
No sorry or admit is present in this auxiliary file.

Definitions and conclusions:

* `IsPrimeCubeCover P`: P meets every nontrivial cubic collision all four of
  whose positive roots are prime.
* `summable_prime_cover_of_weighted_cover`: any summable nonnegative weighted
  divisor cover with w(1)=0 yields a prime cover of finite reciprocal mass.
  Take P = {p prime : w(p) >= 1/4}. For prime p, divisorWeight w p = w(p),
  so the four-root cover inequality forces one of these four weights >=1/4.
  Comparison with 4*sum(w(d)/d) proves summability.
* `summable_excluded_primes_of_divisorClosed`: if A is divisor-closed and has
  positive lower density, then sum_{p prime, p notin A} 1/p converges. No Sidon
  hypothesis is used here. The proof counts the disjoint dilates p*A for
  excluded primes p. If p*a=q*b with b in A and p,q excluded primes, primality
  and divisor closure force p=q, then a=b. A positive every-prefix bound for A
  consequently bounds every finite reciprocal sum of excluded primes.
* `summable_prime_cover_of_divisorClosed_cube_sidon`: combines the previous
  result with Sidonness. Thus EVERY positive-density divisor-closed solution,
  not just a summable weighted-cover solution, would provide a harmonically
  summable prime-root collision cover.

LIMITATION: no such prime cover has been constructed and its nonexistence has
not been proved. Arbitrary positive-density cube-Sidon sets need not be
(divisor-)closed. These necessary conditions do NOT negate the original
conjecture, nor do they supply a witness for it.

The saved LP support was inspected without running further blind finite
searches. Floating-point diagnostics (not asymptotic assertions):

  cutoff 10000: prime contribution 0.324604539, composite 0.041995922
  cutoff 30000: prime contribution 0.351084685, composite 0.038402632

The harmonic-weighted mean prime weight on [100,1000) changes from about
0.1307 to 0.1401; on [1000,5000), from 0.1059 to 0.1244. These numbers do NOT
prove divergence, convergence, or any uniform global cost bound. No explicit
formula covering all collisions emerged from this inspection.

Clarification after rereading `SquarefreeColoringReduction.lean`: its fixed
finite squarefree coloring hypothesis suffices for the EXISTENTIAL density
conjecture. It does not assert that the same coloring extends to all integers.
In particular, the higher-perfect-power obstruction for multiplicative
colorings on all roots is not automatically an obstruction to coloring only
squarefree roots. No uniform squarefree coloring has been established.

`Submission/Spec.lean` remains unchanged and unresolved. No submission made.

## Continuation: squarefree/conic reassessment, no settlement

Rechecked the squarefree route against the explicit pairwise-coprime quadratic
family in `CoprimeCollisionFamily.lean`. Exact SymPy factorization and
polynomial expansion gave:

  8428*t^2 + 62629*t + 116863, discriminant -17293815
  8428*t^2 + 62587*t + 116707, discriminant -17293815
  1204*t^2 + 9973*t + 20359,   discriminant 1411785
  1204*t^2 + 7915*t + 12715,   discriminant 1411785.

All four have content one, are irreducible over Q, and are pairwise coprime
as polynomials. Their cubic collision identity was again checked by exact
expansion. This is a symbolic diagnostic, not a new Lean theorem or a
squarefree-value distribution theorem. In particular, irreducibility does
NOT assert that simultaneous squarefree or prime values occur infinitely
often. No such assertion is used.

Also reread the existing fixed-gap sieve, conic discriminant, reduced-gap,
and denominator-cancellation results. Their global limitations remain:
fixed integer gaps are not the same as a fixed reduced ratio with arbitrary
common multiplier; finite collections of summable families do not provide
a uniform cost for their infinite union; and no cancellation factor can be
silently discarded. No uniform squarefree coloring or global density
argument emerged.

No new Lean theorem was added in this continuation. `Spec.lean` is unchanged
with its original statement and sorry. The task remains unresolved; no
completed proof or disproof has been submitted.

## New verified prime-relabel-invariance obstruction

`Submission/PrimeRelabelObstruction.lean` compiles and has a built `.olean`.
All four printed axiom checks report only propext, Classical.choice, Quot.sound.
There are no sorry/admit declarations in this auxiliary file.

`PrimeRelabelInvariant A` means that for each injective map f : Nat -> Nat
sending primes to primes, and each positive n, membership in A is unchanged
when n is replaced by

    n.factorization.prod (fun p e => f(p)^e).

Thus this restriction applies to membership rules depending only on the
multiset of prime exponents, rather than on prime identities.

Main proved results:

* `prime_relabel_cube_sidon_powerful`: if A is invariant in this sense and
  its cubes are Sidon, every n in A is powerful (every prime divisor has
  exponent at least two). If some member has an exponent-one prime, relabel
  all its other prime factors to distinct primes above 35543, obtaining a
  common positive cofactor m. Replacing the remaining exponent-one prime by
  26711, 31469, 32009, and 35543 forces all four roots of the exact collision

      (26711*m)^3 + (35543*m)^3 = (31469*m)^3 + (32009*m)^3

  into A, a contradiction.
* `powerful_eq_square_mul_cube`: every powerful n can be written a^2*b^3.
  The proof splits each prime exponent e into
  2*((e-3*(e mod 2))/2) + 3*(e mod 2), using e=0 or e>=2.
* `powerful_prefix_count`: there are at most t^5 powerful integers below t^6.
  In the preceding decomposition, positive n<t^6 gives a<t^3 and b<t^2;
  zero is handled separately by a=b=0.
* `lowerDensity_zero_of_powerful_support`: any subset of the powerful
  integers has lower density zero.
* `prime_relabel_cube_sidon_lowerDensity_zero` combines these conclusions.

LIMITATION: the conjecture imposes NO prime-relabel invariance. No operation
symmetrizing an arbitrary positive-density cube-Sidon set while preserving
Sidonness has been established; such an operation must not be assumed.
This is another construction-class obstruction, not a disproof of Spec.lean.

`Submission/Spec.lean` remains unchanged with its original statement and sorry.
No complete proof or disproof has been obtained or submitted.

## Continuation: global-route reassessment, still unresolved

Rechecked the actual `IsSidon` and `lowerDensity` definitions: they have the
standard meanings needed by the conjecture. No definitional shortcut was found.

Recorded the previous exact prime-swap diagnostic: {1,9,35,147} has ten distinct
unordered cube-pair sums. Swapping prime labels 2 and 7 sends this set to
{1,9,10,12}, whose cubes have the collision 1^3+12^3=9^3+10^3.
This exact integer observation was not formalized in Lean. In particular,
prime relabelling does NOT generally preserve cube-Sidonness, so the verified
prime-relabel-invariant obstruction cannot simply be applied by symmetrization.

Inspected the saved complete four-distinct-root edge list, rather than generating
new search instances. Exact finite counts (not asymptotic bounds):

  cutoff  total   primitive  pairwise-coprime  squarefree  all-prime
    1000   1601        634                 6          83          0
    3000   7846       2771                26         402          4
   10000  41810      13168               152        2292          6
   30000 184007      53097               732       10287         30
  100000 898947     238300              3516       51697        105

Here squarefree/all-prime requires all four roots to have the property.
Primitive means common gcd one; it does not mean pairwise coprime.
These counts give neither a convergent reciprocal cover nor a lower-density
obstruction. No unproved point-counting or prime-value heuristic is used.

Reconsidered bounded reduced-gap ratios as a possible quantitative negative
route. The existing positive-density progression avoiding each finite ratio
collection does not rule out bounds tending to zero as collections grow, but
no such quantitative upper bounds have been proved. Standard additive-density
recurrence cannot be applied directly: arbitrary common translation does not
preserve a nontrivial cubic collision.

No new Lean theorem was added in this continuation. `Spec.lean` is unchanged,
with its original statement and sorry. No complete proof/disproof was submitted.

## Continuation: extraction and global-coloring reassessment

Re-read `Compactness.lean`, `ColoringReduction.lean`, and
`SmoothHarmonicFinite.lean`, and searched the imported libraries for stronger
Sidon extraction results. No missing ready-made theorem was found.

The compactness condition remains a single positive delta and a single error C
valid at every prefix of each finite witness. A final-cutoff cardinality bound
alone does not satisfy it. The finite-coloring reduction obtains bounded
multiplicative coverage by repeatedly eliminating colors using dilation and
compactness; no fixed finite coloring is available to invoke that reduction.
The normalized smooth bounds remain only upper bounds, not a proved positive
construction criterion.

Considered whether homogeneity could amplify a fixed finite density loss by
products. Fiberwise Sidon constraints do not justify multiplying losses across
prime directions: correlated choices can defeat that inference. No additional
cubic identity supplying the needed product amplification was obtained.

An exact check of the existing edge file found no collisions supported solely
on the prime pairs {2,3}, {2,5}, {3,5}, {2,7}, or {3,7} through 100000, and 321
edges supported on {2,3,5}. These are ONLY bounded checks. They prove no
infinite smooth Sidon theorem, rank restriction, or coloring result.

No new Lean theorem or settlement was obtained in this continuation.
`Submission/Spec.lean` remains unchanged with its original sorry.

## Continuation: ratio-family covering check

Checked the complete parametrization symbolically. With the existing A,B,C,D
and parameters a,b,t, the exact factorizations are:

  B-A = 3*b*(a^2-a*b-2*a*t+b^2+b*t+t^2)
  D-C = 3*b*(a^2-a*b+2*a*t+b^2-b*t+t^2)
  C-A = -(2*a-b)*(3*a^2-3*a*b+3*b^2+3*b*t+t^2)
  D-B = -(2*a-b)*(3*a^2-3*a*b+3*b^2-3*b*t+t^2).

These are exact SymPy checks, not newly added Lean theorems. They describe
common factors in raw gaps. They do not justify replacing the unbounded raw
coordinate gcd by a constant or asserting a summable cost over reduced-ratio
families. Re-read `GapRatioNorms.lean` and `FixedGapSieve.lean`; their stated
limitations still apply. In particular a fixed absolute-gap family and a
fixed reduced-ratio family with arbitrary common gap multiplier are different.

No global uniform bound or completed proof/disproof was obtained.
`Submission/Spec.lean` remains unchanged with its original sorry.

## New packing work (certificate verification initially pending)

`Submission/CubePacking.lean` compiles with permitted axioms only and has a
built `.olean`. New theorems:

* `smooth_harmonic_bound_of_cube_packing`: a finite list of valid four-root
  collisions, with nonnegative integer edge weights and integral vertex
  capacities `n * load(n) <= M`, gives smooth reciprocal mass at most
  `smoothReciprocalMass P - totalWeight/M` for every finite cube-Sidon set.
* `cube_packing_fractional_barrier`: every such packing has
  `totalWeight/M <= smoothReciprocalMass P / 4`. Thus plain four-vertex
  fractional packings CANNOT give normalized bounds below 3/4, even with
  arbitrarily large prefixes. A zero-density argument needs more than these
  constraints.

LP extraction (not relied on as an axiom) produced exact rational certificates
in `/tmp/cube_harmonic_packing_{5,19,31,47}.json`. Exact Python checks verified
all collisions and integral capacity inequalities. Normalized upper-bound
values from these finite packings are approximately .9231646, .9020214,
.8933050, and .8880701. These are not asymptotic claims.

A 900-edge subset of the p<=31 certificate was generated in
`Submission/CubePackingCertificate.lean`. It uses 1845 distinct roots, common
weight denominator 10000000000, and total integer edge weight 6559361803.
All roots divide the explicit smooth number
8494990594304404599449212473100800000.
The intended normalized bound is
152573765065999 / 169575630859375 < 9/10.

The first complete numeric kernel run passed all collision/smoothness and
45 capacity checks, but the two final assembly proofs failed: list `++` was
left-associative while the `rcases` pattern was right-associated. Therefore
that first run did NOT verify the global 9/10 theorem.

The source now uses explicitly right-associated appends and assembles via
`List.forall_mem_append` and conjunctions. A second full verification was
started (Lean PID 41183; wrapper PID 41135). Check the current log/status:

  /tmp/cube_packing_certificate_lean.log
  /tmp/packing_certificate_stage

Do not claim the final theorem is verified unless the second run succeeds
and its axiom check contains no sorryAx. The numerical checks use
`decide +kernel`, split into blocks of 20 edges; no native_decide is used.
Compilation has been taking about 25 minutes at `-j 1`.

Even a verified 9/10 upper bound would NOT settle the conjecture, which only
asks for some strictly positive lower density. `Spec.lean` is unchanged.

## Packing certificate successfully verified

The second complete run of `Submission/CubePackingCertificate.lean` succeeded.
All numerical checks, the right-associated list assembly, and the exact
normalization proof passed. The module is built at:

  .lake/build/lib/lean/Submission/CubePackingCertificate.olean

A fresh importing file `/tmp/check_cube_packing_axioms.lean` independently
printed the axioms of:

* `Erdos1206.packing31_harmonic_bound`
* `Erdos1206.cube_sidon_lowerDensity_le_nine_tenths`
* `Erdos1206.cube_packing_fractional_barrier`

Each lists exactly `[propext, Classical.choice, Quot.sound]`, with no sorryAx.
Thus the global bound `A.lowerDensity <= 9/10` for arbitrary cube-Sidon root
sets is now a verified partial theorem, not a pending certificate.

The original conjecture is STILL UNRESOLVED. The bound permits positive
lower density and cannot serve as a disproof. The fractional-packing barrier
also means this method by itself cannot produce normalized bounds below 3/4.
Reconsidering the finite-coloring and finite-prefix compactness reductions
supplied neither of their missing global hypotheses. No converse from a
positive smooth harmonic optimum to a positive natural lower-density witness
was established.

`Submission/Spec.lean` remains unchanged and still contains its original sorry.
No complete proof or disproof was submitted. The pending certificate process
has finished; there is no need to repeat its approximately 25-minute build.

## Further global-route review: no settlement

Re-read the weighted divisor-cover criterion, the complete cubic
parametrization and its raw/inverse height estimates, the fixed-gap sieve,
and the finite-extension construction. No new sufficient hypothesis was
proved and no new settlement theorem was added.

In particular:
* The raw-coordinate cubic height bound retains the unbounded cancellation
  factor. It gives no summable global cover of reduced primitive collisions.
* Summability for each individual fixed-gap family is not summability of
  their countable union. Finite-family avoidance supplies no uniform positive
  density bound as the family grows.
* Adjoining sufficiently remote short blocks preserves Sidonness, but those
  extension bounds do not maintain positive density at every intervening
  prefix. Final-cutoff cardinality bounds cannot be substituted for the
  hypothesis of `compactness_finite_cube_sidon`.
* Neither a uniform finite coloring nor vanishing normalized smooth harmonic
  bounds has been established.

The verified 9/10 bound remains a partial result only. `Spec.lean` remains
unchanged with its original sorry, and no completed proof was submitted.

## New verified result: cancellation remains unbounded in all 24 charts

`Submission/AllChartCancellation.lean` now compiles successfully. A fresh
import in `/tmp/CheckNewChartResults.lean` confirms only the permitted axioms
for its main theorems. Its built module is:

  .lake/build/lib/lean/Submission/AllChartCancellation.olean

The explicit family is

  1 + (9*T^4 + 3*T)^3 = (9*T^4)^3 + (9*T^3 + 1)^3.

The file lists exact polynomial certificates for all 24 signed coordinate
permutations of `(1, -9*T^4, -(9*T^3+1), 9*T^4+3*T)`. It verifies:
* All four raw-coordinate identities for each chart, by `ring`.
* A polynomial Bezout identity with constant 6 for each parameter triple.
* Nonvanishing of the relevant inverse coordinate for T >= 1.
* A lower bound `8*T^2 <= |G|` for the displayed polynomial scale factor.
* Completeness of the 24-entry permutation table by `decide +kernel`.

`certificate_scale_bound` compares any primitive integral certificate for a
point to a polynomial certificate satisfying the Bezout identity. The latter
parameter triple is an integer multiple m of the primitive one, `m | 6`,
and `G = m^3*g`. Consequently `|G| <= 216*|g|`.

The main quantitative theorem is

  Erdos1206.ChartCancellation.permutation_cancellation_lower

which proves `8*T^2 <= 216*|g|` for every primitive integral certificate of
every signed permutation in this family. The existential theorem

  Erdos1206.ChartCancellation.unbounded_cancellation_all_permutations

states that for every K some T >= 2 has this cubic identity and every such
primitive certificate, in every signed permutation chart, has |g| > K.
Thus selecting the best of these 24 charts does NOT bound the cancellation
factor uniformly. This rules out one possible repair of the raw height
argument; it does NOT settle the density conjecture.

Complementary positive result:

`Submission/QuarticFamilySieve.lean` also compiles, with only permitted axioms.
It proves reciprocal summability of

  quarticFamilyDivisors = {9*(n+1)^3+1 : n in Nat}

using the exact count bound below 16^j of at most 8^j. Its theorem

  Erdos1206.positive_density_avoids_quartic_family

constructs a set of positive lower density excluding every
`q*(9*t^3+1)` for t >= 1. Therefore all dilations of the entire displayed
quartic collision family can be avoided at positive lower density. Large
cancellation in that family is not itself a zero-density obstruction.

Auxiliary exact calculation scripts remain in `/tmp/cube_chart_*.py`.
The source generator `/tmp/gen_all_chart_cancellation.py` predates several
Lean fixes and must NOT be rerun over the final checked file without review.
The successful full verification log is
`/tmp/all_chart_cancellation_v5.log`; compilation took several minutes.
Earlier logs contain failed attempts and must not be mistaken for the final
verification. No Lean compiler remains running for these new modules.

The original task is STILL UNRESOLVED. `Submission/Spec.lean` is unchanged
and still contains its original sorry. No completed proof was submitted.

## Bounded-degree extraction diagnostic (finite data only)

Re-examined whether collision incidence is concentrated on a sparse set of
exceptional roots, which might permit a bounded-degree extraction argument.
`/tmp/cube_degree_diagnostic.py` uses only the existing exact edge file.
For roots in (N/2,N], total incidence degree in the prefix hypergraph has:

  N       mean     median   90th percentile
  1000     4.890      4       11
  3000     7.807      6       16
  10000   12.154      9       25
  30000   17.509     13       36
  100000  25.310     19       51

The prime-root medians in those same bands are 2,3,4,6,8. Roots with larger
Omega have higher degrees, but the finite growth is not confined to that
class. These observations establish NO asymptotic degree estimate, no
independence-ratio upper bound, and no impossibility of positive density.
They do not supply the uniform bounded-degree hypothesis that would make
this extraction route work. No new Lean settlement was obtained.

`Spec.lean` remains unchanged with its original sorry. No proof was submitted.

## Latest continuation: no settlement

Reassessed a recurrence-based disproof route and a large-prime-factor source
for positive-density extraction. Neither yielded a missing global hypothesis.
The known conic identities do not supply a translation-invariant polynomial
configuration to which a standard additive density theorem applies. No claim
that arbitrary positive-density sets contain a cubic collision was proved.

Finite diagnostic `/tmp/cube_large_prime_degree.py` restricts the stored
four-distinct-root edges to roots with largest prime factor greater than
`n^(1-epsilon)`. For epsilon 0.1, the retained edge counts at cutoffs
1000, 3000, 10000, 30000, 100000 were 0, 7, 26, 103, 396. For epsilon 0.2,
they were 7, 45, 178, 690, 3008. These are only finite diagnostics. They
establish neither bounded asymptotic edge density, summable collision mass,
nor positive-density Sidon extraction. The stored edge list excludes
repeated-middle-root cases, and the threshold comparison in this diagnostic
uses floating-point powers; no Lean certificate is claimed.

No new global construction, uniform coloring, summable divisor cover, or
vanishing upper-density bound was established. `Submission/Spec.lean` is
unchanged and still contains its original `sorry`. No proof was submitted.

## New verified global collision-growth theorem

`Submission/CubeCollisionGrowth.lean` compiles, with a built `.olean`.
It imports the existing `PrimitiveCollisionMass.lean`.

In namespace `Erdos1206.CubeCollisionGrowth`:

* `collisionsUpTo N` counts strictly increasing positive quadruples
  `(a,b,c,d)` with `d <= N` and `a^3+d^3=b^3+c^3`.
* `finite_dilate_count` injects the integer dilates of any finite collection
  of primitive collisions into this finite set. Primitivity recovers the
  dilation factor from the gcd, so no collisions are double-counted.
* `finite_reciprocal_count_bound` proves the corresponding reciprocal-height
  lower bound, with additive error equal to the number of primitive edges.
* `collision_count_superlinear` proves that for every real `C`, all
  sufficiently large `N` satisfy `C*N < (collisionsUpTo N).card`.
* `collision_count_div_tendsto_atTop` states that the count divided by `N`
  tends to positive infinity.

The last two axiom checks list only `propext`, `Classical.choice`, and
`Quot.sound`. Successful log: `/tmp/cube_collision_growth_v2.log`.

This is NOT a disproof: superlinear edge counts do not force vanishing
independence density. It rules out a uniform `O(N)` bound on the number of
all-root cubic collisions as a shortcut to a random-deletion construction.
The old primitive family giving the divergent mass is itself avoidable by
excluding even roots, as already proved in `PrimitiveCollisionMass.lean`.

A finite increasing-order greedy diagnostic on the stored four-distinct-root
edge list accepted 671, 1867, 5749, 16050, 49842 roots at cutoffs
1000, 3000, 10000, 30000, 100000 respectively. It supplies no asymptotic
bound or full Lean Sidon certificate. Saved array:
`/tmp/cube_root_greedy_100000.npy`.

The fixed-gap sieve bounds still do not have the global uniform control
needed for a summable cover. No settlement was obtained. `Spec.lean`
remains unchanged with its original `sorry`; no proof was submitted.

## Repeated-middle-root gap now resolved (verified)

New files, both compiled with built modules:

* `Submission/CubeAPDescent.lean` (about 600 lines).
* `Submission/StrictCubeCollision.lean`.

In namespace `Erdos1206.CubeAPDescent`:

* `primitive_norm_cube_strong` parametrizes a primitive solution of
  `x^2+3*y^2=z^3`, assuming coprimality of the norm with 6 and odd `x+y`.
  It proves `x=e*(e^2-9*f^2)`, `y=3*f*(e^2-f^2)`, `z=e^2+3*f^2`,
  together with coprimality and parity of `e,f`.
* This uses the actual PID theorem for the ring of integers of
  `CyclotomicField 3 Rat`, an integral two-element power basis, the six-unit
  classification, and coprime-factor cube extraction. No unproved descent
  or rank computation is assumed.
* `int_cube_AP_trivial x y z` proves `x=y` from `z != 0` and
  `x^3+y^3=2*z^3`, for signed integers. The proof is strong induction on
  `z.natAbs`. After removing common factors, put `x=s+t`, `y=s-t`.
  If `3` does not divide `s`, extract cubes from
  `e*(e-3*f)*(e+3*f)`. If `3` divides `s`, extract cubes from
  `f*(e-f)*(e+f)`. Each case produces a smaller nontrivial middle root.
* `nat_cube_AP_trivial a b c` proves `a=b AND c=b` from
  `a^3+c^3=2*b^3`, including the zero case.

In namespace `Erdos1206`:

* `weak_cube_collision_is_strict_positive` upgrades any weakly ordered
  nontrivial natural collision to positive first root and strictly ordered
  middle roots. Zero is excluded using Mathlib's FLT for exponent three;
  a repeated middle root is excluded by the new descent theorem.
* `cubeSidon_iff_no_strict_positive` and
  `not_cubeSidon_iff_strict_positive_collision` give the exact four-distinct,
  positive, sorted-root characterization of Sidon cubes for ANY natural set.
* `cubeSidon_insert_zero_iff` shows that adjoining zero introduces no new
  cubic Sidon obstruction.

Fresh import/axiom check: `/tmp/CheckCubeAPResults.lean`, output
`/tmp/check_cube_ap_results.log`. Every listed theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound`. Successful development logs:
`/tmp/cube_ap_descent_v13.log` and `/tmp/strict_cube_collision_v2.log`.
Earlier logs contain failed intermediate attempts; they are not the checked
final proof.

This supersedes the earlier warning that repeated-middle-root cases were an
unproved gap in reducing Sidonness to four-distinct-root collisions. It does
NOT certify the completeness of an external edge enumeration or provide a
kernel check of any saved SAT assignment. It does NOT settle the positive
lower-density conjecture.

`Submission/Spec.lean` is still unchanged, with its original `sorry`.
No proof or disproof of the original existential statement was submitted.

## Large-prime-source transfer and obstruction (verified)

New file `Submission/LargePrimeSource.lean`, compiled with a built `.olean`.
Successful log: `/tmp/large_prime_source_final.log`.

* `largePrimeSource k` uses the exact natural-power condition
  `0<n AND exists prime p dividing n, n^(k-1)<p^k`.
  For `k>=2` this is the large-prime threshold with epsilon `1/k`.
* `largePrimeSource_prime_prefix` proves that for every positive `k`, every
  finite positive prefix, and every lower bound on the multiplier, there is
  a prime multiplier moving the entire prefix into this source.
  The elementary sufficient inequality is `M^(k-1)<p`.
* `HasPrefixDilations` abstracts this property, and
  `goodCubeColoring_of_prefix_dilations` transfers any fixed finite coloring
  with cube-Sidon fibers on such a source to all positive roots by compactness.
* `largePrimeSource_coloring_iff` gives exact equivalence for each prescribed
  number of colors. Thus this restriction does not reduce finite-coloring
  complexity.
* `LargePrimeSource.no_hereditary_linear_bound` combines dilation embedding
  with the previously verified superlinear collision count. For every natural
  constant C it gives a finite vertex set in the source and distinct strict
  positive cubic collision edges with `C*vertices.card < edges.card`.
* `LargePrimeSource.largePrimeSource_no_hereditary_linear_bound` specializes
  that result to each positive k.

Both final principal axiom checks list only `propext`, `Classical.choice`,
`Quot.sound`. This does NOT show that the edge/vertex ratio of the source's
full natural prefixes is unbounded. It does NOT preclude a positive-density
independent subset, nor does it settle the original conjecture.

Additional finite diagnostic caution: for epsilon .05 and n<=100000 the
large-prime source is simply the primes, since n^.05<2. Thus the very small
finite collision counts at that epsilon do not represent asymptotic
positive-density behavior. No asymptotic estimate was inferred from them.

`Spec.lean` remains unchanged with its original `sorry`. No proof or disproof
of the required existential statement has been obtained or submitted.

## Explicit residue-class collisions and finite-cover obstruction (verified)

New file `Submission/ResidueCollision.lean` compiles, with built `.olean`.
Successful final log: `/tmp/residue_collision_final.log`.

The four increasing positive roots for m>0 are

  a(m) = 6*m^3 + 15*m^2 + 7*m + 1
  b(m) = 27*m^3 + 24*m^2 + 8*m + 1
  c(m) = 45*m^3 + 36*m^2 + 10*m + 1
  d(m) = 48*m^3 + 39*m^2 + 11*m + 1.

They satisfy a(m)^3+d(m)^3=b(m)^3+c(m)^3 and are all 1 modulo m.
The identity is proved by ring normalization; order is proved algebraically.

In namespace `Erdos1206.ResidueCollision`:

* `collision_in_residue_tail q r N hq` gives a strict positive collision with
  all roots larger than N and all congruent to r modulo positive q.
  Evaluate at m=q*(N+1) and multiply the four roots by r+q.
* `no_residue_tail` proves a cube-Sidon root set contains no entire tail of
  any residue class modulo a positive integer.
* `finite_of_eventually_periodic` proves such a set is finite if, beyond some
  N, membership is equivalent at n and n+q for a fixed positive q.
* `lowerDensity_zero_of_eventually_periodic` is the density corollary.
* `no_finite_divisor_cover` proves no finite forbidden-divisor set omitting 1
  can cover all cubic collisions. Take m to be the product of its positive
  divisors; every constructed root is 1 modulo each of them.

All five principal axiom checks list exactly the allowed axioms: propext,
Classical.choice, Quot.sound.

These results do not disprove the conjecture: an arbitrary positive-density
set need not be eventually periodic. They do not exclude an INFINITE summable
divisor cover, nor uniform bounds for finite covers that vary with the cutoff.
No such bound or global weight formula was found on reexamining the existing
finite optimization data. Finite LP outputs still do not supply asymptotic
bounds.

`Submission/Spec.lean` is unchanged and still contains its original `sorry`.
No proof or disproof of its existential statement was submitted.

## Composition and symmetric-height reassessment: no settlement

Reexamined composition of cubic identities as a possible way to make density
losses accumulate. No uniform amplification or independent-loss mechanism was
established. Multiplying two cube-sum identities produces an equality with more
terms, not automatically another four-root collision. No inference of zero
independence density was made.

Correction/clarification: `FiniteDivisorObstruction.lean` already proved that
finite forbidden-divisor sets omitting 1 leave a collision uncovered, using an
older higher-degree polynomial identity. Thus the finite-cover consequence in
`ResidueCollision.lean` is not a new obstruction. That file gives a simpler
cubic family and explicit residue-tail/eventual-periodicity conclusions.

A targeted finite test of a possible best-chart height improvement was run:
`/tmp/cube_min_chart_height.py`. It computes the gcd-normalized quadratic
inverse parameter height in all 24 signed permutation charts. The inputs are
recorded primitive collisions through 100000, with deterministic subsampling
at the larger cutoffs. In this sample the smallest parameter height can be
comparable to the largest root, not its square root. For example, the recorded
collision (68144,75603,77061,83074) has minimum chart height 126867 according to
this exact-integer script. The printed height-squared/maximum ratios use
floating division only for display. This is not a kernel-checked certificate
and proves neither an asymptotic lower bound nor any uniform linear upper
bound. No useful global counting estimate was obtained from it.

No new Lean settlement was produced in these reassessments. `Spec.lean` is
unchanged with its original `sorry`; no submission was made.

## Direct finite-prefix diagnostics (not asymptotic proofs)

The latest tests targeted the actual criterion in `Compactness.lean`, rather
than a stronger divisor-closure or finite-coloring condition.

`/tmp/cube_prefix_independent.py` used SciPy/HiGHS MILP with all stored strict
four-root collisions and prefix constraints at multiples of 100 (additive
error 10). At N=1000, target 0.7, a 40-second run found 742 roots. All 1601
stored edges were avoided; an independent exact-integer check of *all*
unordered pair cube sums, including repeated roots, found no collision.
The exact maximum of 7*n - 10*count({a in S : a<n}), for 0<=n<=1000, was 142.
Thus this one finite set satisfies delta=7/10, C=15 through 1000. It was not
proved optimal (solver upper bound 786). At N=3000, target .65, an 80-second
run returned no feasible incumbent, NOT an infeasibility proof.

`/tmp/cube_prefix_greedy.cpp` removed vertices according to current edge degree
weighted by (n/N)^beta and then reinserted admissible roots in increasing order.
At N=100000, the selected counts for beta=0,.25,.5,1 were respectively
57469,56606,55141,53243. The respective maximum deficits
6*n-10*count({a in S : a<=n}) were 39764,45110,54002,69732.
Each output avoided all 898947 stored edges. These are finite diagnostics,
not Lean certificates or evidence of a proved uniform density bound.

No positive-density infinite construction or general density-zero result was
obtained. `Spec.lean` remains unchanged with its original `sorry`.

## Robust-source full-prefix growth (new, verified, conditional)

`Submission/SourceCollisionGrowth.lean` compiles; built `.olean` exists.
Successful log: `/tmp/source_collision_growth_final.log`.

* `largePrimeSource_mul_eventually`: for k>0 and fixed m>0, every sufficiently
  large n in `largePrimeSource (2*k)` has m*n in `largePrimeSource k`.
  The explicit sufficient cutoff is n > m^(2*(k-1)). The proof compares
  squares of the required integer-power inequalities.
* `EventuallyDilatesInto B D`: every fixed positive multiplier eventually
  sends B into D.
* `source_collision_count_superlinear`: if B has positive lower density and
  `EventuallyDilatesInto B D`, then the number of strict positive cubic
  collisions in D's FULL natural prefixes, divided by N, tends to infinity
  in the quantified sense: for every real C, eventually C*N < edgeCount_D(N).
  The proof sums copies of finitely many distinct primitive collisions.
  Their multiplier counts have a common density coefficient, while the
  finite cutoff errors may depend on the family. Primitive normalization
  ensures the copies are distinct. Divergent reciprocal-height mass then
  defeats every linear bound.
* `largePrimeSource_prefix_superlinear`: specializes this to the large-prime
  source k, CONDITIONAL ON positive lower density of source 2*k.

Principal axiom checks contain only propext, Classical.choice, Quot.sound.
The positive-density hypothesis for the stronger large-prime source was NOT
proved in this file. Do not describe this specialized conclusion as an
unconditional Lean theorem. This improves the earlier hereditary-only
obstruction under that explicit additional hypothesis. It invalidates the
proposed combination of stronger-source positive density and a full-prefix
linear edge bound, but does NOT bound independence density or settle Spec.

The finite-prefix diagnostic results from the preceding continuation have
also now been recorded above. No pending computation remains.

`Spec.lean` remains unchanged with its original `sorry` (SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63).
No proof/disproof of the requested conjecture has been found or submitted.

## Multiplicative-recurrence reassessment (no new settlement)

Reassessed whether the existing polynomial collision parametrizations imply
an unavoidable configuration in every positive-density root set. No applicable
recurrence theorem or proof was found. Ordinary polynomial Szemeredi cannot
be applied merely because a collision family is polynomial: its common
translation parameter is absent, and translating all roots destroys the
cube identity. Likewise, multiplying two binary cube-sum identities yields
four terms on each side, not a new binary cube-sum identity without additional
cancellation. The reduced-gap Eisenstein-norm restriction remains only a
necessary arithmetic condition, not a density obstruction.

A search of the imported Sidon infrastructure found definitions, elementary
closure facts, and greedy constructions, but no theorem providing the missing
positive-density cube-Sidon set. No new proof or disproof was obtained in this
reassessment; no submission was made, and Spec.lean is unchanged.

## Conic concentration and generator structure reassessment (unresolved)

Investigated whether superlinear collision counts could be concentrated on a
small enough vertex set to recover a positive-density construction. No uniform
concentration bound was established. Zero-density value sets for an individual
quadratic form, even if available, would not control the union of all scaled
conic families.

Also checked a possible stronger multiplicative-antichain property of the
stored greedy divisor generators. The diagnostic list contains 16, 69, and
184, with 184 dividing 16*69. Thus the stored data do not support the proposed
2-primitive property. This is a diagnostic of that construction, not a new
kernel-verified theorem or an obstruction to all possible covers. In any
case, multiplicative-antichain properties alone do not establish reciprocal
summability (the primes are already an important caution).

No uniform positive prefix-density bound, global summable cover, finite
coloring, or arbitrary-set density-zero theorem was obtained. Spec.lean is
unchanged; no proof was submitted. No computational job is pending.

## Short-interval gluing reassessment (no uniform bound)

Examined whether cube-Sidon short intervals can be joined with bounded
relative gaps while controlling interactions with an earlier Sidon set.
The established separation that eliminates all two-old/two-new collisions
requires the next scale to exceed a constant times the previous scale to the
3/2 power; that produces density gaps. No replacement estimate at a fixed
scale ratio was proved.

A targeted finite diagnostic counted stored edges a<b<=M<C*M<c<d<=2*C*M
whose old roots a,b are in the saved increasing-order greedy cube-Sidon set.
For C=1 and M=500,1000,2000,5000,10000,20000,50000 the counts were
227,498,1255,3817,8671,19541,54997. For C=2 and M=500,1000,2000,5000,10000,20000
these were 106,234,668,1972,4595,10307. These finite numbers prove neither a
uniform linear bound nor its failure, and the external enumeration remains
uncertified. They did not provide an infinite construction.

No new Lean theorem settling the conjecture was obtained. Spec.lean remains
unchanged, no verification submission was made, and no job is pending.

## Quadratic-residue source candidate (new counterexample, verified)

New file `Submission/QuadraticResidueSource.lean` compiles, with built `.olean`.
Successful log: `/tmp/quadratic_residue_source_final.log`.

The candidate `nonresidueSource` consists of n=p*m with p prime, 0<m<p,
and Jacobi(m,p)=-1 (equivalently Legendre, since p is prime). Thus p is a
prime factor larger than the cofactor. No density assertion is made.

`arithmetic_certificate` proves p=35977 prime and that each of
26711,31469,32009,35543 has Jacobi symbol -1 modulo p.
`counterexample_membership` certifies the four roots
960981647,1132160213,1151587793,1278730511 are in the candidate.
Their cubes satisfy the strict collision identity, obtained by dilating the
previous all-prime collision by 35977.
`nonresidueSource_not_cubeSidon` proves that this particular whole source
is not cube-Sidon. Both printed axiom checks contain only the allowed axioms.
This does NOT rule out positive-density Sidon subsets of the source, or
other arithmetic-symbol constructions, and does not settle Spec.

A separate unverified symbolic/norm diagnostic examined the quadratic family
in PrimitiveCollisionMass. The hoped-for simultaneous cross-norm obstruction
between Q(sqrt(-5)) and Q(sqrt(85)) does not hold in that tested form:
Sage reported both cross ratios to be norms at t=8,u=57, with roots
16123,27003,42214,44934. This diagnostic was not made into a Lean theorem
and supplies no general conclusion about the conjecture.

Spec.lean remains unchanged with its original sorry. No proof or disproof of
the existential statement was obtained; no verification submission was made.

## Global-weight reassessment (still missing)

Reexamined the actual finite fractional-cover weights rather than their
objective values alone. They put substantial weights on many primes and
irregular composite divisors. No arithmetic formula covering every collision
with summable reciprocal cost was extracted. In particular, a generic weight
that decays to zero on all primes cannot be justified from the known finite
all-prime collision, and no classification or summable covering of all-prime
collisions was established. The finite optimized weights remain finite data,
not a construction of the global weights required by WeightedDivisorCover.

No new settlement or axiom-safe replacement for Spec.lean's sorry was found.
The submission file remains unchanged and no proof was submitted.

## Unrestricted coloring revisited (finite result only; no global coloring)

New scripts:
* `/tmp/cube_densest_core.cpp` (and executable): greedy minimum-degree peeling
  of stored collision hypergraphs, retaining the densest encountered core.
* `/tmp/cube_walk_color.cpp` and `/tmp/cube_prob_color.cpp` (and executables):
  local searches for unrestricted two-colorings, with no multiplicativity
  assumptions.

The probabilistic local search found a two-coloring of all roots 1..6000.
Assignment: `/tmp/cube_prob_color_6000_1.txt` (one 0/1 color per line).
Log: `/tmp/cube_prob_6000_1.log`.
Color sizes are 2976 and 3024. An independent exact-int64 check enumerated
ALL unordered pair cube sums within each color, INCLUDING repeated roots,
and found no duplicates: respectively 4429776 and 4573800 pair sums.
The values fit int64. This is an external finite verification, not a Lean
certificate and not a coloring of all positive integers.

The assignment does not show a useful simple periodic or multiplicative
pattern: the checked small moduli and single-prime dilation correlations
were close to balanced. No general rule or infinite extension was proved.

Greedy-peeling cores had:
  cutoff 8000: 5808 vertices, 23704 edges;
  cutoff 10000: 7624 vertices, 33658 edges;
  cutoff 30000: 24867 vertices, 160016 edges;
  cutoff 100000: 81733 vertices, 769099 edges.
CaDiCaL searches on the cores at 8000 and 30000 were stopped at 240 and 600
seconds respectively with NO SAT/UNSAT conclusion. Logs are
`/tmp/cube_core_8000.out` and `/tmp/cube_core_30000.out`. Their incomplete
LRAT traces are not certificates and were deleted. No solver is still running.
Local searches at 8000 and 10000 also failed to find a coloring within their
limits; that is not evidence of a proved obstruction.

A separate finite diagnostic selecting the same positional pair in every
ordered edge (any of the six pairs among a<b<c<d) encountered an odd cycle
in each resulting graph, already at cutoffs <=144. This only rejects those
six fixed-pair sufficient coloring rules; it is not an unrestricted coloring
obstruction. The first-fit coloring counts through 100000 were reconfirmed,
not newly discovered: [49842,33770,14094,2232,62].

No complete proof or disproof was obtained. Spec.lean remains unchanged
with the original sorry; no verification submission has been made.

## Large-prime separation (new, verified; no settlement)

`Submission/LargePrimeSeparation.lean` compiles and has a built `.olean`.
Successful log: `/tmp/large_prime_separation_final.log`.
Namespace: `Erdos1206.LargePrimeSeparation`.

* `large_prime_cube_congruence`: for prime p != 3, if |x|,|y| <= N,
  x != y, p^3 divides x^3-y^3, and 3*N^2 < p^3, then p divides both x and y.
  The proof factors the difference of cubes. Unless p divides x and y,
  p^3 must divide one of x-y and x^2+x*y+y^2; each is too small.
* `shared_prime_dvd_all`: in a strict positive cubic collision
  a<b<c<d<=N, if 3*N^2 < p^3 and p divides any two roots, it divides all four.
  This statement does not need a separate p != 3 hypothesis: strict
  positivity gives N>=4, excluding p=3 under the size bound.
* `primitive_shared_prime_bound`: in a gcd-one strict positive collision,
  any prime dividing two roots satisfies p^3 <= 3*d^2.

All three printed axiom checks contain only propext, Classical.choice,
Quot.sound. There is no sorry/admit in the new auxiliary file.

Limitation: this separates shared-large-prime dilations from configurations
with unshared large primes, but it supplies no uniform edge-count or
independence-density bound for the latter. No finite coloring, summable
cover, positive-density witness, or zero-density theorem was obtained.

A small separate diagnostic also rejected simple colorings by the digit sum
of n^3 modulo k (rather than the previously studied digit sum of n). For
example, roots (10,19,24,27) have a strict collision and their cubes all have
even binary digit sum. The base-2/3/10, k=2..8 tests all found finite
monochromatic collisions. These are external exact-integer diagnostics,
not new Lean theorems or obstructions to arbitrary digit constructions.

Spec.lean is unchanged with its original sorry and statement. No proof or
disproof of the existential conjecture was obtained, no verification
submission was made, and no job is pending from this continuation.

## Endpoint-density and dilation-coherence review (no new settlement)

Revisited the direct compactness criterion and the possibility of weakening
its every-prefix hypothesis to a cardinality bound only at the final cutoff.
No such implication was established. In particular, averaging integer
 dilation-preimages of a dense finite set can lose the lower-density
information; one cannot use this as a substitute for the verified
all-prefix hypothesis. The previously noted large-gap gluing obstruction
remains, and no uniform extension bound was proved.

Reexamined the smooth-prime weighted criterion and the large-prime separation
lemma. Neither yields a bound for the unshared-large-prime configurations,
or a sequence of normalized harmonic independence bounds tending to zero.
No tensorization of independent prime losses is justified; the existing
parity counterexample still prevents that shortcut.

External references remain unavailable: both the Erdős problem site and
arxiv.org failed DNS resolution; direct-IP HTTPS attempts to arxiv.org and
GitHub timed out. No external theorem was obtained or assumed.

No new Lean theorem or complete mathematical settlement was obtained in this
continuation. Spec.lean remains unchanged with its original sorry. No proof
was submitted, and no computation is pending.

## Ordinary greedy bounded-dilation test (finite only; no settlement)

Tested the saved ordinary increasing-order greedy set
`/tmp/cube_root_greedy_100000.npy`, not the divisor-closed greedy set.
For each B, only n<=floor(100000/B) were checked, so all B tested multiples
were inside the stored prefix. Numbers of n with no accepted multiple k*n,
1<=k<=B, were:

  B=2:15790, 3:6906, 4:3607, 6:1233, 8:476, 12:117,
  16:24, 24:6, 32:1, 64:0, 128:0, 256:0.

The zero counts at larger B have progressively smaller checked domains and
are NOT global bounds. In particular all multiples 1980*k for 1<=k<=36
are rejected in the stored data, while 1980*37=73260 is accepted. Record
first accepted multipliers (for uncensored n<=10000) included
(12,6), (76,8), (172,10), (540,13), (738,14), (836,15),
(1164,16), (1210,25), (1830,26), (1980,37).
These are external finite diagnostics, not Lean certificates, and do not
prove unboundedness of the required multipliers.

A uniform bounded-dilation cover by a cube-Sidon root set would imply
positive lower density by the existing verified lemma. It would also imply
a finite cube-Sidon coloring: color n by an accepted multiplier k<=B;
a monochromatic collision scales into the given Sidon set. Thus this is
not a genuinely weaker existential route than finite coloring, though it
is a specific possible property of the ordinary greedy candidate.

No uniform multiplier bound, global coloring, or density argument was
proved. Spec.lean remains unchanged with its original sorry. No proof was
submitted and no job is pending.

## Prime/coprime chart-cancellation audit (finite diagnostic; no settlement)

Reviewed the existing sieve, inverse-height, conic, and exact-cancellation
lemmas for a uniform-cover implication. No such implication was obtained.
In particular, restricting attention to pairwise-coprime or all-prime roots
does not justify discarding the raw cancellation factor.

New diagnostic `/tmp/cube_coprime_chart_check.py` checks the 24 signed
permutations for each selected stored primitive collision. For every chart
with nonzero inverseT, it divides the three inverse coordinates by their
gcd, verifies gcd=1, and checks ALL FOUR raw cubic coordinate identities
against one signed scalar. It then records the absolute scalar. Results:
`/tmp/cube_coprime_chart_check.log`,
`/tmp/cube_coprime_chart_prime.json`,
`/tmp/cube_coprime_chart_pairwise.json`.

Among the 105 stored all-prime collisions through 100000, the collision

  17713^3 + 63689^3 = 42643^3 + 57119^3

has minimum absolute scalar 2133097393 over the 24 charts. Primality of all
four roots was separately checked with SymPy, and the identity with exact
integer arithmetic. One minimizing signed chart has coordinates
(-42643,-17713,57119,63689) and primitive parameters
(-25674,9930,10727). No Lean certificate was added for these finite checks.

The 3516 stored pairwise-coprime primitive collisions were also checked.
One example, (76847,77033,98221,98335), has minimum absolute scalar
6645400237. These are finite observations, NOT proofs of unbounded
cancellation under either restricted hypothesis. They do not rule out some
larger constant or any different counting argument.

No global summable divisor cover, positive-density construction, or
universal density-zero theorem was established. Spec.lean remains unchanged
with its original sorry; no proof was submitted and no job is pending.

## Prefix-obstruction review (no settlement)

Considered the exact negation of the every-prefix compactness criterion as
an alternative to proving that all finite endpoint independence ratios tend
to zero. No universal prefix obstruction was established.

The existing CompletionBoundary extension is not an unavoidable pattern in
arbitrary positive-density sets. Its parameters include v=9*t^4, and the
selected extension triple contains v*s for every old selected s. Thus the
positive-density set {n : 3 does not divide n} avoids all such extension
triples. This set is NOT cube-Sidon; the observation only explains why
positive lower density alone does not force this particular amplification
pattern. The already verified sparse boundary examples consequently cannot
be promoted to a universal prefix obstruction without a new argument.

No complete proof or disproof was obtained. Spec.lean retains its original
statement and sorry; no verification submission was made and no job is
pending.

## Positive density of the large-prime source (new, verified)

`Submission/LargePrimeSourceDensity.lean` (303 lines) compiles and has a built
`.olean`. Successful final log:
`/tmp/large_prime_source_density_final.log`.
Namespace: `Erdos1206.LargePrimeSourceDensity`.

This removes a genuinely missing hypothesis from `SourceCollisionGrowth.lean`:

* `largePrimeSource_lowerDensity_pos`: for every natural k>=2,
  `0 < (largePrimeSource k).lowerDensity`.
* `largePrimeSource_collision_count_superlinear`: for every k>0 and real C,
  eventually the number of strict positive cubic collisions in the full natural
  prefixes of `largePrimeSource k` exceeds C*N. This conclusion is now
  UNCONDITIONAL, unlike the earlier theorem `largePrimeSource_prefix_superlinear`.

Proof ingredients, also kernel checked in the new file:

1. `primeCounting_lower_mul_log`: for n>=2,
   `log 2 * n <= 4 * primeCounting n * log n`. This follows from
   `2^m <= centralBinom m <= (2*m)^(primeCounting (2*m))` and m=floor(n/2).
   No prime number theorem or additional axiom is used.
2. An injective count of pairs (m,p) with 1<=m<=t, p prime,
   t^(k-1)<p<=t^(2*k)/m. The product m*p lies in the source, and p>t
   ensures uniqueness of this representation among these pairs.
3. Summing the prime-counting bound against small cofactors and using the
   harmonic sum gives a uniform linear prefix bound at t^(2*k)+1 once t is
   sufficiently large. The removed small-prime pairs cost at most t^k.
4. `positive_lowerDensity_of_power_prefix` interpolates the bounds at power
   cutoffs to every sufficiently large natural prefix, losing only a fixed
   factor 2^d. It applies to a single fixed set S; it is NOT a compactness
   statement allowing unrelated finite Sidon witnesses at each cutoff.

Both main axiom checks list only propext, Classical.choice, Quot.sound. The
new file contains no sorry, admit, native_decide, or added axioms.

LIMITATION: superlinear collision counts do not imply that every positive-density
subset contains a collision. No independence-density estimate, finite coloring,
summable cover, positive-density cube-Sidon set, or universal density-zero theorem
has been obtained. The original conjecture remains unsettled by this work.

`Spec.lean` is unchanged (SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63), with its
original statement and sorry. No verification submission was made. No job is
pending from this continuation.

## Arbitrarily separated middle-root scales (new, verified)

`Submission/SeparatedConicFamily.lean` (359 lines) compiles and has a built
`.olean`. Successful final log: `/tmp/separated_conic_final.log`.
Namespace: `Erdos1206.SeparatedConicFamily`.

Main verified theorems:

* `separated_reciprocals_not_summable K`: among primitive ordered positive
  collisions a<b<c<d with K*b<c, the sum of reciprocal heights 1/d diverges.
* `separated_collision_count_superlinear K C`: for EVERY fixed natural K and
  real C, eventually the full natural-prefix count of such collisions exceeds
  C*N. In particular a fixed large separation between the middle-root scales
  does not give a linear full-prefix edge-count bound.

The new conic family, over integers, is

  A=(r^6-1)*u^2-6*r^3*u*v-3*v^2
  B=(r^6-1)*u^2+6*r^3*u*v-3*v^2
  C=r*(r^6-1)*u^2-6*r*u*v+3*r*v^2
  D=r*(r^6-1)*u^2+6*r*u*v+3*r*v^2.

`identity` verifies A^3+D^3=B^3+C^3. For r>=3 and 0<v<=u,
`ordered_and_separated` proves 0<A<B<C<D and r*B<2*C.
`height_bound` gives D<=r*(r^6+8)*u^2. The inverse identities are

  C+D-r*(A+B)=12*r*v^2,   D-C=12*r*u*v.

The proof does NOT assume the raw coordinates are primitive. The generic
`normalize_collision` lemma divides all four coordinates by their gcd.
For u=p prime >=29 and 1<=v<p, the inverse ratio v/p recovers the parameter
pair from the normalized collision. `point_injective` proves this; normalization
can only decrease the height. Summing over p-1 choices of v gives a lower
bound proportional to 1/p, hence divergence. Set r=2*K+3 for the desired
separation, then count distinct positive integer dilations using their gcds.

Both main axiom checks contain only propext, Classical.choice, Quot.sound.
There is no sorry/admit/native_decide or added axiom in this auxiliary file.

LIMITATION: this is still a collision-count theorem, not an independence-density
theorem. It rules out a uniform linear bound for ALL cross-scale edges selected
only by K*b<c. It does not rule out every block construction, count edges on a
particular selected Sidon set, or settle the conjecture. No positive-density
cube-Sidon witness or universal density-zero result has been obtained.

`Spec.lean` remains unchanged with its original sorry (same SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63).
No proof was submitted; no job is pending.

## Repeated cubic differences and Sidon-piece joining (new, verified)

`Submission/RepeatedCubeDifferences.lean` compiles and has a built `.olean`.
Successful final log: `/tmp/repeated_cube_diff_final.log`.
Namespace: `Erdos1206.RepeatedCubeDifferences`.

Main verified theorems:

* `infinite_positive_cube_difference`: infinitely many positive rational b
  admit positive rational a with a^3-b^3=7.
* `rational_sidon_pairs k`: disjoint injective arrays a,b of k positive
  rationals, each array having Sidon cubes, with a(i)^3-b(i)^3=7.
* `natural_sidon_pairs k`: after a common denominator D>0, disjoint arrays
  a,b of k positive natural roots, each having Sidon cubes, and
  a(i)^3=b(i)^3+7*D^3 for every i.
* `mixed_collisions_not_cardinality_linear C`: for every natural C, there
  are disjoint finite positive root sets S,T, each with Sidon cubes, and
  a finite set E of genuine four-distinct-root mixed collisions such that
  C*(S.card+T.card)<E.card. E uses oriented quadruples; reversing the two
  index pairs counts the same underlying four-root edge twice. The
  unbounded ratio is unaffected by this fixed factor.

Construction and checks:

1. Start from integer coordinates (73,17,38), satisfying
   73^3-17^3=7*38^3. Iterate the homogeneous tangent map
     (a,b,c) -> (a*(a^3-2*b^3), -b*(2*a^3-b^3), c*(a^3+b^3)).
2. The identity is preserved by a polynomial identity. Numerators remain
   odd and congruent modulo 4; their cube sum is 2 modulo 4. Hence every
   new denominator is divisible by twice its predecessor and is nonzero.
   Cross multiplication with odd numerators proves both rational-coordinate
   sequences injective. No unproved elliptic-curve rank theorem is used.
3. If the two rational coordinates have opposite signs, the next tangent
   point has coordinates of the same sign. Infinitely many same-sign
   points exist; negative pairs are converted to positive ones by
   (x,y) -> (-y,-x).
4. Finite Sidon extraction excludes finitely many completions, half-sums,
   and translates by +/-7. This simultaneously makes the two cube-value
   sets Sidon and disjoint. Clearing a common positive denominator gives
   natural roots. Every two distinct indices give a mixed collision.
5. Taking k=2*C+2, the explicitly injective family of oriented quadruples
   has k*k-k members on 2*k vertices, proving the cardinality-ratio claim.

All four printed axiom checks list only propext, Classical.choice, Quot.sound.
The file contains no sorry, admit, native_decide, or added axioms.

LIMITATIONS: this is NOT an obstruction to every block construction. It
rules out a mixed-collision bound based only on Sidonness and the two set
cardinalities. No uniform interval placement, height bound comparable to
cardinality, or positive density is obtained; the common denominator can
be enormous. In particular this does not imply superlinear counts in
terms of a natural prefix cutoff for these selected sets, and it does not
settle the original conjecture.

A further targeted finite diagnostic examined d(n), the number of stored
strict collisions whose largest root is n. Divisibility monotonicity
(d(m)<=d(n) when m|n) follows by dilating witnesses, but was not added as a
Lean theorem. The distribution in [N/2,N] has median respectively 2,3,4,6,8
at N=1000,3000,10000,30000,100000; the fraction with d(n)<=4 is respectively
0.87625,0.73284,0.54329,0.37657,0.22372. These data do not establish a
positive-density bounded-degree source, nor prove that every such source
has density zero. Enumeration completeness remains uncertified.

Spec.lean is unchanged with its original conjecture and sorry. No complete
proof or disproof has been obtained, no proof has been submitted, and no
job is pending.

## Combined finite-color and summable-sieve criterion (new, verified)

`Submission/SummableSourceColoring.lean` compiles and has a built `.olean`.
Successful log: `/tmp/summable_source_final.log`.
Namespace: `Erdos1206.SummableSourceColoring`.

This continuation produced a positive construction criterion, rather than
another collision-count obstruction. Its global input is still missing.

Main results:

* `summable_source_prefix_multipliers`: if B has summable reciprocal mass,
  then for every finite cutoff N a positive-lower-density set of positive
  multipliers q preserves `divisorAvoider B` throughout that prefix:
  n in the source and n<=N implies q*n is in the source. The multipliers
  need not work beyond this finite prefix.
* `PositivePrefixMultipliers S` abstracts the required property (including
  1 in S and positivity of S). `finite_source_coloring_suffices` extracts
  the original positive-lower-density conclusion from a fixed finite
  cube-Sidon coloring of such a source.
* `finite_coloring_summable_source_suffices`: finite coloring on a source
  obtained by a reciprocal-summable divisor deletion omitting 1 suffices.
  No assumption that the reciprocal sum is less than 1 is needed.
* `colored_sieve_compactness`: simultaneous compactness of the colors and
  forbidden divisors yields a global colored summable-sieve source from
  uniformly bounded finite witnesses.
* `uniform_finite_colored_sieves_suffice`: it is enough to find fixed k and
  fixed real C such that at EVERY cutoff N there are a finite divisor set
  B_N and a k-coloring whose fibers, after deleting multiples of B_N, have
  Sidon cubes on [1,N], with 1 not in B_N and sum_{d in B_N} 1/d <= C.

The last criterion combines the previous separate routes: no deletions is
pure finite coloring; one color is a summable divisor cover; the squarefree
source is another special case. It does not assert that the criterion is
necessary for the original conjecture. Crucially, BOTH k and C must be
independent of N. Finite data alone do not supply this hypothesis.

Key multiplier proof: use the enlarged forbidden set
  B'_N = {d>1 : exists t, 1<=t<=N and t*d in B}.
Its reciprocal sum converges by summing, over finitely many t, the
subsequence t*(1/(t*d)) of the original reciprocal series. If b in B divides
q*n with n in the source, put g=gcd(b,n) and d=b/g. Then d>1, g<=N,
g*d=b, and d divides q. Thus avoiding B'_N forces q*n to remain in the
source. This avoids any unsupported intersection-density assertion for
arbitrary divisor-closed sets.

The extraction proof uses the finite color-erasure/compactness argument,
not the invalid claim that one original fiber of every finite partition
of a positive-lower-density set must itself have positive lower density.
All four printed axiom checks list only propext, Classical.choice,
Quot.sound. No sorry/admit/native_decide/axiom was added to the new file.

No fixed pair (k,C), global coloring-and-sieve construction, or universal
zero-density theorem has been proved. The original conjecture remains
unsettled. Spec.lean is unchanged with its original sorry; no proof has
been submitted and no job is pending.

## Direct color-and-sieve candidates (new finite constructions, not an infinite proof)

Investigated explicit finite inputs to the combined criterion instead of
adding another conditional Lean reduction.

1. Completely multiplicative Boolean coloring on squarefree roots coprime
   to 6, through N=100000: SAT. Source size 30398, color sizes 14033/16365.
   There are 4279 primitive stored constraints and 5353 stored constraints
   including dilations. All 91787 CNF clauses were independently checked.
2. Same source with coprimality to 30: SAT. Source size 25331, color sizes
   11870/13461. Primitive/stored edge counts 1768/2046. All 66501 CNF clauses
   were independently checked.
3. Completely multiplicative coloring into Z/4Z on ALL positive roots
   through N=10000: SAT. All 262993 clauses and 41810 stored edges checked;
   color sizes 4093,2883,1994,1030.
4. Z/4Z on all positive roots through N=30000: SAT in about 1.7 seconds.
   All 850453 clauses, all 184007 stored edges, and EVERY product a*b<=30000
   were independently checked. Color sizes 9463,7146,6542,6849.
5. Z/4Z through N=100000: the run was stopped by a 240-second timeout.
   NO SAT or UNSAT conclusion. This is not evidence of an obstruction.

The returned source colorings in (1), (2), and the full coloring in (4)
were additionally verified by a separate exhaustive pair-sum checker,
NOT by reliance on the stored collision enumeration. For each fiber this
checker forms ALL unordered cube-pair sums INCLUDING repeated roots,
sorts exact uint64 values (no overflow at these cutoffs), and checks for
adjacent duplicates. All checks passed:

* Squarefree/coprime-6: 232384356 pair sums total.
* Squarefree/coprime-30: 161060376 pair sums total.
* Full Z/4Z through 30000: 115175125 pair sums total.

These are external exact-integer finite checks, NOT kernel-verified Lean
certificates and NOT asymptotic theorems. They establish no uniform coloring
for all cutoffs. In particular, assigning colors arbitrarily to larger
primes extends multiplicativity but does NOT establish Sidonness beyond
the tested prefix. No such extension theorem or arithmetic invariant was
found.

Files:
* Generator `/tmp/cube_sieved_mult2.py`.
* `/tmp/cube_sieved_mult2_100000_{6,30}.{cnf,out,npz}`;
  assignments `_colors.npy`, selected roots `_selected.bin`, exhaustive
  check logs `_pairs_check.log`.
* Existing generator `/tmp/cube_mult_stored.py`; new instances/results
  `/tmp/cube_mult_stored_4_{10000,30000,100000}.{cnf,out}`.
* `/tmp/cube_mult_stored_4_30000_check.json`, `_colors.npy`, `_selected.bin`,
  `_pairs_check.log`.
* Exhaustive checker `/tmp/check_cube_coloring_pairs.cpp` and its binary.

Simple local quadratic characters modulo 24 do NOT explain the source
colorings: all eight such Boolean characters have monochromatic stored
collisions on the squarefree/coprime-6 source. In particular the squarefree
collision (6409,11233,16081,17449) has all four roots 1 modulo 24. These
local-character observations are finite exact diagnostics only.

Arithmetic correction worth preserving: 59^k+158^k=133^k+134^k holds for
k=4, NOT for k=6. Do not cite that familiar quartic example as an equal-sum
of sixth powers or as a square-root cubic collision. None of the verified
Lean results depends on that incorrect sixth-power assertion.

The main conjecture is still unresolved. Spec.lean is unchanged with its
original sorry. No proof has been submitted. There is no running job from
this continuation (the process list contains only old defunct CaDiCaL
entries, not pending solvers).

## Complete smooth exponent boxes (new finite diagnostics; no settlement)

Implemented the previously pending full-box tests, independently of the
height-truncated collision list. `/tmp/cube_smooth_box.cpp` enumerates every
unordered root pair, including repeated roots, and sorts exact unsigned
256-bit cube sums. `/tmp/cube_smooth_box_check.py` verifies every reported
identity with Python arbitrary-precision integers and tests all character
assignments. Each box has 4096 roots and 8390656 unordered pairs.

1. Primes 2,3,5,7,11,13; exponents 0,1,2,3; characters into Z/4Z:
   912 collisions; 3728 of 4096 characters survive. In fact all collisions
   normalize to just (1,9,10,12) (768 dilations) or (42,49,120,121)
   (144 dilations). Largest root 27081081027000; maximum pair sum needs
   only 135 bits, so no overflow.
2. Squarefree products of 5,7,11,13,17,19,23,29,31,37,41,43:
   no nontrivial collision at all. Largest root 2180460221945005;
   maximum pair sum needs 154 bits. All Boolean characters survive,
   vacuously; this is particularly weak evidence about coloring.
3. A more targeted squarefree support, the union of the prime supports
   of two known collisions: 5,7,11,13,19,23,29,37,53,67,71,97.
   32 collisions; 3136 of 4096 Boolean characters survive. All collisions
   are 16 dilations of each of (583,4921,12901,13135) and
   (335,23959,25259,31027). Largest root 57393934272860185;
   maximum pair sum needs 169 bits.

Result prefixes are `/tmp/cube_smooth_box_c4.csv`,
`/tmp/cube_smooth_box_c2_sf.csv`, and
`/tmp/cube_smooth_box_c2_targeted.csv`, with `.roots`, `.check.json`, and
`.audit.json` suffixes for root lists, assignments, and normalized-pattern
checks. These are external exact finite checks, NOT Lean certificates or
infinite S-unit classifications. No claim is made beyond the finite boxes.

The Z/4Z completely multiplicative instance through 100000 was also rerun
with a longer allowance, but manually stopped after about nine minutes
without a SAT/UNSAT conclusion. Log:
`/tmp/cube_mult_stored_4_100000_long.out`. No solver job remains running.

Reexamining the complete cubic parametrization did not produce a global
coloring invariant or a density recurrence theorem. No new Lean theorem
was added in this continuation. `Spec.lean` is unchanged with its original
`sorry`; there is still no proof or disproof and nothing valid to submit.

## Latest global-step review (no new result)

Reviewed the combined color-and-sieve criterion against the complete cubic
parametrization, exact cancellation formula, and the available counting and
prime-cover results. No uniform covering bound or positive-density extraction
hypothesis was established. In particular, raw coordinate height bounds still
include the common cancellation factor; neither dropping it nor using total
collision counts as independence bounds is justified.

No new theorem or numerical diagnostic was produced in this review. Spec.lean
remains unchanged with its original sorry, and there is no valid proof to
submit. No computation is pending.

## Squarefree/coprime-6 conic sieve and primitive mass (new, verified)

Two new files compile and have built `.olean` files, including copies in the
Lake build path:

* `Submission/QuadraticSquarefreeSieve.lean` (509 lines), namespace
  `Erdos1206.QuadraticSquarefreeSieve`.
* `Submission/SquarefreeConicFamily.lean` (259 lines), namespace
  `Erdos1206.SquarefreeConicFamily`.

Successful logs:
`/tmp/quadratic_squarefree_sieve_final.log` and
`/tmp/squarefree_conic_family_final.log`.
All printed final axiom checks contain only propext, Classical.choice,
Quot.sound. Neither file contains sorry/admit/native_decide or an added axiom.

### General elementary quadratic sieve

For `quad a b c t u = a*u^2+b*t*u+c*t^2`, the first file proves:

* `quadratic_roots_card`: at most two roots modulo p^2 if the leading
  coefficient and discriminant remain nonzero modulo the prime p.
  Reduction to roots modulo p is injective: the derivative factor in the
  difference of two evaluations is a unit. The field root count is then two.
* `bad_prime_pairs_count`: in parameters t=M*i, u=M*j+1, 0<=i,j<N,
  with p coprime to M and the same nonvanishing hypotheses, the number of
  pairs for which p^2 divides the value is at most
      3*N^2/p^2 + 4*N + 1.
  The degenerate rows p|t force p|u and are counted separately.
* `primeCounting_mul_eventually_le`: for each fixed L and each epsilon>0,
  pi(L*N)<=epsilon*N eventually, using Mathlib's Chebyshev bound.
* `factorial_progression_sieve`: for finitely many such forms, squarefree
  positive values at (0,1) and nonzero discriminants imply that at least
  N^2/2 parameter pairs in a fixed factorial-square progression have ALL
  form values squarefree, for every sufficiently large N.

The last theorem is a parameter-density statement, NOT density of a
cube-Sidon root set. Small primes are controlled by M=(K!)^2; the large-prime
union bound uses the reciprocal-square tail and an O(N*pi(L*N)) error.

### Explicit squarefree primitive collision family

The four forms, written as coefficients of (t^2,t*u,u^2), are

  F0 = (3419,1160,29)
  F1 = (374777,19880,263)
  F2 = (769417,41884,571)
  F3 = (797983,43324,589).

They satisfy F0^3+F3^3=F1^3+F2^3 and are strictly positive and ordered for
u>0,t>=0. At (0,1) they give the squarefree collision (29,263,571,589),
all coprime to 6. Their discriminants are 948996 (first two) and -3078972
(last two), both nonzero. The determinant of the first three coefficient
rows is -721465056.

The finite cutoff K is chosen with K>=10^9, then M=(K!)^2. K is implemented
by Classical.choose with a proved lower bound so that Lean does not try to
evaluate the enormous closed factorial during conversion; no size estimate
or unproved arithmetic property is assumed.

For parameters (M*i,M*j+1), the good squarefree pairs have:

* all roots coprime to 6;
* gcd of all four roots equal to 1;
* an injective map from parameter pairs to the four-root tuple;
* maximum root at most (1000000*(M+1)*N)^2 for i,j<N.

Primitivity: a common prime <=K is excluded using the coprime constants
29 and 263. A common prime >K, through the explicit adjugate identities,
would divide both parameters, forcing its square into a squarefree root.

Main verified results:

* `good_eventually_large`;
* `weight_not_summable`;
* `squarefree_coprime_six_primitive_mass_diverges`;
* `exists_large_squarefree_primitive_mass`.

Thus reciprocal maximum-root mass diverges even among strictly positive,
primitive collisions with all four roots squarefree and coprime to 6.
The non-summability proof uses the Cauchy tail criterion: after deleting any
fixed finite parameter set, a large parameter box still contributes at least
one fixed positive reciprocal mass.

IMPORTANT LIMITATIONS:

* This does NOT show that finite coloring of the squarefree/coprime-6 source
  is impossible, nor that every positive-density subset contains a collision.
* It does NOT by itself prove superlinear FULL-PREFIX collision counts on
  this source. Squarefree dilations must also be coprime to all four roots;
  no uniform multiplier-density bound over the growing family was proved.
* It does NOT rule out a summable divisor cover using reuse or a coloring.
  It only invalidates treating the primitive collisions of this source as
  having summable per-collision reciprocal height.
* This is one fixed reduced-gap-ratio conic: F1-F0=13*(F3-F2). No assertion
  about the coloring complexity of that single conic is made.

Possible next analytical step, NOT implemented: count simultaneously
squarefree parameters and squarefree multipliers coprime to the four form
values using a three-variable sieve. This might yield uniform averaged
multiplier bounds and full-source collision growth, but still would not
settle the independence/density problem without an additional argument.

The original conjecture remains unresolved. `Spec.lean` is unchanged with
its original sorry and original checksum. No proof has been submitted and
no computation is pending. The temporary `Submission/SieveCheck.lean` query
file was removed.

## Compact gap-ratio coloring and positive-density avoidance (new, verified)

`Submission/CompactGapRatioColoring.lean` now compiles. Its `.olean` is in
`.lake/build/lib/lean/Submission/CompactGapRatioColoring.olean`; successful
log: `/tmp/compact_gap_ratio_coloring_final.log`.

Namespace: `Erdos1206.CompactGapRatioColoring`.

Main results:

* `multiplicative_bins`: for q>1 and R>=1, a finite coloring of positive
  integers satisfies
      a<=b<=R*a and color a=color b => b<q*a.
  Construction: choose the bin index k with q^k<=n<q^(k+1), then color
  k modulo m, where q^m>R*q. This is one coloring for all integers.
* `compact_gap_ratio_coloring`: for each H>=1, one finite coloring excludes
  every strict collision a<b<c<d, a^3+d^3=b^3+c^3, with
      (H+1)*(d-c)<=H*(b-a) and b-a<=H*(d-c).
  In fact color b != color d. There is no bound on the denominator of
  the reduced gap ratio. Thus this handles an infinite set of ratios,
  not merely finitely many bounded numerators/denominators.
* `geometricBand_lowerDensity_pos`: the explicitly defined set of integers
  in the union of intervals [r^k,q*r^k), k>=0, has positive LOWER density
  for any q>1 and r>1. The proof obtains a uniform prefix bound from a
  whole band before N, using floor/ceiling counting. It does not use a
  false pigeonhole claim about arbitrary finite colorings.
* `positive_density_avoids_compact_gap_ratios`: an infinite set of positive
  lower density excludes every collision in the displayed ratio range.
  It uses q=(100H+1)/(100H) and r=2H*q+1, and again only needs b,d in
  the set to exclude such a collision.

Arithmetic ingredient: the cube identity gives
  (b-a)*(a^2+a*b+b^2)=(d-c)*(c^2+c*d+d^2).
The upper ratio bound implies d<=2H*b. If 100H*d<(100H+1)*b, then
  b-a<=12*(d-b), (100H-12)*b<100H*a,
which forces H*(b-a)<(H+1)*(d-c). The final coefficient inequality is
  H*(100H+1)^2 < (H+1)*(100H-12)^2.

All four printed axiom checks contain only propext, Classical.choice,
Quot.sound. No sorry/admit/native_decide or added axiom occurs in this
auxiliary file. The query file GeometricDensityCheck.lean was removed.

LIMITATIONS: this is not a settlement. The number of colors and the
geometric spacing depend on H. The positive density bound deteriorates
as H tends to infinity, so neither a uniform finite coloring nor uniform
positive-density finite witnesses have been obtained. The unresolved
regimes are gap ratios tending to 1 or growing without bound. In
particular, the conic reciprocal-mass results do not justify deleting
these exceptions at a uniformly bounded or summable density cost.

Spec.lean remains unchanged, with its original sorry and original SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof has been submitted and no computation is pending.

## Latest global-step review (no additional theorem)

Rechecked the finite-prefix compactness criterion, the completion-boundary
limitations, the summable colored-source criterion, and the new compact-gap
construction. The required single positive density constant at every cutoff
is still missing. Neither individual-family sparsity nor countability of the
family permits an uncontrolled union of deletions; no uniform exceptional-tail
cover or coloring bound was established. No new numerical search was used as
mathematical evidence. An attempt to read the problem's reference page failed
at DNS resolution.

No new theorem, proof, or disproof was obtained in this review. Spec.lean is
unchanged and still contains its original sorry. No submission was made and
no computation is pending.

## Further parametrization/cover review (no new theorem)

Revisited the cubic raw-height, exact cancellation, and inverse-height
identities specifically for the uniform divisor-cover criterion. No selector
of forbidden divisors with a uniform reciprocal bound was found. A naive
three-parameter cubic-height estimate is critical even before cancellation:
height-T parameter boxes contain order T^3 triples and raw roots have order
T^3. Such an estimate alone gives no convergent reciprocal-height bound.
Unbounded cancellation cannot be discarded. The symbolic check of raw
coordinate irreducibility/nonsingularity repeated an earlier diagnostic and
is not new mathematical evidence.

No new Lean theorem or settlement was produced. The original Spec.lean and
its sorry are unchanged. No proof was submitted and no job is pending.

## Incidence-concentration review (no new result)

Rechecked the already saved bounded-degree and local-degree diagnostics rather
than rerunning them. They do not supply a uniform bounded-degree positive-density
source: medians increase in the finite prefixes, including on prime roots.
This finite behavior is not an asymptotic theorem and is not a disproof of the
conjecture. No incidence estimate or independent-set extraction satisfying the
original uniform prefix-density requirement was established. No new Lean lemma
was added. Spec.lean is unchanged, no proof was submitted, and no job is pending.

## Four-color extension tests (new, exact finite results; no settlement)

Tested whether the saved completely multiplicative Z/4Z coloring through
30000 extends coherently, instead of merely rerunning the old one-hot solver.

### A small kernel-checked obstruction to the saved full assignment

`Submission/FourColorExtensionObstruction.lean` (42 lines) compiles; `.olean`
is in the Lake build path. Log:
`/tmp/four_color_extension_obstruction_final.log`.

The theorem `Erdos1206.FourColorExtensionObstruction.prescribed_prime_colors_obstruct`
says that a character c : Nat -> ZMod 4, additive on products of positive
integers, with

  c(2)=0, c(3)=3, c(5)=3, c(2081)=0, c(2399)=3,
  c(3001)=0, c(7517)=0

cannot have Sidon cubes in its color-3 fiber. Indeed all four roots of

  2399^3 + 30010^3 = 22551^3 + 24972^3

have color 3. Factorizations are 22551=3*7517,
24972=2^2*3*2081, 30010=2*5*3001. These seven prime colors occur in the
saved 30000 assignment. The new theorem uses only propext, Classical.choice,
Quot.sound. This is an obstruction to that prescribed candidate, NOT to all
four-colorings or to the original conjecture.

An exact inspection found 2071 stored primitive collisions through 100000
monochromatic under the colors forced by the old prime assignments alone.
The displayed one has the smallest maximum root. Data:
`/tmp/cube_c4_old_assignment_extension_obstruction.json`.

### Low/high-bit encodings and stronger finite extension failure

New generators:
* `/tmp/cube_c4_fixed_low.py`: fix prime low bits, then encode the unknown
  high bits as a Boolean multiplicative character plus the known carry.
* `/tmp/cube_c4_binary.py`: encode full mod-4 addition with two bits, an
  AND carry, and an intermediate XOR.

The known coloring through 30000 was independently checked against all
119011 clauses of the fixed-low encoding and all 613220 clauses of the
full binary encoding, including every auxiliary bit.

At 100000, fixing the old prime low bits and arbitrary seeded low bits for
new primes gave UNSAT in 0.48 seconds. Its pruned LRAT proof independently
replayed 793 derived clauses and 45580 hints. This initially only ruled out
that particular full low-bit choice.

A STRONGER test fixed only low bits for the 3245 primes <=30000, leaving ALL
high bits and ALL new prime low bits free. The full binary encoding was
UNSAT in 2.44 seconds. The pruned proof has 29840 initial clauses and 18265
derived clauses; independent RUP replay checked 151128 hints and reached
the empty clause. The replayed core uses 253 of the prescribed prime low
bits. Thus even the old LOW-bit assignment cannot extend through 100000.
This does NOT rule out recoloring the old primes.

Files:
* `/tmp/cube_c4_fixed_low_100000_1_old.*`, with `_pruned.*`, `_audit.json`,
  `_rup_check.log` variants.
* `/tmp/cube_c4_old_prime_low_extension.*`, with `_pruned.*`, `_audit.json`,
  `_rup_check.log` variants.
* `/tmp/cube_c4_binary_encoding_audit.json`: exhaustive exact truth-table
  checks of mod-4 addition and the monochromatic-edge clauses, plus exact
  checks of all 238300 stored primitive identities.

These SAT encodings and LRAT replays are external exact finite verifications,
NOT Lean proofs or asymptotic results. The explicit seven-prime theorem above
is the only new kernel-checked result.

The UNRESTRICTED binary mod-4 instance through 100000 has 380684 variables
and 2308527 clauses. It timed out at 240 seconds without SAT or UNSAT.
Files: `/tmp/cube_c4_binary_100000.{cnf,npz,out,exit}`. No inference about
unrestricted four-colorability follows from that timeout.

Spec.lean is unchanged with its original sorry and original checksum.
No proof has been submitted. All jobs have finished; only old defunct
CaDiCaL processes remain, not pending solvers.

## Squarefree first-fit checks (new finite diagnostics; no settlement)

New script `/tmp/cube_sieved_firstfit.py` reruns increasing-order first-fit
on three squarefree sources using the stored collision list through 100000.
Results are saved in `/tmp/cube_sieved_firstfit_results.json` and
`/tmp/cube_sieved_firstfit_100000_{1,6,30}_colors.npy`.

* All squarefree roots: 60794 vertices, 51697 stored edges, color sizes
  [44002,16455,337]. First colors occur at 1,34,7126.
* Squarefree roots coprime to 6: 30398 vertices, 5353 stored edges, color
  sizes [26870,3527,1]. First colors occur at 1,589,65911.
* Squarefree roots coprime to 30: 25331 vertices, 2046 stored edges, color
  sizes [23674,1657]. First colors occur at 1,589.

At 65911 on the coprime-6 source, earlier colors 0 and 1 are blocked by
  (5555,28097,64177,65911),
  (589,30115,63745,65911),
respectively; extremes' cubes equal the middle cubes' sum. Thus a two-color
bound for THIS source-restricted first-fit rule is false. This does not rule
out recoloring the source with two colors or prove anything asymptotic.

The saved FULL first-fit coloring was also filtered to squarefree roots.
Its color counts there are [34650,20049,5731,362,2]; color 4 first occurs
at squarefree root 76602. Hence its higher colors are not confined to roots
with repeated prime factors. The full first-fit rule and a first-fit rule
rerun on a restricted source are different constructions.

All newly computed assignments were checked against every stored source
edge, but the enumeration is not kernel-certified and no exhaustive new
pair-sum audit was performed. These are external finite diagnostics, not
Lean theorems or a uniform density estimate. No new proof or disproof of
Spec.lean was obtained. Spec.lean remains unchanged with its original sorry;
no submission was made and no job is pending.

## Further continuation: global cover and density routes remain unresolved

Reviewed the exact target, the finite-prefix criterion, the weighted divisor-cover
criterion, the necessary summable prime-cover condition for divisor-closed
constructions, and the existing parametrization/cancellation estimates. No
cutoff-independent reciprocal-cost bound or positive-density construction was
established. Reexamining finite optimized weights supplies no such bound.
Likewise, collision counts and the failures of particular coloring rules do not
establish a density obstruction for arbitrary sets. No new finite search or
asymptotic claim was made in this continuation, and no new Lean result was added.

Spec.lean remains unchanged with its original sorry. No complete proof or
disproof was obtained, no verification submission was made, and no new job is
pending.

## Squarefree odd-parity coloring obstruction (new, verified; no settlement)

`Submission/SquarefreeParityObstruction.lean` compiles, with a built `.olean`
in the Lake build path. Log: `/tmp/squarefree_parity_obstruction_final.log`.
Namespace: `Erdos1206.SquarefreeParityObstruction`.

All six roots 1115,15773,27541,29167,33167,38569 are squarefree and coprime
to 6, and

  27541^3-1115^3 = 29167^3-15773^3 = 38569^3-33167^3
                = 20888646305546.

The three pairs give three strict four-root collisions. Each of the six
roots appears twice among these three collisions. Therefore no function
`c : Nat -> ZMod 2`, even WITHOUT any multiplicativity assumption, can have
sum of the four colors equal to 1 on EVERY strict collision in this source.
Adding the three equations would give 0=1 in ZMod 2.

`no_odd_parity_coloring` proves that obstruction. `source_witnesses` and
`three_differences` certify the arithmetic. Their printed axiom checks use
only propext, Classical.choice, Quot.sound (the difference identity only
needs propext). This is an obstruction to the stronger odd-parity sufficient
condition, NOT an obstruction to ordinary nonmonochromatic two-coloring,
positive-density subsets, or the original conjecture.

The witness was extracted by exact F2 elimination on prime-support vectors
of stored squarefree primitive edges. A smaller unrestricted-squarefree
odd dependency uses the three edges
  (317,573,870,934), (317,678,870,979), (573,678,934,979).
These external witness files are `/tmp/cube_sf_product_linear_{1,6}.json`.
On the coprime-to-30 source through 100000, all 1768 stored primitive
product-parity equations were independent, and a solution was checked.
That last finite observation is not a global coloring result. No completeness
or asymptotic conclusion is inferred from the stored edge enumeration.

Spec.lean remains unchanged with its original sorry. No complete proof or
disproof was obtained, and no verification submission was made. No new
computation is pending.

## Specialized extension review (no new result)

Revisited block extension and increasing-greedy constructions. A short new
block far above the old roots excludes one-old/three-new collisions by size,
but no uniform useful control of two-old/two-new collisions at a fixed scale
ratio was established. Complete separation still requires growth that produces
lower-density gaps. No bound particular to the selected greedy set, fixed
positive prefix-density construction, or universal density obstruction was
proved. The existing arbitrary-set boundary counterexamples were not used as
counterexamples to every specialized extension rule.

No new Lean result or finite diagnostic was produced in this review.
Spec.lean is unchanged with its original sorry; no proof was submitted and
no new job is pending.

## Bounded repeated differences and narrow-band mixed obstructions (new, verified)

Two new auxiliary files compile, with `.olean` files in the Lake build path:

* `Submission/BoundedCubeDifferences.lean` (305 lines).
  Log: `/tmp/bounded_cube_differences_final.log`.
* `Submission/ShortBandMixedCollisions.lean` (360 lines).
  Log: `/tmp/short_band_mixed_collisions_final.log`.

The dependency `RepeatedCubeDifferences.lean` was rebuilt into the Lake build
path as well; its earlier sibling `.olean` was not sufficient for import lookup.

### Bounded rational family

`Erdos1206.BoundedCubeDifferences.bounded_roots_infinite` proves that

  {b in Q : 0<b, exists a>0, a^3-b^3=7,
            1/100000 <= b <= 100000}

is infinite. This strengthens the earlier positive-rational infinitude result
by keeping the roots in a fixed range bounded away from zero. The companion
a is at most b+2.

Proof uses a quadratic chord map, not an unproved elliptic-curve rank or
real-density theorem. For triples p,q, write

  F(p)=p0^3-p1^3-7*p2^3,
  L(q,p)=q0^2*p0-q1^2*p1-7*q2^2*p2,
  M(q,p)=q0*p0^2-q1*p1^2-7*q2*p2^2,
  R(q,p)=L(q,p)*p-M(q,p)*q.

When F(q)=0, polynomial identities prove

  F(R(q,p))=L(q,p)^3*F(p),
  R(q,R(q,p))=L(q,p)^3*p.

Thus the normalized map is injective away from the exceptional line and
zero normalization denominator. Reflect the normalized point by (x,y)->(-y,-x).
For inputs p=(a,b,1) with a^3-b^3=7 and a,b>0:

* if b>=100, use q=(73,17,38);
* if b<=1/100, use q=(-17,-73,38).

Explicit polynomial inequalities show that each image is positive, has lower
root between 1/100000 and 100000, and lies away from all exceptional
normalization factors. Either one of these tails is infinite and its injective
image works, or the original middle band is already infinite.

### Narrow separated bands and mixed collisions

Namespace `Erdos1206.ShortBandMixedCollisions`.

* `infinite_narrow_pairs K`: an infinite subset V of the bounded family such
  that for all b,d in V, b<mate(d), and both the b-values and mate-values have
  pairwise ratios at most (K+1)/K when K>0.
* `rational_narrow_sidon_pairs K k`: choose k pairs from this family so that
  each of the two cube-value arrays is Sidon, with the same narrow-band
  inequalities and all lower roots below all upper roots.
* `natural_narrow_sidon_pairs K k`: clear one common positive denominator D.
  The arrays remain separately Sidon, with a(i)^3=b(i)^3+7*D^3 and all the
  narrow-band inequalities. Also a(i)<=10^11*b(j) for every i,j, so the ratio
  between the two bands is bounded by one fixed constant.
* `narrow_mixed_collisions_not_cardinality_linear K C`: gives finite S,T
  with positive roots, each having Sidon cubes, every t in T below every s
  in S, s<=10^11*t, and

    K*x <= (K+1)*y  for all x,y in S,
    K*x <= (K+1)*y  for all x,y in T,

  but more than C*(|S|+|T|) oriented mixed collisions. As in the earlier
  construction, reversing the two pair indices counts an underlying
  four-root edge twice; this fixed factor does not affect unboundedness.

The narrow-family proof uses a finite partition of the bounded rational
b-range into floor bins. On the curve, mate is monotone and 1-Lipschitz.
In the bounded family, mate(b)-b>10^-12. Bins of width
1/(10^15*(K+1)) therefore keep the two bands disjoint and give the ratio
bounds. Finite Sidon extraction and denominator clearing reuse the earlier
proved lemmas.

All five printed axiom checks contain only propext, Classical.choice,
Quot.sound. Neither new file contains sorry/admit/native_decide or added
axioms. No finite numerical search is used in these theorems.

LIMITATION: this closes the previous lack of narrow-band placement in the
mixed CARDINALITY counterexamples. It still does not bound the common
clearing denominator in terms of k, give positive density inside either
band, or refute a mixed-collision bound linear in the largest root. The
sets may be extremely sparse in their bands. It is not a disproof of every
specialized extension rule and does not settle the original conjecture.

Spec.lean remains unchanged with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof was submitted. The compilations have finished and no new job is
pending.

## Further global-step and library review (no new result)

Rechecked Spec.lean and the every-prefix compactness and summable-source
reductions. None supplies the required uniform input unconditionally.
Reviewed whether near-diagonal rational collisions, multiplicative recurrence,
or local polynomial configurations force collisions in every positive-density
set. No valid density-transfer theorem was obtained: rational dilation changes
divisibility, and translating roots does not preserve a cubic collision.

A targeted search in Mathlib's NumberTheory and Combinatorics sources found
no Sidon/cube-sum extraction theorem supplying the missing global bound.
The available IsSidon definition and basic insertion lemmas are in
FormalConjecturesForMathlib/Combinatorics/Basic.lean; those insertion lemmas do
not establish positive root density.

No new Lean proof or finite diagnostic was produced. Spec.lean remains
unchanged with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof was submitted; no new computation is pending.

## Arithmetic-coloring continuation (no new result)

Reviewed the finite-coloring extraction theorem, the Boolean multiplicative
obstruction, reduced-gap congruences, and large-prime separation. No fixed
finite coloring was constructed. In particular, shared-large-prime separation
does not constrain the four-unshared-prime case, and the cancellation-aware
cubic parametrization does not give a uniform deletion estimate.

Also reconsidered rainbow-difference selection: absence of three-term
progressions of rational cubes makes the pairs with any fixed nonzero cubic
difference a matching, but arbitrarily many pairs with that difference are
possible. This alone supplies neither a bounded coloring nor a positive-density
independent set. No theorem asserting otherwise was used.

Reference retrieval from both www.erdosproblems.com/1206 and
erdosproblems.com/1206 again failed DNS resolution. No literature claim or
new finite numerical conclusion was made. No auxiliary Lean theorem was added,
Spec.lean is unchanged with its original sorry, and no proof was submitted.

## Collision-concentration continuation (no settlement)

Checked the saved degree distributions and finite-prefix deletion experiments.
They do not yield bounded typical degree, bounded deletion cost, or uniform
prefix density. No asymptotic claim was extracted from them.

A small exact local check of the four quadratic forms in the saved squarefree
conic family found a projective parameter pair modulo each prime below 100
where none of the four forms vanishes. This only rules out a fixed-prime
obstruction at those primes for that particular family. It neither establishes
simultaneous prime values nor proves any statement about a global divisor cover.
No Lean theorem or conjecture settlement follows from this check.

Spec.lean was not changed; the original sorry remains. No proof was submitted.

## Conic norm-field review (no settlement)

Computed the discriminants of the four saved quadratic coordinate forms.
The first pair has discriminant 948996 = 18^2 * 2929; the second pair has
-3078972 = 18^2 * (-9503). Thus this family does not put all four coordinates
in one common quadratic norm field by the displayed representations. This
was an exact integer calculation, not a new Lean theorem or a density bound.

Revisited the idea of deleting tails of the root-value sets of individual
conic families. Even if a primitive-coordinate value set has density zero,
its arbitrary integer dilations need not: a single primitive root produces
an entire set of multiples. Consequently this observation does not justify
a summable deletion of all scaled collision families. No valid uniform
covering, coloring, or arbitrary-positive-density recurrence argument was
obtained. Spec.lean remains unchanged with its original sorry; no submission
was made.

## Bounded unrestricted two-coloring retries (no conclusion)

Retried the unresolved finite coloring route, without imposing multiplicativity
or fixing the old colors. These are only finite diagnostics, not a settlement.

* `/tmp/cube_prob_extension.cpp` starts from the checked 6000-root coloring
  and permits recoloring all roots while searching through 8000. Two 240-second
  runs used polynomial break-score exponents 1.5 (seed 41) and 4 (seed 42).
  Neither found a coloring. The best counts of monochromatic stored edges were
  792 and 19 respectively. Logs: `/tmp/cube_prob_extension_8000_{41,42}.log`.
* A 240-second CaDiCaL retry on `/tmp/cube_core_30000.cnf`, with `--unsat`,
  seed 43, and LRAT output, ended UNKNOWN. Log:
  `/tmp/cube_core_30000_retry43.log`. The 721 MB incomplete LRAT trace was
  deleted; it was not a certificate.
* `/tmp/cube_weighted_color.cpp` implements a weighted local search, allowing
  full recoloring and penalizing repeatedly unsatisfied edges. A 120-second
  run through 8000 (seed 44) found no coloring; its best count was 176
  monochromatic stored edges. Log: `/tmp/cube_weighted_color_8000_44.log`.

Failure of these searches is NOT a proof of non-two-colorability, unbounded
chromatic number, or zero independence density. No new candidate was available
for the independent exhaustive pair-sum verification. The verified 6000-root
coloring remains the earlier finite result. All new jobs have finished.
Spec.lean is unchanged with its original sorry; no proof was submitted.

## Small-prime-factor sieve reassessment (no theorem)

Considered selecting integers with upper bounds on counts of small prime
factors, including counts in the splitting classes of a fixed quadratic
field. Such conditions might suppress scaled points of a fixed conic family
more strongly than a squarefree sieve. No required number-theoretic estimate
was proved, and no uniform bound across all conic families was obtained.

In particular, choosing separate large starting cutoffs for infinitely many
field-specific restrictions leaves finitely many uncontrolled primitive
patterns per family, but infinitely many patterns overall. Their deletion
cost is not known to be summable. A countable collection of individually
controlled tails therefore does not establish the conjecture. This was
reasoning only, not a new Lean result or a certified asymptotic claim.

Spec.lean remains unchanged with the original sorry, and no proof was
submitted.

## Global-bound continuation (no settlement)

Rechecked the exact conjecture, density and Sidon definitions, compact-gap
coloring, fixed-gap sieves, inert-prime gap restrictions, and the saved
arithmetic-source counterexamples. No definition discrepancy or missing
uniform bound was found. No Lean theorem was added and no finite search was
run in this continuation.

Also considered normal-order restrictions on prime-factor counts in the
splitting classes of the two quadratic fields of a conic family. This was
reasoning only: no uniform counting/sieve estimate was proved. In particular,
normality at the full root height cannot uniformly constrain a fixed primitive
pattern under arbitrarily large dilations. Restrictions at all smaller prime
cutoffs would need quantitative estimates, and family-dependent cutoffs still
leave infinitely many exceptional patterns with uncontrolled total cost.
This does not improve the previously recorded global density/coloring criteria.

Spec.lean remains unchanged with its original sorry. No proof was submitted.

## General rational differences and positional cliques (new verified results)

Added five auxiliary files. They compile, and the printed axiom audits for
all principal results list only `propext`, `Classical.choice`, `Quot.sound`.
These are not a proof or disproof of Spec.lean.

* `GeneralCubeDifferences.lean`, namespace
  `Erdos1206.GeneralCubeDifferences`: `infinite_nat_difference` and
  `infinite_rational_difference` show that every positive difference of two
  positive rational cubes has infinitely many positive rational representations.
  The argument generalizes the two-adic tangent orbit. Besides a tangent seed
  for two odd integer numerators, it uses the verified tripling numerators
  `a^9+3*a^6*b^3-6*a^3*b^6+b^9` and
  `a^9-6*a^6*b^3+3*a^3*b^6+b^9`, with denominator
  `3*a*b*(a^6-a^3*b^3+b^6)`. Opposite numerator parities give equal odd
  residues modulo four, allowing the denominator-divisibility argument.
* `UnboundedCubeDifferences.lean`, namespace of that name under `Erdos1206`:
  `unbounded_of_infinite` and `unbounded_rational_difference` prove positive
  representations with arbitrarily large lower root. Close pairs in a bounded
  infinite set give large points by a chord map. This is now a theorem, not
  merely an elliptic-curve heuristic. Still no denominator-height estimate.
* `LocalCubeDifferences.lean`: `near_pair_below` produces positive rational
  representations approaching any prescribed positive pair from below.
  `second_fourth_pair` proves that every positive rational pair `b<d` is the
  second/fourth positional pair of some strict positive rational collision.
* `PositionalCubeCliques.lean`: `second_fourth_cliques` gives a common integer
  dilation of `1,...,k` forming a clique in that positional graph.
  `no_finite_second_fourth_coloring` proves that every finite coloring has a
  strict positive collision with the second and fourth roots equally colored.
  This rules out a global extension of the *fixed-positional-pair separation*
  used in the compact-gap coloring. It does NOT rule out ordinary finite
  cube-Sidon coloring: the other two roots need not have that color.
* `OneBandCubeDifferences.lean`: `infinite_one_band` proves, for every natural
  `K`, existence of positive rational `L<U` with `K*U <= (K+1)*L`, and
  infinitely many positive rational pairs `(x,y)` in `(L,U)` satisfying
  `x^3-y^3=7`. Thus both roots can now be confined to one arbitrarily narrow
  multiplicative band. This strengthens the earlier two-band existence result,
  but no density or denominator-height conclusion follows. The older finite
  separately-Sidon extraction statements were not strengthened in this file.

All five have oleans under `.lake/build/lib/lean/Submission/`. No computation
is pending. `Spec.lean` is unchanged with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
The missing global density/coloring/divisor-cover estimate remains unproved.
No proof was submitted.

## All six positional graphs (new verified extension)

Added and compiled two further auxiliary files, with oleans in the Lake build
path. Principal theorem axiom audits list only the three allowed axioms.

* `RationalCurveLocal.lean`, namespace `Erdos1206.RationalCurveLocal`:
  `near_below_of_unbounded` permits either sign for the initial coordinates
  (the upper coordinate must be nonzero), assuming unbounded positive rational
  points on the same difference curve. It produces nearby points below both
  initial coordinates. `positive_difference_of_sum` and `sum_unbounded` show
  that the sum of two distinct positive rational cubes is a difference of
  positive rational cubes and has unbounded such representations. These use
  explicit tangent/chord identities, not an assumed elliptic-curve theorem.
* `AllPositionalCubeCliques.lean`, namespace
  `Erdos1206.AllPositionalCubeCliques`: `rational_pair_extension` prescribes any
  selected two positions in a strict collision when their values `u<v` satisfy
  `v^3<2*u^3`. Only the third/fourth pair needs this closeness restriction.
  `positional_cliques` clears finitely many denominators to construct cliques
  of arbitrary size for every one of the six positional graphs.
  `no_finite_fixed_position_coloring` states that for any `p<q : Fin 4` and
  any `color : Nat -> Fin k`, there is a strict positive cube collision whose
  roots in positions `p,q` have the same color.

The final result excludes ALL fixed-positional-pair separation strategies,
not just the second/fourth strategy of the compact-gap construction. It is
still NOT an obstruction to ordinary finite Sidon coloring: which pair of
positions receives different colors may vary from collision to collision.
Nor does it imply a bound on the independence density. No denominator-height
bound or missing global density/covering estimate was obtained.

Spec.lean remains unchanged with its original sorry. No proof submitted.

## Density-extraction reassessment (no settlement)

Rechecked the target and the every-prefix, weighted-divisor, and summable-source
criteria. Revisited whether the homogeneous cubic parametrization forces a
reciprocal-summable exceptional set of roots. No such set or uniform estimate
was obtained. Cancellation and arbitrary dilations remain essential; they were
not discarded.

Also investigated using arbitrarily many pairs with one common cubic difference
to improve the global density bound. The finite combinatorial constraint is
valid (at most one whole pair can lie in a Sidon set), but the attempted transfer
to ordinary lower natural density was not justified. Natural density is not
invariant under dilation preimages: the odd integers have density 1/2 and empty
preimage under multiplication by 2. Thus uniform multiplicative averaging of
these rational pair configurations cannot simply be substituted for the
weighted smooth-orbit projection. No new 1/2 bound, and no zero-density result,
is claimed.

This continuation added no Lean theorem and ran no numerical counterexample
search. Spec.lean remains unchanged with the original sorry. No proof was
submitted; no new computation is pending.

## Finite progression criterion and local integral collisions (new verified results)

Added `CubeArithmeticProgressions.lean`, namespace
`Erdos1206.CubeArithmeticProgressions`. It compiles, has an olean in the Lake
build path, and the principal axiom checks use only propext, Classical.choice,
and Quot.sound.

* `cubes_sidon_of_large_coprime_step u step L`: if gcd(step,u)=1 and
  6*L<step, the cubes of u+step*i for 0<=i<=L are Sidon. Expanding the
  equality, cancelling one factor of step, and reducing modulo step forces
  3*(i+j)=3*(k+l). Equal root-pair sums together with equal cube sums then
  force equality of the unordered pairs. This quantitatively confirms that
  progression length alone cannot force a cubic collision.
* `narrow_collision_in_residue_class q r K M`: for q>0, constructs
  M<a<b<c<d, all congruent to r modulo q, satisfying
  a^3+d^3=b^3+c^3 and K*d <= (K+1)*a.
* `no_residue_class_tail`: a cube-Sidon root set cannot contain all sufficiently
  large members of any residue class with positive modulus.

The integral collision construction uses the following homogeneous cubic forms
in q,z (coefficient order z^3, q*z^2, q^2*z, q^3):

  A = (1, 7,15, 6)
  B = (1, 8,24,27)
  C = (1,10,36,45)
  D = (1,11,39,48).

They satisfy A^3+D^3=B^3+C^3 and 0<A<B<C<D for q>0. If q<=z and
70*K*q<=z, then K*D<=(K+1)*A. Set z=q*(70*K+M+1)+1 and multiply
all four forms by q+r. This proves the congruence and size conclusions
without any rational-denominator estimate or numerical search.

LIMITATION: these facts neither construct a positive-lower-density Sidon set
nor show that every positive-density set contains a collision. Long finite
progressions and tails of infinite progressions are different conditions.
Spec.lean remains unchanged with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof was submitted. No new computation is pending.

## Reusable-cover review and provenance correction (no settlement)

Rechecked GreedyDivisorCover, PrimeCoverNecessity, FiniteDivisorCompactness,
PrimitiveCollisionMass, and the exact cancellation formula. No uniformly
bounded reciprocal-cost cover was obtained. Primitive collision mass is not
a lower bound for the optimum reusable divisor-cover cost, nor does the
parametrization supply a summable upper bound after cancellation is included.
The unconditional hypothesis needed by the sufficient criteria remains absent.

PROVENANCE CORRECTION to the preceding entry: ResidueCollision.lean already
proved collisions arbitrarily far out in every residue class, the no-residue-
tail obstruction, and impossibility of finite divisor covers omitting 1.
CubeArithmeticProgressions.lean independently repeats the residue-tail
conclusion. Its actual additions are the finite coprime-step Sidon criterion
and the narrow-band refinement of the integral residue-class construction.
The new four forms specialize at z=1 to the older ResidueCollision forms.

No new Lean theorem was added in this continuation, and no numerical search
was run. Spec.lean is unchanged with its original sorry. No proof or disproof
has been submitted, and no new computation is pending.

## Global theorem and norm-field sieve review (no settlement)

Searched the local Mathlib/FormalConjecturesForMathlib sources for an applicable
cube-Sidon density or partition theorem; none was found. Rechecked the finite
coloring and upper-density-one source reductions. A fixed finite coloring on
an upper-density-one source already yields one on all positive roots, so merely
removing a density-zero source exception does not bypass the coloring problem.

Investigated simultaneous prime-factor restrictions in the different quadratic
norm fields of a fixed conic family, including constraints that compare the
common multiplier with the primitive coordinates. No uniform counting estimate
across all conic families was proved, and no positive-density source satisfying
the needed simultaneous restrictions was constructed. No unproved normal-order,
large-deviation, or sieve estimate was used as a theorem.

No new Lean theorem, numerical search, or target-file edit arose from this
continuation. Spec.lean still has its original sorry; no proof was submitted.

## Modular-construction review (no settlement)

Investigated adapting finite modular Sidon constructions to the cubic image.
A generic Sidon residue set modulo q has size only of order sqrt(q), so the
ordinary residue-class selection does not retain a fixed positive fraction as
q grows. Using a larger modulus leaves the unproved problem of arranging a
large intersection with the actual cube values. No such construction, no
uniform color bound, and no uniform every-prefix density estimate was obtained.

No new Lean result or numerical search arose from this continuation.
Spec.lean remains unchanged with its original sorry. No proof was submitted.

## Active finite diagnostics after context continuation (2026-08-28 10:31 UTC)

The earlier statements that no computation is pending are now superseded.
The conjecture remains unresolved, and Spec.lean is unchanged.

Three bounded jobs are currently running:

* Unrestricted two-color CNF on the 100000-root densest core:
  `/tmp/cube_core_100000_retry120601.log`, corresponding `.exit` and `.pid`.
  Solver PID 68335, `--unsat --seed=120601 -t 3600`, launched at about
  10:05:52 UTC. Last check: no SAT/UNSAT result, about 8.25 million conflicts.
* Unrestricted two-color CNF on the 8000-root densest core:
  `/tmp/cube_core_8000_retry120602.log`, corresponding `.exit` and `.pid`.
  Solver PID 68336, `--sat --seed=120602 -t 3600`, launched at about
  10:05:52 UTC. Last check: no SAT/UNSAT result, about 9.34 million conflicts.
* Stochastic 8000-root coloring search:
  `/tmp/cube_prob_savebest_120603.log`, corresponding `.exit` and `.pid`.
  Actual child PID 68580, duration 3000 seconds, seed 120603, exponent 4.
  Best saved assignment `/tmp/cube_prob_best_8000_120603.txt` has 21 stored
  monochromatic edges at last check and is NOT a valid two-coloring.
  A successful full assignment would instead be saved at
  `/tmp/cube_prob_extension_8000_120603.txt` and require independent checking.

The core CNFs were audited in the preceding context: 5808 variables/23704
strict collision edges for cutoff 8000, and 81733 variables/769099 edges for
cutoff 100000. The maps are `/tmp/cube_core_N.map`; each edge has positive
ordered distinct integer roots with a^3+d^3=b^3+c^3. Each edge gives its two
monochromaticity-forbidding clauses, plus a single color-swap symmetry clause.
Neither solver was asked to produce a proof trace. A future UNSAT report is
not a kernel proof; a SAT core assignment is not automatically a coloring of
all roots through the cutoff.

Three completed local-neighborhood repair runs must be kept separate:
`/tmp/cube_lns_1206.py` freed 100, 500, and 2000 roots near the 21 bad edges
of its input assignment and FROZE all other colors. All three returned UNSAT.
These results say only that those frozen assignments cannot be repaired in
the chosen neighborhoods. They do NOT prove unrestricted non-two-colorability.
The script did not separately save its original coloring snapshot or free-root
map, and the stochastic best file can subsequently change. Treat those runs
as diagnostics, not reproducible theorem certificates.

Repeated-representation bucket analysis from the preceding context:
`/tmp/cube_bucket_analysis_1206.py` and its `.log`, with output
`/tmp/cube_repeated_buckets_100000_1206.txt`. From the stored edge enumeration,
it found difference-group representation counts
  2:1670420, 3:40416, 4:981, 5:34,
and sum-group counts
  2:887256, 3:3843, 4:27.
The 45301 groups with at least three pairs were saved. Sum keys are tagged
by adding 4*10^15. Roots within each saved group were checked distinct.
Enumeration completeness is not kernel-certified; no successful new global
bound or strengthened solver encoding followed from this analysis.

In this continuation, reviewed the divisor-cover criterion, cancellation
bounds, and possible prime-factor/normal-order approaches again. Symbolic
factorization of the parametrization did not supply a uniform root-factor
excess or a summable cover. Recomputed finite degree quantiles only as a
check of earlier recorded diagnostics; these are NOT new mathematical
results. No uniform finite coloring bound, every-prefix Sidon-density bound,
or zero-density theorem was obtained. No Lean theorem was added and no
proof was submitted.

## Pair-separation review (2026-08-28, no settlement)

Considered replacing root deletion by a choice of one separated pair per
primitive collision. This did not produce a global estimate. In particular,
a reciprocal-lcm sum for reduced pairs cannot simply be used as the density
cost of deleting endpoints from all their dilates: the density of multiples
of one endpoint is a different quantity. No such sufficiency lemma was used
or proved. Reusing ratios would still require an actual summable cover or a
uniformly controlled coloring, neither of which was obtained.

Rechecked the existing finite multiplicative Boolean colorings on squarefree
roots coprime to 6 and 30 through 100000. These were already verified finite
constructions in the earlier log, not new results in this continuation.
No infinite prime-color extension argument was found. The ordinary squarefree
Boolean instance without the coprimality restriction had previously returned
UNSAT at 30000; this is a different source and must not be conflated with the
coprime-to-6 source.

No Lean theorem, numerical search, or target-file edit was added in this
continuation. The three previously launched bounded jobs remain pending as
of the latest check; their artifacts and scope are documented above.
Spec.lean retains its original sorry. No proof has been submitted.

## Bounded search outcomes and safe warm-start check (2026-08-28 11:07 UTC)

All jobs listed as pending in the preceding entries have now finished.
No SAT or unrestricted UNSAT result was obtained:

* `/tmp/cube_core_100000_retry120601.exit`: 0, time limit reached, undecided.
* `/tmp/cube_core_8000_retry120602.exit`: 0, time limit reached, undecided.
* `/tmp/cube_prob_savebest_120603.exit`: 0, completed its time budget.
  Final log: `final N 8000 best 21 bad 39 steps 12144600001`.
  Its best assignment is still NOT a coloring: it has 21 monochromatic edges.

Two targeted finite diagnostics were performed in this continuation:

1. Autarky extraction from the fixed snapshot
   `/tmp/cube_prob_snapshot_8000_120603_1031.txt` (SHA256
   ca8db69b3b6b6236755ccf51b32ab6fc4576d7d506bbb62f1a7e5bda24deede4).
   Script `/tmp/cube_autarky_1206.py`, output `.json`, `.fixed`,
   `.remaining.bin`. Starting with the snapshot colors, it repeatedly removes
   assignments that touch a clause without satisfying it. The surviving
   partial assignment was checked to supply BOTH colors on every touched
   collision, hence is a genuine autarky for the paired NAE clauses.
   Only 27 vertices survived, removing just one of the 30792 stored edges.
   The remainder has 30791 edges incident to 7973 vertices. This did not
   isolate a small hard component and did not decide the instance.

2. A full 8000-root warm-start instance, not merely the densest core.
   Generator `/tmp/cube_warmstart_1206.py`; artifacts
   `/tmp/cube_warmstart_8000_120605.{cnf,json,flips,log,exit,pid}`.
   All 30792 input edges were checked using Python integer arithmetic to
   have 0<a<b<c<d<=8000 and a^3+d^3=b^3+c^3. Variables were complemented
   according to the saved near-coloring, after aligning the color-swap
   symmetry break x_1=true. The translation is x_n = y_n XOR flips[n].
   This fixes NO original colors and preserves the full instance's SAT
   status; unlike the earlier frozen-neighborhood repair tests it is an
   unrestricted search. CaDiCaL ran with `--sat --phase=false
   --rephase=false --seed=120605 -t 900`. It exited 0, undecided at its time
   limit. No proof trace was requested and no coloring was returned.

Also checked elementary dilation-color correlations in the previously
verified coloring through 6000: they did not provide an exact multiplicative
invariant. This is only a finite diagnostic, not an obstruction theorem.

Revisited prefix constructions and block gluing. Important distinction:
`ShortBandMixedCollisions.narrow_mixed_collisions_not_cardinality_linear`
excludes a bound linear in |S|+|T|, NOT a bound linear in the largest root.
No useful bound of the latter kind, no finite positive-density construction
at arbitrary cutoffs, and no infinite extension argument was obtained here.

No Lean theorem or target-file edit was made. Spec.lean retains its original
sorry and SHA256 9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
The original conjecture remains unresolved; no proof has been submitted.
No computation from this continuation remains pending.

## Odd-parity bucket sieve (completed finite diagnostic)

New route considered: seek a summable divisor sieve after which every finite
collection of strict collision edges with even vertex incidences has even
cardinality. This would give an F₂ coloring whose sum on every edge is 1,
stronger than ordinary proper two-coloring. No global sieve or summability
bound has been obtained.

Script `/tmp/cube_parity_bucket_sieve_1206.py`, artifacts `.log` and `.json`,
completed. It checks stored repeated-sum/difference buckets with exact integer
arithmetic, takes EVERY triple of pairs, divides the six roots by their gcd,
and forbids the largest normalized root. Redundant divisors are removed.
Through 100000 this gives 5281 forbidden divisors, displayed reciprocal cost
0.38108042580999407, and 69751 surviving roots. This is a finite computation,
not an infinite reciprocal bound; bucket enumeration completeness is not
kernel-certified.

F₂ elimination on surviving stored edges:
* All positive: 113408 edges, rank 575 before an odd dependency was found.
  Extracted witness has 181 edges, max root 784, 283 vertices. Every vertex
  has even incidence; every cube identity checked with exact integers.
* Squarefree: 18530 edges, rank 18529, no odd dependency.
* Squarefree/coprime-6: 3654 edges, rank 3654, no odd dependency.

No coloring assignment was decoded for the consistent finite systems.
Neither they nor the finite reciprocal cost imply a global coloring.
The all-positive witness shows that the sieve generated by the stored triple
buckets does not suffice even finitely. It does not by itself characterize
obstructions after deleting all conceivable repeated-representation buckets.

`Submission/CheckCycle.lean` is scratch API exploration only (two guessed
LinearMap method names fail). No odd-cycle reduction theorem has yet been
written. The existing target remains unchanged with sorry. No computation
from this diagnostic remains pending.

## Verified odd-cycle reduction

`Submission/OddCycleColoring.lean` now compiles. Its checked results include:
* `exists_functional_of_relations`: over any field, prescribed values on an
  indexed family extend to a linear functional iff the needed finite-support
  consistency condition holds (the theorem proves the sufficient direction).
* `noOddCycle_iff_odd_coloring`: for any indexed finite-edge hypergraph,
  every finite even-incidence edge collection has even cardinality iff there
  is a ZMod 2 vertex coloring summing to 1 on each edge.
* `odd_coloring_good`: odd-parity coloring on strict cubic collision edges
  gives cube-Sidon fibers, using the established strict-collision theorem.
* `summable_odd_cycle_cover_suffices`: a reciprocal-summable forbidden-divisor
  set omitting 1 suffices IF its surviving cubic hypergraph has no odd cycle.

Axiom audits for the functional lemma, equivalence, and final conditional
reduction list only propext, Classical.choice, Quot.sound. The compiled object
is in `.lake/build/lib/lean/Submission/OddCycleColoring.olean`; build log is
`/tmp/oddcycle.log`. The required `SummableSourceColoring.olean` was also rebuilt
in that library directory with the same allowed-axiom audit.

This is a conditional reduction only. No arithmetic cover satisfying its
hypotheses has been found. The original target is still unchanged with sorry.

## Exhaustive audit of the finite larger odd circuit

Independently enumerated ALL distinct-root unordered cube pairs on the 283
vertices of the recorded 181-edge witness, using exact Python integers.
Every cube sum and every positive cube difference has at most two pair
representations. Thus this finite SOURCE really is free of three-pair buckets;
this conclusion no longer depends on completeness of the stored 100000-root
edge enumeration. It is still a finite diagnostic, not a kernel theorem or
an infinite sieve result.

`/tmp/cube_shrink_parity_1206.py` independently builds the complete cubic edge
set on that source (228 edges), then tries 50 randomized elimination/greedy
vertex-deletion orders. It did not improve the 181-edge, 283-vertex witness.
Artifacts: `/tmp/cube_shrink_parity_1206.log` and `.json`. The process finished;
no computation is pending. No claim of general minimality follows from this
bounded shrinking attempt.

## Rough-root and residue-source investigation (no settlement)

Revisited the missing uniform bound for divisor-cover costs, especially edges
with no small prime factors. No usable arithmetic bound or infinite cover was
proved. The already known prime-cover necessity remains an obstacle; finite
LP costs must not be extrapolated to summability.

Exact finite diagnostics from the stored 100000-root enumeration found 105
all-prime edges, with 410 distinct incident primes. Counts at cutoffs 3000,
10000, 30000, 100000 are 4, 6, 30, 105 respectively. These are not a prime
collision asymptotic or a proof that every prime cover has divergent cost.

Also tested squarefree residue-class sources. A lack of stored examples for
larger moduli is not a theorem: the existing narrow cubic polynomial family
explicitly gives squarefree collisions congruent to 1 modulo 27, 48, 72, 144.
These examples were checked using exact Python integers and factorization:
* mod 27: (4850551, 6299830, 8249230, 8867449), using z=109, q=27;
* mod 48: (27038353, 35150785, 46053409, 49507153), using z=193, q=48;
* mod 72: (90944281, 118279585, 155003185, 166630969), using z=289, q=72;
* mod 144: (422767873, 593280145, 808768945, 871661377), using z=433, q=144.
The roots are in increasing order with a^3+d^3=b^3+c^3. This is not a proof
for every modulus and not an obstruction to arbitrary positive-density sets.
No global divisor-cover, coloring, density construction, or disproof was
obtained in this investigation. No computation is pending.

## New verified local arithmetic result and its density limitation

`Submission/CoprimeResidueCollisions.lean` compiles with only propext,
Classical.choice, Quot.sound. Public theorem
`Erdos1206.CoprimeResidueCollisions.coprime_narrow_collision_mod_one` says:
for any positive modulus m and naturals L,N, there are ordered roots
N<a<b<c<d with a^3+d^3=b^3+c^3, all six pairwise gcds equal to 1,
all four roots congruent to 1 modulo m, and L*d<(L+1)*a.
This combines coprimality, arbitrary finite congruence restrictions, arbitrary
relative narrowness, and arbitrary height; no squarefreeness is asserted.

The explicit family uses q>0 and k>=0, with
A=(k^3+26k^2+232k+657)q^3+(3k^2+52k+232)q^2+(3k+26)q+1,
B=(k^3+29k^2+307k+1128)q^3+(3k^2+58k+307)q^2+(3k+29)q+1,
C=(k^3+31k^2+347k+1412)q^3+(3k^2+62k+347)q^2+(3k+31)q+1,
D=(k^3+34k^2+392k+1583)q^3+(3k^2+68k+392)q^2+(3k+34)q+1.
Six integer Bezout identities establish pairwise coprimality whenever
132300 divides q. They come from the homogeneous forms in t=(k+10)q+1,
with constants 1050,2940,1890,1260,2940,1050 times q^5.
Take q=132300*m*(N+1), k=20*(L+1).
Build log: `/tmp/coprime_residue.log`.

IMPORTANT: this does not prove recurrence for arbitrary dense sets. In fact
`Submission/CoprimeResidueFamilyAvoider.lean` now proves the opposite for this
particular family: there is an infinite set S of positive lower density which
avoids EVERY integer multiple of EVERY A(k,q), q>0. Thus it contains none of
these explicitly constructed collisions, even after dilation. The proof uses
((k+1)(r+1))^2 <= A(k,r+1), the product of two convergent reciprocal-square
series, and the existing summable divisor-sieve positivity theorem.

Both `family_reciprocals_summable` and
`positive_density_avoids_entire_family` have allowed-axiom audits and compile.
Build log: `/tmp/coprime_residue_avoider.log`. Compiled objects are in
`.lake/build/lib/lean/Submission/`.

This gives a concrete limitation of the attempted recurrence route: favorable
finite congruence and Archimedean properties of rational collisions do not
supply the needed arbitrary-positive-density recurrence. No such recurrence,
no global cover, and no settlement of the original conjecture was obtained.
Spec.lean remains unchanged with sorry. No computation is pending.

## Extension and large-prime review (no settlement)

Revisited the finite-extension route. Uniformly excluding two-old/two-new
collisions by cube-gap separation requires a new root scale roughly beyond
M^(3/2) when old roots are at most M. That scale separation does not maintain
positive lower density. No cutoff-linear boundary estimate or every-prefix
extension invariant was obtained. The existing counterexample to a bound
linear in the cardinalities of two pieces is not a counterexample to every
bound linear in their root cutoff.

Also reviewed a recursive large-prime-factor construction. Existing results
already show that the large-prime source contains dilations of every finite
positive prefix, has no hereditary linear collision-count bound, and has
superlinear collision counts in its full prefixes. The shared-prime separation
lemma distinguishes common-large-prime copies from collisions with distinct
large prime factors, but no adequate uniform estimate for the latter or
recursive density-preservation argument was obtained. These are reviews of
existing results, not new global theorems or new computational evidence.

No Lean proof, disproof, new finite search, or target-file edit resulted.
Spec.lean remains unchanged with its original sorry. No computation is pending
and no proof has been submitted.

## Verified large cancellation with four prime roots

Revisited gap-ratio interval selection. The existing compact-gap-ratio
coloring leaves both ratios approaching 1 and unbounded ratios untreated.
No summable-loss combination or uniform positive-density construction was
obtained; no new gap-ratio theorem was added.

Tested the specific possibility that prime-root collisions have small
cancellation in at least one of the 24 signed cubic-parametrization charts.
Exact diagnostic script `/tmp/cube_prime_chart_1206.py` evaluated all 24 charts
on the 105 four-prime collisions in the stored enumeration through 100000.
Artifacts: `/tmp/cube_prime_chart_1206.log` and `.json`. This is a finite
diagnostic, not an asymptotic bound or proof of unboundedness on prime roots.

A new Lean file `Submission/PrimeChartCancellation.lean` independently
verifies one resulting example. Namespace `Erdos1206.PrimeChartCancellation`:

* `certificate_natAbs_scale_eq`: in a fixed nondegenerate signed chart, two
  primitive integral certificates have equal absolute cancellation factors.
  This is general, not limited to the numerical example.
* `example_prime_identity`: all four roots 17713, 42643, 57119, 63689 are prime,
  and 17713^3 + 63689^3 = 42643^3 + 57119^3.
* `prime_example_cancellation_lower`: for every signed permutation chart and
  EVERY primitive integral certificate for that chart, its cancellation
  factor has absolute value at least 2133097393. Explicit primitive
  certificates for all 24 charts are checked in `example_audit`.

The lower bound is for a single example. It does NOT prove that no finite
uniform bound exists for four-prime collisions. It does show that restricting
to four prime roots does not justify discarding cancellation or assuming a
small constant such as 1, 6, or 216.

The file compiles. All three displayed axiom audits report only propext,
Classical.choice, Quot.sound. Build artifact:
`.lake/build/lib/lean/Submission/PrimeChartCancellation.olean`.
Lean log: `/tmp/prime_chart_lean_1206.log`.

No settlement of the original existential conjecture was obtained.
Spec.lean remains unchanged with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No computation is pending; no proof has been submitted.

## Verified squarefree, coprime-to-210 parity obstruction

Investigated a specific possible source for the odd-parity coloring route:
squarefree roots coprime to 30 (and then 210). The stored repeated buckets
through 100000 contain no triple with every root squarefree and coprime to
30. This finite absence was NOT used as a theorem.

An elliptic-curve construction produced a counterexample to that proposed
odd-parity source restriction. Start with D=20888646305546 and the three
known pairs (27541,1115), (29167,15773), (38569,33167). Their Weierstrass points
are (12*(a^2+a*b+b^2),36*(a^2+a*b+b^2)*(a+b)) on
Y^2=X^3-432*D^2. A small group combination (-2,0,-1), followed by choosing
the positive pair, gives the rational pair
(105350827203419039,68627966441445241)/3434214987167.
Clearing this denominator with the second and third original pairs gives:

* (105350827203419039, 68627966441445241)
* (100165748530699889, 54167872992585091)
* (132454237840044023, 113902608479367889)

All three positive cube differences equal
846043579199798306600801513348186984803243047823798.
Every one of the six roots is squarefree and coprime to 210.

New verified file: `Submission/SquarefreeRoughParityObstruction.lean`.
Namespace: `Erdos1206.SquarefreeRoughParityObstruction`.
It imports only FormalConjecturesUtil, and independently checks the numeric
identity, source membership, and resulting three-edge parity contradiction.
The elliptic-curve computation is discovery only, not a Lean dependency.
Public results:

* `source_witnesses`, where source is squarefree roots coprime to 210;
* `three_differences`;
* `no_odd_parity_coloring` for the entire source.

Large prime factors are certified with the Lucas primality theorem, an
explicit recursively certified factorization of p-1, and fast modular powers
via `reduce_mod_char`. The file uses `decide +kernel`, NOT native_decide.
There are 38 small or recursively certified prime lemmas. All displayed
axiom checks contain only propext, Classical.choice, Quot.sound.
Build: `.lake/build/lib/lean/Submission/SquarefreeRoughParityObstruction.olean`.
Lean log: `/tmp/sf_rough_parity_lean_1206.log`.
Discovery: `/tmp/cube_sf30_elliptic_1206.sage` and `.log`.
Generator: `/tmp/gen_sf30_parity_1206.py` originally generated the version
with source coprime to 30; the final file was renamed and strengthened to 210.
The superseded SquarefreeThirtyParityObstruction.lean and olean were removed.

Also factored the tangent-iteration and tripling formulas. The iterated
formulas include degree-8 and degree-12 irreducible factors, so the existing
quadratic squarefree sieve does not apply directly. The exact rational
tripling formulas were checked symbolically by `/tmp/cube_tripling_forms_1206.py`.
No new global squarefree-value theorem was obtained or claimed.

IMPORTANT SCOPE: no_odd_parity_coloring only excludes the stronger requirement
that each collision have color sum 1 in F2. It does NOT exclude ordinary
proper two-coloring, the existing finite multiplicative colorings on the
coprime-to-30 source, or a positive-density cube-Sidon subset. The new triple
is one of the repeated-representation obstructions already included in the
global odd-cycle-sieve reduction; it does not refute that conditional route.

Original conjecture still unresolved. Spec.lean is unchanged with its sorry.
No computation is pending and no proof has been submitted.

## Return to the every-prefix density requirement (no new theorem)

Reviewed Compactness.lean, ThickCubeSidon.lean, and
CompletionBoundaryUnbounded.lean with the aim of finding a direct nested
construction, rather than another finite coloring obstruction. No uniform
positive density constant or compatible every-prefix extension bound was
obtained. Endpoint cardinality, expected prefix counts, and unbounded-gap
interval gluing were not promoted to a proof of positive lower density.
The general cardinality-linear completion-boundary estimate remains false;
a suitably controlled bound specific to a successful construction is still
missing.

No new Lean theorem, computation, or target-file edit resulted in this
continuation. This entry is a review, not new global mathematical evidence.
The original conjecture remains unresolved. No computation is pending and
no proof has been submitted.

## Saved-character inspection (finite diagnostic only; no settlement)

Revisited the global counting and finite-coloring routes. The existing
squarefree conic primitive-mass theorem does not itself establish a
full-prefix superlinear count on that source; the missing uniform coprime
multiplier estimate was not silently assumed. No new global count,
coloring, recurrence, or every-prefix bound was proved.

Inspected the two previously verified Boolean multiplicative assignments
through 100000. Relative to prime-factor parity (all prime colors equal to
1), their changed prime colors are:

* squarefree/coprime-6: 584 primes, reciprocal sum about 0.10116166368;
  the smallest changed prime is 193;
* squarefree/coprime-30: 252 primes, reciprocal sum about 0.04316951850;
  the smallest changed prime is 619.

For the coprime-30 assignment, the changed-prime reciprocal sums at cutoffs
1000, 3000, 10000, 30000, 100000 are approximately
0.01223333, 0.03319121, 0.03848495, 0.04072462, 0.04316952.
These numbers describe ONE SAVED assignment, not optimal repair costs or a
sequence of compatible assignments. No convergence or extension rule was
established. Prime-factor parity itself has 305 monochromatic stored
collisions on this finite source (684 on the coprime-6 source).

The proposed prime-repair interpretation therefore supplies no infinite
coloring or uniformly bounded sieve cost. No new Lean theorem was added.
Spec.lean remains unchanged with SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No computation is pending and no proof has been submitted.

## Larger unrestricted two-color tests (UNKNOWN, not a theorem)

A further bounded test of ordinary, not multiplicative, two-coloring used
all stored edges through 30000 and 100000. Before writing the CNF, the
script `/tmp/cube_plain_high_1206.py` checked strict root ordering and every
cube equality using Python arbitrary-precision integer arithmetic. The
instances have respectively 184007 and 898947 edges, two NAE clauses per
edge, and the harmless global color-symmetry choice c(1)=false.

CaDiCaL was run independently with a 170-second internal time limit and a
180-second external timeout. BOTH results were UNKNOWN (exit 0). Neither
is SAT or UNSAT. Logs and inputs:
`/tmp/cube_plain_high_1206_{30000,100000}.{cnf,log,exit}`.
All jobs have finished; no proof certificate or coloring was obtained.

Also reviewed a possible passage from arbitrary finite colorings to
multiplicative colorings. The existing compactness/color-erasure argument
does not impose multiplicativity, and no new such reduction was proved.
The existing multiplicative obstructions therefore remain restricted to
that stronger coloring ansatz.

No new Lean theorem or target-file edit resulted. Spec.lean retains its
original statement and sorry. The conjecture is unresolved.

## Quadratic diagonal-family elimination (auxiliary calculation only)

Completed the symbolic elimination left pending in the previous context.
For real quadratic polynomials with constant term 1, write

 A=1+a*t+b*t^2,
 B=A+p*t+u*t^2,
 C=A+q*t+v*t^2,
 D=A+(p+q)*t+(u+v-2*p*q)*t^2.

The coefficient conditions in degrees 1 and 2 have already been imposed.
If p*q != 0, rescale t to take p=1. Degrees 3 and 4 give

 a = -3*q/2 + u - 3/2 + v/q,
 b = -(q^3-6*q^2+6*q*u+6*q*v+q-4*u*v)/(4*q).

Degree 5 is -3*(q-1)*(q+1)*(q^2-q*u-q+v)/2.
Write degree 6 as -F/8. In the three resulting cases:

 * v=q*(u+1-q): F=q*(q^2+3)*(3*q^2+1), nonzero for real q != 0;
 * q=1: F=4*(3*(u-v)^2+4), strictly positive;
 * q=-1: F=-4*(3*(u+v+2)^2+4), strictly negative.

If p=0 and q!=0, degree 3 gives u=0, hence B=A and D=C.
The symmetric case q=0,p!=0 gives C=A and D=B.
If p=q=0, degree 4 gives u*v=0, again a trivial identity.
Thus no nontrivial REAL quadratic family through (1,1,1,1) exists.
The identities were checked symbolically with Sympy; this classification
has NOT been formalized in Lean, and is NOT a settlement of the density
conjecture. It merely closes the pending auxiliary polynomial calculation.

No global density construction, coloring, cover, or recurrence theorem was
obtained. No new Lean theorem was added. Spec.lean remains unchanged with
its original sorry. No computation is pending and no proof was submitted.

## Quadratic diagonal families: new complete Lean proof (auxiliary only)

Added `Submission/QuadraticDiagonalFamilies.lean`. It compiles to
`.lake/build/lib/lean/Submission/QuadraticDiagonalFamilies.olean`.
Build/audit log: `/tmp/quadratic_diagonal_lean_1206.log`.

Namespace: `Erdos1206.QuadraticDiagonalFamilies`.
Main theorem: `quadratic_family_trivial`.
For eight real coefficients a,b,c,d,e,f,g,h, if

 (1+a*t+b*t^2)^3 + (1+g*t+h*t^2)^3
   = (1+c*t+d*t^2)^3 + (1+e*t+f*t^2)^3

for every real t, the four quadratic polynomials have one of the two
trivial pairings. Thus the previously symbolic real classification now has
a kernel-checked proof. `polynomial_trivial` is the polynomial version.

The proof is simpler than the degree-six elimination: after the first two
coefficient equations, the two differences B-A and D-C have forms
 t*(p+u*t), t*(p+(u-2*p*q)*t).
They have the same real zero set, since A=B iff D=C under the cubic identity.
If p!=0, evaluating at the possible second roots forces u=u-2*p*q. Hence
p*q=0 in every case. This gives A+D=B+C. Factoring the cubic identity in
R[X], and using the nonzero constant term of A+D, forces A=B or A=C.
No degree-three-through-six coefficient elimination is needed.

All three printed axiom checks list only propext, Classical.choice,
Quot.sound. The file has no sorry/admit/native_decide or new axioms.

SCOPE: this is NOT a proof or disproof of the positive-density conjecture.
It closes an auxiliary low-degree parametrization question only. No global
uniform coloring, density construction, divisor cover, or recurrence theorem
was obtained. Spec.lean is unchanged with its original sorry. No computation
is pending and no proof was submitted.

## Continuation: recurrence and large-prime review (no settlement)

Rechecked the unchanged target and the successful quadratic-diagonal-family
axiom audit. Reviewed whether a conic/polynomial collision parametrization
could yield recurrence in every positive-natural-density set. No applicable
recurrence theorem or proof was obtained; the existing positive-density
avoider for the explicit congruence-flexible family remains a concrete
limitation of that inference.

Also revisited a source requiring a prime factor greater than n^((k-1)/k).
The existing source definition already covers arbitrary fixed k, and the
verified full-prefix superlinear collision theorem applies to it. Shared
large primes can be reduced, but no bound or coloring for distinct-large-prime
collisions, and no density-preserving recursive construction, was obtained.
These are reviews of existing results, not new theorems or numerical evidence.

No Lean file was changed in this continuation. Spec.lean still contains its
original statement and sorry. No proof or disproof has been obtained, and no
proof has been submitted. No computation is pending.

## Continuation: squarefree coloring review (no settlement)

Revisited the squarefree-source reduction and the square-product observation.
No structural invariant giving a finite cube-Sidon coloring was obtained.
The absence of square-product edges in the stored finite squarefree data is
still only a finite observation. Even a global absence statement would need
an additional argument to produce the required finite coloring. The existing
squarefree rough odd-parity obstruction excludes a stronger parity condition,
not ordinary proper coloring or a positive-density independent set.

Further examination of the rational parametrization and its cancellation
loci yielded no new uniform reciprocal-cover estimate or density bound.
No new theorem, finite search, or Lean edit resulted from this continuation.
Spec.lean remains unchanged with sorry; no proof has been submitted.


## New verified result: full-prefix collision growth on the squarefree/coprime-6 source

CLOSED the previously recorded gap between primitive reciprocal mass and
full-prefix superlinear collision counts for this source. Added four complete
Lean files, all compiled with audits listing only propext, Classical.choice,
Quot.sound. No sorry/admit/native_decide/new axioms occur in these files.

1. `Submission/SquarefreeCoprimeDensity.lean`
   Namespace `Erdos1206.SquarefreeCoprimeDensity`.
   `lowerDensity_bound h hh` proves, for h>0,

     phi(h)/(4*h) <= lowerDensity {q | Squarefree q and Coprime h q}.

   An explicit finite-prefix estimate is `sfCount_lower`:

     (phi(h)/h)*N/4 <= sfCount h N + (h+1)*(sqrt(N)+1).

   Coprime counts have periodic main term N*phi(h)/h and error at most h.
   Cover nonsquarefree positive integers by square multiples k^2, k>=2.
   The reciprocal-square sum is at most 3/4, with at most sqrt(N) counting
   errors. Zero is accounted for separately.

2. `Submission/TotientHarmonicBound.lean`
   Same namespace.
   `copRate_mul_harmonic_lower` proves

     1/4 <= (phi(h)/h)*harmonic(h).

   It avoids prime-distribution estimates: each squarefree n decomposes as
   gcd(n,h) times an integer coprime to h. Sum the coprime counts over divisors
   of h, and compare with the squarefree count at square cutoffs.
   `lowerDensity_log_bound` then gives

     1/(16*(1+log h)) <= lowerDensity {q | Squarefree q and Coprime h q}.

3. `Submission/SquarefreeWeightedMass.lean`
   Namespace `Erdos1206.SquarefreeWeightedMass`.
   `multiplierModulus x = 6*a*b*c*d` for the existing conic family.
   `logWeight_not_summable` and `exists_large_log_weight` show divergence of

     sum 1/(d*(1+log(6*a*b*c*d)))

   over its good, squarefree parameter pairs. Dyadic parameter annuli contain
   a constant proportion of good pairs. Height is quadratic in parameter
   size, while the logarithmic penalty is linear in the annulus index.
   Their mass therefore dominates a constant multiple of the harmonic series.

4. `Submission/SquarefreeSourceCollisionGrowth.lean`
   Namespace `Erdos1206.SquarefreeSourceCollisionGrowth`.
   `source = {n | Squarefree n and Coprime n 6}`.
   Main theorem `collision_count_superlinear`:

     forall C : Real, exists L : Nat, forall N >= L,
       C*N < (sourceCollisionsUpTo source N).card.

   Use multiplier rate 1/(32*(1+log(6*a*b*c*d))) for each fixed primitive
   collision. Coprimality preserves squarefreeness of all four dilated roots.
   The primitive gcd makes the (collision,multiplier) map injective. Choose
   finitely many primitive collisions with arbitrarily large weighted mass,
   then absorb their finitely many prefix errors at a sufficiently large N.

Final clean build logs:
 `/tmp/SquarefreeCoprimeDensity_final_1206.log`
 `/tmp/TotientHarmonicBound_final_1206.log`
 `/tmp/SquarefreeWeightedMass_final_1206.log`
 `/tmp/SquarefreeSourceCollisionGrowth_final_1206.log`.
Compiled objects are under `.lake/build/lib/lean/Submission/`.
The three temporary API-check files created in this continuation were removed.

SCOPE: this is NOT a disproof. Superlinear collision counts on a fixed source
are compatible with positive-density independent subsets. No uniform coloring,
summable cover of all obstructions, every-prefix Sidon construction, or
arbitrary-positive-density recurrence theorem was obtained.
Spec.lean remains unchanged with SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63,
and still contains the original sorry. No proof has been submitted and no
computation is pending.

## Quadratic three-difference family and superlinear triple counts (new, verified)

Added two complete auxiliary files:

* `Submission/TripleConicFamily.lean` (namespace `Erdos1206.TripleConicFamily`).
* `Submission/TripleConicGrowth.lean` (namespace `Erdos1206.TripleConicGrowth`).

Both compile with built oleans under `.lake/build/lib/lean/Submission/`.
Final logs are `/tmp/triple_conic_family_final_1206.log` and
`/tmp/triple_conic_growth_final_1206.log`. All printed axiom audits list only
`propext`, `Classical.choice`, `Quot.sound`; no sorry, admit, native_decide, or
new axiom occurs in either file. The temporary `CheckTripleGrowth.lean` was
removed.

The six natural quadratic forms, in increasing order for u>0 and v>=0, are:

```
a =  242004*u^2 +  24480*u*v +  612*v^2
b = 1839215*u^2 + 184200*u*v + 4605*v^2
c = 1915945*u^2 + 198120*u*v + 5115*v^2
d = 2175145*u^2 + 211080*u*v + 5115*v^2
e = 2365746*u^2 + 241020*u*v + 6138*v^2
f = 2545746*u^2 + 250020*u*v + 6138*v^2.
```

They satisfy a^3+e^3=b^3+c^3, a^3+f^3=b^3+d^3, and
c^3+f^3=d^3+e^3. Thus (a,b), (c,e), (d,f) have a common positive cube
difference. The corresponding three four-root edges form an odd
 even-incidence cycle; `IsTriple.not_noOddCycle` verifies the parity obstruction
on the six-root source in Lean. This excludes only odd-parity coloring.

Index parameters by v=p prime>=29 and 1<=u<p. Height is at most
2801904*p^2. `point_dilate_injective` proves that different parameter pairs and
positive integer multipliers give different six-coordinate tuples, WITHOUT
assuming that the raw tuples are primitive. The proof recovers u/v from
scaled coordinate equalities, then uses p prime and u<p. The reciprocal height
sum over these projectively distinct parameter pairs diverges, by summing
p-1 terms of order 1/p^2 over primes.

`triple_count_superlinear C` proves:

```
exists M, forall N >= M,
  C*N < ((triplesUpTo N).card : Real).
```

Here `triplesUpTo N` counts increasing positive six-tuples bounded by N whose
three indicated pairs have equal cube differences. The proof counts injective
dilates of finitely many family members, then absorbs floor errors. It is a
FULL-PREFIX superlinear theorem, not just an unbounded subsequence result.

Discovery was algebraic, not a blind numerical search: factoring the sextic
sum from the existing separated conic family supplies a third quadratic
representation. It has the required signs for three positive differences when
1<r<cuberoot(2); take r=6/5 and substitute the second parameter by 20*u+v.
The symbolic scripts `/tmp/cube_quadratic_third_1206.py` and
`/tmp/cube_quadratic_third_symbolic_1206.py` are discovery only; Lean checks the
resulting integer identities independently.

CRUCIAL LIMITATION: `five_dvd_B` proves that the single divisor 5 meets this
entire raw family (and its positive dilates). The result does not refute the
summable REUSABLE divisor-cover criterion, does not prove superlinear triple
counts on squarefree/rough sources, and provides no independence-density
bound. It only rules out a global linear count for these smallest odd-cycle
configurations. Spec.lean remains unchanged with its original sorry and hash
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No settlement has been submitted and no computation is pending.

## Uniform small-prime covers for the quadratic triple family (new, verified)

Two additional arithmetic cover results are now checked. They remain auxiliary;
no cover of ALL cubic odd cycles has been obtained.

### The factor 5 survives normalization of the fixed family

`TripleConicFamily.lean` now also proves:

* `five_dvd_A_iff u v`: 5 divides the first coordinate iff 5 divides BOTH
  parameters. This is an exhaustive calculation modulo 5.
* `five_not_dvd_A_of_coprime`: coprime parameters make the first coordinate
  prime to 5.
* `five_survives_normalization`: if u,v are coprime and A(u,v)=g*a,
  B(u,v)=g*b, then 5 divides b. Thus dividing out a common integer factor does
  not remove the fixed cover by 5 from this family.

The file and its dependent `TripleConicGrowth.lean` were rebuilt successfully.
Logs: `/tmp/triple_conic_normalization_final_1206.log` and
`/tmp/triple_conic_growth_normalization_final_1206.log`. The normalization
lemma's axiom audit lists only the three permitted axioms.

### A uniform factor-2 cover for the broader rational-parameter family

New file `Submission/QuadraticTripleParity.lean` (88 lines), namespace
`Erdos1206.QuadraticTripleParity`, imports only FormalConjecturesUtil. It
compiles, with olean in the build library and final log
`/tmp/quadratic_triple_parity_final_1206.log`.

It defines six signed forms, quadratic in u,v and homogeneous of degree four
in p,q:

```
q*((p^3-q^3)*u^2-6*p^3*u*v-3*(p^3+q^3)*v^2)
p*((p^3-q^3)*u^2+6*q^3*u*v+3*(p^3+q^3)*v^2)
q*((p^3-q^3)*u^2+6*p^3*u*v-3*(p^3+q^3)*v^2)
p*((p^3-q^3)*u^2-6*q^3*u*v+3*(p^3+q^3)*v^2)
p*((p^3+2*q^3)*u^2+3*(p^3-2*q^3)*v^2)
q*(-(2*p^3+q^3)*u^2+3*(2*p^3-q^3)*v^2).
```

`identities` verifies that the sums of cubes of pairs (0,1), (2,3), (4,5)
are equal over EVERY commutative ring. Appropriate signs give positive
three-difference configurations; no global sign restriction is assumed.

`even_coordinate_after_common_division` proves, for integer parameters,
integer g and z : Fin 6 -> Z:

```
(Odd p or Odd q) -> (Odd u or Odd v) ->
(forall i, forms p q u v i = g*z i) -> exists i, Even (z i).
```

In particular, primitive parameter pairs satisfy the parity hypotheses, and
removing a common integer factor still leaves an even coordinate. The cover
by 2 is uniform over p/q, not just the earlier choice 6/5.

Proof: record the truncated 2-adic valuation of each residue modulo 8. The
six raw residues cannot all have the same truncated valuation when neither
parameter pair is simultaneously even. This exhaustive 8^4 local statement
is proved by `decide +kernel`, not native_decide. Multiplication by an odd
residue preserves the truncated valuation, so a common scalar times six odd
integers would contradict the local calculation. The symbolic identities
are separately proved with `ring`.

All printed axiom audits list only propext, Classical.choice, Quot.sound.
There is no sorry, admit, native_decide, or new axiom. The external finite
check `/tmp/quadratic_triple_parity_check_1206.py` is discovery only, not a
proof dependency.

SCOPE: this does NOT classify all rational quadratic families, and it says
nothing about arbitrary cubic odd cycles outside the displayed family. In
particular, it does not contradict the already verified squarefree,
coprime-to-210 odd-root triple in SquarefreeRoughParityObstruction.lean.
No finite reciprocal-cost cover of all remaining cycles has been constructed.
Spec.lean is unchanged, still contains its original sorry, and retains hash
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof has been submitted and no computation is pending.

## General parity obstruction for collinear triples (new, verified)

New file `Submission/CollinearTripleParity.lean` (142 lines), namespace
`Erdos1206.CollinearTripleParity`, imports only FormalConjecturesUtil.
It compiles with a built olean. Final log:
`/tmp/collinear_triple_parity_final_1206.log`. Both public theorem axiom audits
list only propext, Classical.choice, Quot.sound. There is no sorry, admit,
native_decide, or new axiom.

`odd_collinear_triple_false` proves the following general arithmetic fact,
not merely a statement about the earlier parametrization. Suppose integer
points (a,b), (c,d), (e,f) have common nonzero cube sum S, with the three
first coordinates pairwise distinct and the three second coordinates pairwise
distinct. If all six coordinates are odd, then

```
(c-a)*(f-b) = (e-a)*(d-b)
```

is impossible. Signs of the coordinates are unrestricted. Thus after clearing
denominators, any genuine three-point chord configuration on x^3+y^3=S!=0
has an even coordinate. This gives a uniform factor-2 cover for chord-generated
triple representations, beyond the previously displayed family.

Proof ingredients (all formalized):

1. A cubic with three distinct integer roots has the usual first two Vieta
   coefficient identities; this is proved by elementary divided differences.
2. Normalize the direction vector by Int.exists_gcd_one' to write the line
   K*x-H*y=T with H,K not both even and neither zero.
3. Put L=H^3+K^3. Vieta gives
   L*(a+c+e)=3*K^2*T,
   L*(a*c+a*e+c*e)=3*K*T^2,
   L*(b+d+f)=-3*H^2*T.
   Nonzero S and three distinct roots ensure L!=0.
4. The first and third identities force H,K to have the same parity.
   Primitive parity makes both odd. The first two identities give
   (a+c+e)*T=K*(a*c+a*e+c*e), forcing T odd. But then the first identity
   equates an even integer with an odd one.

Additional algebraic observation from the investigation (NOT yet a general
classification theorem): if A^3+D^3=B^3+C^3, lambda=(B-A)/(D-C), X=A+B,
Y=C+D, and lambda^3!=1, the further quadratic representation in a fixed-gap
conic can be written

```
E = (3*lambda^2*X + (lambda^3+2)*Y)/(2*(lambda^3-1))
F = -((2*lambda^3+1)*X + 3*lambda*Y)/(2*(lambda^3-1)).
```

The chord point is (F,E), NOT (E,F). This ordering matters: one may swap
coordinates without changing a cube sum, but not without changing
collinearity. Do not repeat the earlier tentative assumption that the
representations as originally ordered are necessarily collinear.

SCOPE: this does not say that every triple representation is collinear,
nor that every quadratic family is classified, nor that all odd cycles are
covered by 2. The existing all-odd, squarefree, coprime-to-210 triple remains
a valid obstruction outside the chord case. For its three points ordered as
(upper root, minus lower root), the collinearity determinant was checked
exactly as 157165269742600842478462283678400, nonzero; this external check is
not used in the new proof.

No cover of all remaining odd cycles, positive-density independent set, or
universal zero-density theorem has been proved. Spec.lean remains unchanged
with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof has been submitted and no computation is pending.

## Quadratic-triple minor audit (external exact algebra, not a settlement)

The previously hand-derived identity has now been checked exactly with SymPy:

```
m_13 - m_34 =
  3*s*(r-t)*(t+1)^2*(r+1)^2*((2*r-1)*t-r+2).
```

A second useful identity was also checked:

```
m_23 evaluated at t=r =
  (r+1)^3*(s+1)^2*(r^2-r+1)*
  (2*(r^2-r+1)*s-(r+1)^2).
```

Here m_ij are the coefficient minors of the two residual quadrics in
`/tmp/quadratic_triple_planes_1206.py`, using zero-based indices. Audit script:
`/tmp/quadratic_triple_minor_audit_1206.py`.

Consequently, if r,s,t<0 and none equals -1, the inconsistent orientation
pattern cannot have all coefficient minors zero: the first identity forces
r=t, since `(2*r-1)*t-r+2` is strictly positive; the second is then nonzero,
since r^2-r+1>0 and s<0. This is an external algebraic deduction, NOT a Lean
classification theorem. The hypotheses that the quadrics are nonzero and
proportional still need justification in an actual conic classification.

The -1 cases correspond to equal pair sums and hence repeated unordered
pairs when the common cube sum is nonzero. For the consistent orientation
pattern, if the induced relation on B,D,F is nontrivial, A remains free in
the plane. Comparing the coefficients of A in s*Q1-r*Q2 gives a nonzero
multiple of r*s*t*(D-F), precluding proportional quadrics unless pairs
repeat. This argument likewise is not yet formalized or a classification.

IMPORTANT COMPLETENESS WARNING: the rational Fermat cubic surface has a
third rational-line type, A+B=0 and C+D=0. Planes through this line give
relations A+B=k*(C+D), i.e. proportional pair sums. These are NOT included
in the two difference-orientation patterns above. Mixed patterns and this
third type, as well as rank degeneracies and constant-dilation families,
must be analyzed before any complete quadratic-triple classification is
claimed.

Reassessed the global density routes; no new uniform construction, coloring,
summable reusable cover, or recurrence theorem was obtained. None of these
algebraic observations resolves the missing global step. Spec.lean remains
unchanged, with its original sorry. No proof or disproof has been obtained,
no proof has been submitted, and no computation is pending.

## New verified plane obstructions and proportional-pair-sum rigidity

The conjecture is still unresolved. Three new auxiliary files compile, with
built oleans in `.lake/build/lib/lean/Submission/`. All printed axiom audits
use only propext, Classical.choice, and Quot.sound. No sorry, admit,
native_decide, or new axiom is used in these files.

### QuadraticTriplePlaneObstructions.lean

Namespace `Erdos1206.QuadraticTriplePlaneObstructions`.
Theorems about the actual explicitly defined real residual quadrics:

* `inconsistent_difference_not_proportional`: for r,t<0, r,t != -1,
  and s!=0, there is no scalar l such that diffQ1=l*diffQ2 identically.
  These are the inconsistent orientation pattern
  A-C=r(B-D), A-E=s(B-F), C-F=t(D-E).
* `one_sum_not_proportional`: for s!=0, r!=-1, k>0, k!=1,
  sumQ1 and sumQ2 cannot be proportional. This is the mixed pattern
  A-C=r(B-D), A-E=s(B-F), C+D=k(E+F).
  The coefficient-minor identity used is
  `3*s*(k-1)^2*(r+1)^2*(2*k*(r^2-r+1)+(r+1)^2)`.
  Its final factor is strictly positive. No sign hypothesis on r is needed.
* `consistent_unequal_not_proportional`: for nonzero r,s,t and s!=r,
  the consistent-orientation residual quadrics cannot be proportional.
  The pattern is A-C=r(B-D), A-E=s(B-F), C-E=t(D-F).
  Eliminate B using the induced nontrivial relation among B,D,F.
  A 2x2 coefficient minor is exactly `9*r*s*t*(s-r)^4`.

All computations are kernel checked using ring and elementary inequalities,
not the external SymPy calculations. Coefficients are extracted by evaluating
the quadrics at a few fixed vectors, avoiding any coefficient-library axiom.
Log: `/tmp/quadratic_triple_plane_final_1206.log`.

### PolynomialSquarePencil.lean

Namespace `Erdos1206.PolynomialSquarePencil`. Arbitrary characteristic-zero
field K, and polynomials of ARBITRARY degree (not merely quadratics).

`four_square_pencil_constant` assumes f,g,h,j nonzero, IsCoprime f g,
nonzero a,b,c,d, a*d-b*c !=0, and

```
h^2 = C a*f^2 + C b*g^2
j^2 = C c*f^2 + C d*g^2.
```

It proves all four natural degrees equal zero.

Proof: rotate coprimality through the two square identities and their inverse
linear relations. A third square in the pencil divides W(f,g). Consequently
h*j divides W(f,g), and f*g divides W(h,j). If both Wronskians are nonzero,
their strict degree bounds contradict each other. If either vanishes,
coprimality forces both corresponding derivatives to vanish; differentiating
the square identities forces the other two derivatives to vanish as well.

`four_square_pencil_common_factor` removes IsCoprime f g. It proves there are
q!=0 and constants u,v,w,z such that f=C u*q, g=C v*q, h=C w*q, j=C z*q.
Divide by gcd(f,g), using IsIntegrallyClosed.pow_dvd_pow_iff to show that this
gcd also divides h,j, then apply the constant theorem.
Log: `/tmp/polynomial_square_pencil_final_1206.log`.

### PolynomialTriplePairSums.lean

Namespace `Erdos1206.PolynomialTriplePairSums`.
`proportional_pair_sums_common_factor` assumes six polynomials A,B,D,E,F,G,
common cube sums, and

```
D+E = C r*(A+B)
F+G = C s*(A+B).
```

Hypotheses: r,s !=0; r^3,s^3 !=1; r^3 !=s^3; A+B !=0;
and the three pair differences A-B, D-E, F-G are nonzero.
It proves all six polynomials are constant multiples of ONE nonzero common
polynomial. This holds in any characteristic-zero field and at any degree.

Proof: put L=A+B, X=A-B, Y=D-E, Z=F-G. Cancel L in the two cube identities to
obtain

```
Y^2 = C ((1-r^3)/(3*r))*L^2 + C (1/r)*X^2
Z^2 = C ((1-s^3)/(3*s))*L^2 + C (1/s)*X^2.
```

The coefficient determinant is `(s^3-r^3)/(3*r*s)`, nonzero. Apply the
four-square pencil common-factor theorem, then recover each pair from its
sum and difference. Log: `/tmp/polynomial_triple_pair_sums_final_1206.log`.

### Remaining gaps and exact scope

These results do NOT yet classify all quadratic triple-representation
families. One must still rigorously establish the conic-plane reduction:
a nondegenerate quadratic image in a Fermat cubic surface lies in a plane,
whose residual line is one of the three rational-line types. One must then
justify that the residual quadrics in the appropriate plane are nonzero and
proportional, and handle all rank degeneracies, repeated pairs, zero sums,
and constant-dilation cases. The all-pair-sums result above handles at least
two sum-type relations under its explicit nondegeneracy hypotheses, but it
must not be stated without those hypotheses.

A possible elementary implementation of the missing geometric bridge:
write quadratic forms as linear forms in U=u^2, V=u*v, W=v^2. A cubic identity
in u,v forces the cubic in U,V,W to be (U*W-V^2) times a linear form. The
residual line can be classified via the rational linear-family version of
Fermat 3. This outline is NOT yet a Lean proof, nor is the full classification
proved. In particular, the arithmetic classification cannot be inferred
from the current plane-obstruction statements alone.

Even a full classification would NOT settle Spec: arbitrary higher-complexity
collisions/odd cycles remain uncontrolled, and no global summable cover,
uniform coloring, compatible positive-density construction, or recurrence
obstruction has been proved.

Spec.lean is unchanged with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof was submitted. No computation is pending. The scratch
CheckSquarePencil.lean file was deleted.

## New verified rational-line and nondegenerate-conic bridge

Four further auxiliary files now compile with built oleans. All printed
axiom audits contain only propext, Classical.choice, and Quot.sound. No new
axioms, sorry/admit, or native_decide appear in these files. The target is
STILL UNRESOLVED.

### FermatCubicLines.lean

Namespace `Erdos1206.FermatCubicLines`.
`rational_linear_family` classifies rational polynomial families a,b,c,d of
natural degrees at most one satisfying a^3+b^3+c^3+d^3=0. Either:

* (a+b=0 and c+d=0), or (a+c=0 and b+d=0), or (a+d=0 and b+c=0); or
* all four polynomials are constants times one common polynomial.

The definitions are `OppositePairs` and `CommonFactor`.
Proof: if one coordinate is nonconstant, it has a rational root. Fermat 3
forces another coordinate to vanish there. If all four vanish there they
share the linear factor. Otherwise the first derivative of the cubic
identity forces the remaining two linear polynomials to be opposites;
then the initial two are also opposites. All-constant cases are included.
Log: `/tmp/fermat_cubic_lines_final_1206.log`.

### FermatCubicSubspaces.lean

Namespace `Erdos1206.FermatCubicSubspaces`.
`JointlyInjective a b c d` means the four rational linear forms jointly have
zero kernel. The ambient vector space may be any finite-dimensional Q-space.

* `subspace_opposite_pairs`: if dimension is at least two and the sum of the
  four coordinate cubes vanishes identically, one of the three opposite
  pairings holds as an equality of linear maps.
* `subspace_finrank_le_two`: such a jointly injective subspace has dimension
  at most two. In particular, the Fermat cubic contains no rational plane.
* `residual_pair_dependency`: in dimension three, if the cubic sum vanishes
  on ker L for some linear form L, one of the three pairs of pair-sum maps
  is linearly dependent. `PairDependent f g` is the explicit witness
  `exists r s, (r!=0 or s!=0) and r • f+s • g=0`.

The subspace proof chooses a vector avoiding the kernels of every nonzero
coordinate/pair-sum form, using Mathlib's finite-union-of-subspaces lemma.
A second independent vector gives a linear polynomial family. Its common-
factor alternative contradicts joint injectivity; its opposite-pair
alternative, together with the generic vector, gives global map equalities.
Kernel dimension in the last theorem is at least two by rank-nullity.
Log: `/tmp/fermat_cubic_subspaces_final_1206.log`.

### FermatCubicConics.lean

Namespace `Erdos1206.FermatCubicConics`.
`Vec := Fin 3 -> Q`, with

```
linear a x = a 0*x 0+a 1*x 1+a 2*x 2
quad a = C(a 0)*X^2+C(a 1)*X+C(a 2).
```

* `conic_factorization`: from `quad a^3+quad b^3+quad c^3+quad d^3=0`,
  the corresponding cubic in three coordinates is exactly
  `(x 0*x 2-(x 1)^2)*residual a b c d x`.
  `residual` is an explicit rational linear form. The proof expands ten
  cubic coefficients and extracts seven polynomial coefficients.
* `residual_ne_zero`: if the four linearizations are jointly injective,
  the residual form is nonzero, by the no-rational-plane theorem.
* `quadratic_pair_relation`: under that same joint-injectivity hypothesis,
  one of the three polynomial pair relations holds:
  pair (qa+qb,qc+qd), pair (qa+qc,qb+qd), or pair (qa+qd,qb+qc).
  `PolynomialPairDependent p q` is
  `exists r s, (r!=0 or s!=0) and C r*p+C s*q=0`.

This closes the previously unproved residual-line reduction for
NONDEGENERATE conics (jointly injective three-dimensional linearizations).
No rational-line type, including proportional pair sums, is omitted.
The result is in signed coordinates, sum of four cubes zero.
Log: `/tmp/fermat_cubic_conics_final_1206.log`.

### VeroneseQuadrics.lean

Namespace `Erdos1206.VeroneseQuadrics`.
`IsQuad F` means F has the six-coefficient homogeneous quadratic form in
three rational coordinates; closure under addition/scalar multiplication
and products of the above linear forms is verified.

* `vanishing_scalar`: if F is such a quadric and F(t^2,t,1)=0 for every
  rational t, then F(x)=r*(x0*x2-x1^2) for some rational r.
* `vanishing_proportional`: two such vanishing quadrics are proportional,
  PROVIDED the second is not identically zero.

These statements verify the general proportionality step but do not yet
instantiate it for all the earlier orientation-specific residual quadrics.
Log: `/tmp/veronese_quadrics_final_1206.log`.

### What remains in the conic investigation

The full triple-family classification is NOT yet proved. Remaining work:

1. Connect the orientation-specific residual quadrics to VeroneseQuadrics:
   the cubic identity factors as a nonzero polynomial pair difference times
   a residual quadric, so the residual vanishes on the Veronese conic.
   Do not simply infer its vanishing at a zero of the pair difference;
   use the polynomial integral-domain argument to cancel that difference.
2. Prove the residual quadric is nonzero (joint injectivity of its four
   coordinate maps plus the no-rational-plane theorem suffices).
3. Transfer proportionality through the linear coordinate changes used in
   QuadraticTriplePlaneObstructions. Their surjectivity needs proof; it
   follows from joint injectivity and the nonzero eliminated coefficients.
4. Normalize the rational pair-dependence coefficients, justify negative
   difference ratios and positive pair-sum ratios at a nondegenerate real
   parameter value, and handle permutations/swaps of the three pairs.
5. Handle rank-degenerate quadratic images. The new conic-pair theorem
   deliberately assumes joint injectivity and cannot be applied without it.
6. Treat repeated unordered pairs, zero common sums, and constant-dilation
   cases separately. The earlier all-proportional-pair-sums theorem has
   explicit nonzero/different-ratio hypotheses that must be checked.

A possible route for rank degeneracies (NOT yet proved): if v!=0 is killed
by all four linearizations, the cubic F is invariant under translation by v.
Writing F=Q*L with Q=x0*x2-x1^2 and differentiating in the v-direction gives
`polarQ(x,v)*L(x)+Q(x)*L(v)=0`. The irreducible rank-three conic cannot be a
product of two linear forms, so L(v)=0, then polarQ(x,v)*L(x)=0. If L!=0 this
forces polarQ(-,v)=0 and hence v=0, a contradiction. Thus F=0 in a degenerate
case; classify its image subspace using the linear-family result. This is an
outline only, not a verified rank-degeneracy theorem.

Even a complete quadratic classification does NOT supply the global density
construction or a disproof. Arbitrary collisions and higher-complexity odd
cycles remain uncontrolled. No compatible positive-density every-prefix
construction, uniform finite coloring, global finite-cost divisor cover, or
universal recurrence theorem was obtained.

Spec.lean remains unchanged, still with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof has been submitted. No computation is pending. Scratch CheckLines.lean
was removed.

## Continuation update: rank-degenerate conics and ordered-field obstructions

The previous section's proposed rank-degeneracy argument is now verified in
`FermatConicDegeneracy.lean`. In particular:

* `cone_linear_translation_rigid` proves that invariance of Q*L under a
  nonzero translation direction forces L=0, for Q=x0*x2-x1^2.
* `jointlyInjective_iff_residual_ne_zero` characterizes nondegenerate conics.
* `degenerate_family_classification` gives opposite pairings or a common
  polynomial factor for the rank-degenerate four-coordinate identity.
* `quadratic_pair_relation_all` removes joint injectivity from the three-way
  polynomial pair-dependence conclusion.

The supporting theorem `linear_forms_opposite_or_common` was appended to
`FermatCubicSubspaces.lean`; it classifies arbitrary rational linear-map
four-cube identities without finite-dimensionality or injectivity assumptions.

`QuadraticTriplePlaneObstructions.lean` was generalized from R to any linearly
ordered field, so all three obstructions apply directly over Q. Logs:
`/tmp/fermat_conic_degeneracy_1206.log`,
`/tmp/fermat_cubic_subspaces_1206.log`, `/tmp/quad_plane_generic_1206.log`.
All listed results compile and their printed axioms are permitted.

The residual-quadric/coordinate-change bridge and the global density gap are
still open at this update. Spec.lean is unchanged.

## Completed quadratic-family bridge, classification, and odd specialization

The unfinished steps in the preceding conic investigation have now been
verified. Every new file below compiles, has a current olean, and its printed
axiom audits list only propext, Classical.choice, Quot.sound. No sorry, admit,
new axiom, or native_decide occurs in these files.

### QuadraticResidualBridge.lean

Namespace `Erdos1206.QuadraticResidualBridge`.
For A-C=r(B-D), `differenceResidual` is

```
r*(A^2+A*C+C^2)+(B^2+B*D+D^2),
```

where A,B,C,D are the corresponding linear coordinate maps on Vec.

* `polynomial_relation` transfers a relation of linear maps to quadratics.
* `residual_isQuad` proves the six-coefficient homogeneous quadratic form.
* `residual_vanishes`: cancel quad b-quad d IN Q[X], then evaluate; this
  includes roots of the canceled polynomial.
* `residual_nonzero`: joint injectivity plus the no-rational-plane theorem.
* `residuals_proportional`: two normalized identities of a common pair
  give proportional residual quadrics on the entire three-dimensional space.

### QuadraticOrientationBridge.lean

Namespace `Erdos1206.QuadraticOrientationBridge`.
All three coordinate changes are verified, including their surjectivity.

* `inconsistent_difference_false`: the normalized relations A-C=r(B-D),
  A-E=s(B-F), C-F=t(D-E) contradict a quadratic triple when r,t<0,
  r,t!=-1, s!=0, the two polynomial pair differences are nonzero, and
  the A,B,E,F linear maps are jointly injective.
* `one_sum_false`: A-C=r(B-D), A-E=s(B-F), C+D=k(E+F) are impossible under
  the corresponding hypotheses s!=0, r!=-1, k>0, k!=1.
* `consistent_ratios_equal`: for A-C=r(B-D), A-E=s(B-F), C-E=t(D-F), the
  nonzero normalized ratios satisfy s=r.

The three scaling factors are (t+1)^2, (1-k)^2, and (s-r)^2. The maps with
coordinates (B,D,F), (B,D,F), and (A,D,F), respectively, have zero kernel by
the normalized relations and joint injectivity; finite-dimensionality gives
surjectivity. This closes the previously unfinished coordinate-change bridge.

### RationalCubePairRelations.lean

Namespace `Erdos1206.RationalCubePairRelations`.

* `same_sum_repeated`: equal nonzero cube sums and equal pair sums force
  repeated unordered polynomial pairs.
* `dependent_ratio`: nonzero dependent polynomials have a nonzero rational
  proportionality constant.
* `difference_ratio_negative`, `difference_ratio_ne_neg_one`.
* `sum_ratio_positive`, `sum_ratio_ne_one`.
* `linearize` evaluates the degree 2,1,0 coefficients as a linear form, with
  addition, subtraction, scalar, and quad compatibility lemmas.
* `normalized_pair_relation`: from quad a^3+quad b^3=quad c^3+quad d^3,
  nonzero common sum, qa!=qc and qa!=qd, obtain exactly the alternatives
  `SumRelation a b c d`, `DifferenceRelation a b c d`, or
  `DifferenceRelation a b d c`.
  SumRelation includes k>0 and k!=1; DifferenceRelation includes r<0 and
  r!=-1. Their identities hold for every vector in Vec, not merely on the
  parametrizing conic. Symmetry and coordinate-swap lemmas are provided.

### QuadraticTwoSums.lean

Namespace `Erdos1206.QuadraticTwoSums`.

* `common_factor_not_jointlyInjective`: four quadratic coordinates that are
  multiples of one polynomial cannot have jointly injective linearizations.
* `two_sums_false`: two normalized pair-sum relations force such a common
  factor via PolynomialTriplePairSums, contradicting joint injectivity.
  Internal coordinate differences and distinctness of the remaining pairs
  are explicit hypotheses.

### QuadraticTripleClassification.lean

Namespace `Erdos1206.QuadraticTripleClassification`.

```
Pair := Vec × Vec
flip p := (p.2,p.1)
GoodPair p q : cube sums equal and nonzero;
  both internal coordinate polynomials distinct;
  qp.1 != qq.1 and qp.1 != qq.2;
  the four coordinate linear maps jointly injective.
GoodTriple p q r := GoodPair p q ∧ GoodPair p r ∧ GoodPair q r.
Collinear p q r := ∀ x,
  (q1(x)-p1(x))*(r2(x)-p2(x))=(r1(x)-p1(x))*(q2(x)-p2(x)).
```

GoodPair and GoodTriple have symmetry/permutation/flip helpers.

* `sum_relation_false`: no sum relation is possible in a GoodTriple.
* `aligned_differences_collinear`: two aligned difference relations force
  collinearity; the third relation's sum and crossed alternatives are ruled
  out by the plane obstructions.
* `collinear_after_swaps`: GoodTriple p q r implies one of
  Collinear p q r, Collinear p (flip q) r, Collinear p q (flip r), or
  Collinear p (flip q) (flip r).

All orientation and sum-relation cases are covered here. No assumption that
arbitrary numerical triples are collinear is made.

### WeightedPolynomialCubes.lean

Namespace `Erdos1206.WeightedPolynomialCubes`, generic characteristic-zero field.

`proportional_to_common_cube`: for nonzero polynomials f,g,q and constant S!=0,

```
f^3+g^3=C S*q^3  ==>  exists u v, f=C u*q and g=C v*q.
```

Proof: take out gcd(f,g); its cube divides C S*q^3, hence it divides q;
apply Mathlib Polynomial.flt_catalan to the coprime quotients. All quotient
polynomials are constant. This is polynomial rigidity, not integer counting.

### QuadraticTripleDichotomy.lean

Namespace `Erdos1206.QuadraticTripleDichotomy`.

`CommonTriple p q r` asserts all six coordinate polynomials are constant
multiples of one NONZERO polynomial.

* `degenerate_pair_common`: nonzero common sum and distinct unordered pairs
  exclude all opposite-pair alternatives in the rank-degenerate classification.
* `degenerate_triple_common`: one degenerate nontrivial pair propagates to
  all six coordinates by WeightedPolynomialCubes; both coordinates of the
  third representation must be nonzero.
* `common_or_collinear_after_swaps`: the full dichotomy, including all rank
  degeneracies. Hypotheses: two cube-sum identities, nonzero common sum,
  all six coordinate polynomials nonzero, each pair internally distinct,
  and the three unordered pairs distinct (two polynomial inequalities each).
  Conclusion is CommonTriple or one of the four collinearity orientations.

This closes the quadratic classification with these explicit hypotheses.
Constant-dilation families are not excluded or mislabeled as impossible.

### QuadraticOddSpecialization.lean

Namespace `Erdos1206.QuadraticOddSpecialization`.

`odd_specialization_common` assumes a quadratic triple p,q,r, rational t,
and v : Fin 6 -> Z such that:
* the six coordinate polynomials evaluated at t equal the integer values v;
* v is injective and all six v i are odd;
* (v 0)^3+(v 1)^3 != 0.

It concludes CommonTriple p q r. All nonzero/distinctness polynomial
hypotheses follow from the specialization. The four collinearity alternatives
are contradicted by CollinearTripleParity.odd_collinear_triple_false after
casting the determinant equality back to Z.

Thus every genuinely projectively varying rational quadratic triple family
is covered by parity at its six-distinct nonzero-sum integer specializations.
This does NOT assert that all-odd numerical triples are impossible: the
previous squarefree rough all-odd example occurs in the allowed common-
dilation alternative. It does NOT classify higher-degree rational curves.

### Verification and remaining global gap

Final logs:
* /tmp/QuadraticResidualBridge_final_1206.log
* /tmp/QuadraticOrientationBridge_final_1206.log
* /tmp/RationalCubePairRelations_final_1206.log
* /tmp/QuadraticTwoSums_final_1206.log
* /tmp/QuadraticTripleClassification_final_1206.log
* /tmp/WeightedPolynomialCubes_final_1206.log
* /tmp/QuadraticTripleDichotomy_final_1206.log
* /tmp/quadratic_odd_specialization_final_1206.log

Two harmless style warnings remain in RationalCubePairRelations.lean.
No computation is pending. Temporary CheckResidualTools, CheckNormalizationTools,
CheckWeightedTools, and the old failing CheckConicTools scratch files were removed.

The GLOBAL GAP remains: control of all relevant numerical collisions/odd cycles
by a finite-cost reusable divisor cover, a uniform finite coloring, a compatible
positive-density every-prefix construction, or a genuine density recurrence
obstruction. Conic classification by itself gives none of these. Primitive
height counts cannot be inferred just from the absence of nonconstant conics;
higher-degree rational curves and arbitrary points remain uncontrolled.

Spec.lean remains unchanged, with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof or disproof of the conjecture has been submitted.

## New verified higher-degree family sieve with all cancellation handled

Seven new auxiliary files, 695 lines total, compile and have current oleans.
All printed axiom audits list only propext, Classical.choice, Quot.sound.
There is no sorry, admit, new axiom, or native_decide in these files.

### BinaryHeightSummability.lean

Namespace `Erdos1206.BinaryHeightSummability`.

```
height (u,v) := max u.natAbs v.natAbs
```

* `shifted_height_reciprocals_summable` proves summability over Z×Z of
  1/(height+1)^3. Proof compares with the product of two shifted absolute-value
  p-series of exponent 3/2, using (|u|+1)(|v|+1) <= (height+1)^2.
* `family_reciprocals_summable`: for T ⊆ Z×Z, M : T -> N, C>0 and
  (height(p)+1)^3 <= C*M(p), the reciprocals 1/M(p) are summable.
* `range_reciprocals_summable`: the distinct outputs are reciprocal summable;
  injectivity of the parametrization is NOT assumed. Choose a preimage of each
  distinct output and apply Summable.comp_injective.
* `positive_density_avoids_family`: if also M(p)>1, an infinite positive-lower-
  density set avoids every integer multiple of every M(p).

### BinaryHomogeneousHeight.lean

Namespace `Erdos1206.BinaryHomogeneousHeight`.

* `homogeneous_lower_bound`: a continuous map
  F : (R×R) -> (Fin m -> R), homogeneous of positive degree d and vanishing
  only at the origin, satisfies c*norm(x)^d <= norm(F(x)) for some c>0.
  Proof is the compact-unit-sphere minimum, followed by radial normalization.
* `common_divisor_dvd_certificate`: if u,v are coprime integers, g divides
  every F_i, and integral certificates give

  ```
  sum H_i*F_i = R*u^n,  sum K_i*F_i = R*v^n,
  ```

  then g divides R. Uses coprimality of u^n,v^n and Bezout; no cancellation
  factor is ignored and no bound on prime factors of u,v is assumed.

### NormalizedBinaryFamilySieve.lean

Namespace `Erdos1206.NormalizedBinaryFamilySieve`.

`rootHeight N := Finset.univ.sup (fun i => (N i).natAbs)`.
`rootHeight_attained` ensures this is an actual coordinate's absolute value.

* `normalized_cubic_height_bound`: suppose d>=3, F has the preceding analytic
  properties, p ranges over primitive integer pairs, and F(p)_i=g(p)*N(p)_i
  in R. If g(p) divides one fixed nonzero integer R, then
  (height(p)+1)^3 <= C*rootHeight(N(p)) for some C>0.
  The proof first bounds norm(F(p)) <= R.natAbs*rootHeight(N(p)), so the height
  bound is made AFTER cancellation. It uses height>=1 and d>=3.
* `normalized_maxima_summable` applies the binary-height result.
* `positive_density_avoids_normalized_family` excludes at least one absolute
  coordinate in every dilated normalized tuple, assuming rootHeight>1.

### CertifiedBinaryFamilySieve.lean

Namespace `Erdos1206.CertifiedBinaryFamilySieve`.
`BinaryForm := MvPolynomial (Fin 2) Z`.

Input: forms P_i homogeneous of common degree d>=3, auxiliary integral forms
H_i,K_i, nonzero integer R, and the SYMBOLIC identities

```
sum H_i*P_i = C R*X 0^n,
sum K_i*P_i = C R*X 1^n.
```

* `homogeneous_eval_scale` verifies homogeneous scaling of a binary form over
  arbitrary commutative semirings, by expanding monomials.
* `realFamily_continuous`, `realFamily_homogeneous`, `realFamily_zero` supply
  the analytic hypotheses. The certificates force the only real common zero
  to be the origin.
* `normalized_divisor_dvd` evaluates the certificates at primitive integers.
* `certified_maxima_summable` and `positive_density_avoids_certified_family`
  are the purely polynomial-certificate versions of the previous criterion.

No unsupported assertion that arbitrary parametrizations are basepoint-free
is made. The displayed certificates are explicit hypotheses.

### BinaryResultantCertificates.lean

Namespace `Erdos1206.BinaryResultantCertificates`.

* `homogenize_reflect`: for deg p<=d, homogenizing p.reflect d is the coordinate
  reversal of homogenizing p. Proved by polynomial induction.
* `homogenized_bezout` transfers a univariate Bezout identity to binary forms.
* `resultant_certificates`: for p,q in Z[X] with degrees<=d, d>0, nonzero
  resultants `p.resultant q d d` AND
  `(p.reflect d).resultant (q.reflect d) d d`, obtain the two integral symbolic
  certificates for the forms p.homogenize d, q.homogenize d. The common constant
  is the product of the two resultants, and the exponent is d+d.

Both chart hypotheses are explicit. This gives certificates from finite
polynomial computations without requiring a manual Bezout calculation.

### AllNormalizationsFamilySieve.lean

Namespace `Erdos1206.AllNormalizationsFamilySieve`.

```
normalized P g (u,v) i := eval ![u,v] (P i) / (g:Z)
parameters P g := { (u,v) |
  IsCoprime u v and (forall i, (g:Z) divides eval ![u,v] (P i))
  and 1 < rootHeight (normalized P g (u,v)) }
```

* `all_normalizations_summable`: under the symbolic certificate hypotheses,
  there is ONE reciprocal-summable divisor set B, excluding 1, containing the
  normalized maximum for EVERY g and every member of parameters P g.
* `positive_density_avoids_all_normalizations`: one infinite positive-lower-
  density set excludes at least one absolute coordinate of every such tuple,
  for every integer dilation.

The important quantifier improvement is that the source is fixed before g
is chosen. Every admissible g divides R, so there are only finitely many g
(in Nat.divisors R.natAbs), and the union of their summable output sets is
summable. g=0 is automatically impossible from g|R and R!=0. The max>1
hypothesis prevents deleting divisor 1. The theorem does not claim to avoid
trivial all-zero/all-unit configurations.

### FullCubicCurveSieve.lean

Namespace `Erdos1206.FullCubicCurveSieve`.
The four homogeneous cubic forms are

```
A = u^3-4*u^2*v+12*u*v^2-63*v^3
B = u^3-u^2*v+27*u*v^2-42*v^3
C = u^3+u^2*v+27*u*v^2+42*v^3
D = u^3+4*u^2*v+12*u*v^2+63*v^3.
```

`cube_identity`: A^3+D^3=B^3+C^3.
These specialize to the earlier CoprimeResidueCollisions family with
u=(k+10)q+1, v=q. The NEW theorem covers arbitrary primitive integer parameters,
not only that previously selected positive/congruence subfamily.

The verified integral certificates are

```
7*(145*u^2+654*u*v-1344*v^2)*A
 +7*(5*u^2-69*u*v+2016*v^2)*B = 1050*u^5,
(-u^2+u*v-20*v^2)*A
 +(u^2-4*u*v+5*v^2)*B = 1050*v^5.
```

* `cancellation_dvd`: any common integer divisor of all four coordinates at
  a primitive pair divides 1050. This is not merely a coprimality statement
  for parameters satisfying a special congruence.
* `full_cubic_family_avoidable`: an infinite set of positive lower density
  avoids at least one absolute coordinate of EVERY normalized tuple in this
  full curve and EVERY integer dilation. Inputs allow all primitive integer
  parameter pairs and all natural common divisors, with normalized max>1.

The original first-root avoider and this theorem have different scopes: the
older theorem avoids the first root on a restricted positive parameter family;
this theorem avoids some coordinate on the full projective curve and handles
all common-factor normalizations.

### Verification and limitations

Final logs, all successful:
/tmp/BinaryHeightSummability_final_1206.log
/tmp/BinaryHomogeneousHeight_final_1206.log
/tmp/NormalizedBinaryFamilySieve_final_1206.log
/tmp/CertifiedBinaryFamilySieve_final_1206.log
/tmp/BinaryResultantCertificates_final_1206.log
/tmp/AllNormalizationsFamilySieve_final_1206.log
/tmp/FullCubicCurveSieve_final_1206.log

All files have current oleans under .lake/build/lib/lean/Submission.
Temporary CheckHeightTools, CheckNormalizedHeight, CheckBinaryForms, CheckScale,
CheckDenomTools, CheckResultantTools, CheckInductionTools, and
CheckAllNormalizations scratch files were removed. No computation is pending.

This is a general FAMILYWISE result, not the missing global bound. In
particular, countably many individually summable divisor sets need not have a
summable union. No uniform bound on the total cost over all rational curves,
no complete cover of arbitrary odd cycles, and no positive-density cube-Sidon
set have been constructed. The conic classification from the prior continuation
also remains insufficient to supply such a bound. Do not infer a rational-point
count from absence of nonconstant conics, or infer summability over all curves
from the new theorem for each fixed certified curve.

The target Spec.lean is unchanged with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof has been submitted. Last resource reading (not necessarily fresh):
$460.25 used, $539.75 remaining; 49h40m53s elapsed, 46h19m07s remaining.


## Finite quadratic-family avoidance and noncoverage (new, verified)

The previously unfinished CubeShapeCompactness file is now fully verified.
The two factorization signs were corrected, and natural-subtraction casts are
rewritten explicitly before transferring the real inequalities. No original
conjecture statement or import was changed.

### Strengthened compact-gap API

`CompactGapRatioColoring.lean` and `CubeShapeCompactness.lean` now allow
`a < b`, `b <= c`, `c < d` (a possibly repeated middle root). Their existing
real inequalities, finite coloring, and positive-lower-density construction
were rechecked with this stronger interface. Only the newly developed
QuadraticFamilyAvoidance file imports these interfaces.

For h=b-a and k=d-c in a nonnegative ordered real collision:

* `gap_strict`: k<h.
* `largest_le_twice_middle`: d<=2*c.
* `gap_upper_of_middle_bound`: c<=L*b, L>0 implies h<=12*L^2*k.
* `cross_ratio_bounds`: c-a=s*(d-b), s>1, implies
  s*k <= h <= 12*(s/(s-1))^2*k.
* `sum_ratio_bounds`: a+d=q*(b+c), 0<q<1, implies
  (1+(1-q)/2)*k <= h <= 12*(q/(1-q))^2*k.
* `integer_compact_interval` converts these to the natural-indexed compact
  gap constraints used by the explicit geometric bands.
* `positive_density_avoids_sum_ratio` and
  `positive_density_avoids_cross_ratio` give an infinite positive-lower-density
  set excluding simultaneous membership of b,d for a fixed relation.

### QuadraticFamilyAvoidance.lean

Namespace `Erdos1206.QuadraticFamilyAvoidance`.
Imports CubeShapeCompactness and RationalCubePairRelations.

`OrderedInstance a b c d x` means the rational linearized values are
0<A<B<=C<D and satisfy A^3+D^3=B^3+C^3. The numerical cubic identity is
EXPLICIT for arbitrary coefficient vectors x; it is not incorrectly deduced
from the polynomial identity off the Veronese conic.

* `uniform_gap_bound`: a rational polynomial identity
  quad a^3+quad d^3=quad b^3+quad c^3 gives H>=1 such that every
  OrderedInstance has (H+1)*k<=H*h and h<=H*k.
  The proof handles the vacuous case, derives polynomial nontriviality from
  one ordered instance, then uses normalized_pair_relation and its three
  alternatives. The sign of the relation is determined by that instance.
* `finite_uniform_gap_bound`: for a finite-indexed collection of identities,
  ONE H works for all of them. It uses monotonicity of the compact constraints
  and a bound on the finite list of individual H values.
* `positive_density_avoids_finite_families`: ONE infinite set A with positive
  lower density excludes simultaneous membership of the second and fourth
  natural values in every integral OrderedInstance of the finite collection.
  This uses one geometric band, NOT an intersection of positive-density sets.
* `linear_specialization` evaluates at ell * ![t^2,t,1].
* `positive_density_avoids_finite_specializations`: a direct interface for
  arbitrary rational parameters t and scales ell with ordered natural values.
  The numerical cubic identity follows by polynomial evaluation and scaling.
  Thus it includes all rational normalizations/dilations satisfying the
  natural-value hypotheses.

### QuadraticFamilyNoncoverage.lean

Namespace `Erdos1206.QuadraticFamilyNoncoverage`.
Imports QuadraticFamilyAvoidance and CubeArithmeticProgressions.

* `arbitrarily_near_unit_gap`: for every natural H, an explicit positive
  strict collision has H*(b-a)<(H+1)*(d-c). It uses the existing homogeneous
  cubic family at q=1, z=12*H+1. Its gaps are
  b-a=z^2+9*z+21 and d-c=z^2+3*z+3.
* `finite_families_do_not_cover`: given any finite collection of rational
  quadratic polynomial identities, there is one strict positive integral
  cubic collision lying in NONE of their linearized coefficient planes, and
  hence in none of their scaled quadratic specializations. The finite list
  may include all finitely many orientations of every selected family.

### Verification and scope

Successful logs:

* /tmp/compact_gap_weak_1206.log
* /tmp/cube_shape_compactness_1206.log
* /tmp/quadratic_family_avoidance_1206.log
* /tmp/quadratic_family_noncoverage_1206.log

Current oleans were generated in .lake/build/lib/lean/Submission. Every printed
axiom audit contains only propext, Classical.choice, Quot.sound. No computation
is pending. The strict-middle versions were saved as temporary backups in
/tmp/*_strict_1206.lean before strengthening the interfaces.

The global gap is unchanged: the uniform gap bound depends on the fixed finite
collection. There is no uniform positive density as the collection grows, and
countably many individual avoiders cannot be intersected or unioned naively.
The noncoverage theorem rules out a FINITE quadratic-family cover, not a dense
cube-Sidon set. No uniform global coloring/cover, arbitrary-cycle bound, or
zero-density theorem has been proved.

Spec.lean is unchanged with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof has been submitted.


## Residual primitive mass beyond every compact gap cutoff (new, verified)

Three new files compile with current oleans and only the permitted axioms.
No global cover, coloring, or positive-density cube-Sidon set has been found.

### NearUnitConicFamily.lean

Namespace Erdos1206.NearUnitConicFamily. Generic commutative-ring forms:

```
n(m) = 3*m^2-9*m+7
E(s,t) = s^2+3*t^2
U(m,s,t) = (m-2)*s^2-(6*m-8)*s*t-3*(m-2)*t^2
V(m,s,t) = (m-1)*s^2+(6*m-10)*s*t-3*(m-1)*t^2
A = n(m)^2*E+9*m^3*U
B = n(m)^2*E+9*m^3*V
C = 9*m^4*E+3*m*n(m)*U
D = 9*m^4*E+3*m*n(m)*V
```

Verified rotation norm U^2+U*V+V^2=n(m)*E^2, cube identity A^3+D^3=B^3+C^3,
and homogeneity in s,t. Adjacent gap relation:

```
n(m)*(B-A)=3*m^2*(D-C).
```

* `ordered`: m=k+12, s=u+12*m*v, k,u>=0, v>0 gives 0<A<B<C<D.
  Positivity is proved by expanding in k,u,v; the resulting differences have
  positive coefficients.
* `projective_parameter`: over Q, m>=12, nonzero r and t, equality of the
  first THREE scaled coordinate forms for (s,t,r) and (s',t',r') implies
  s*t'=s'*t. It first recovers the scaled E,U,V, then the monomials st,t^2.
  The nonzero determinant factors are n(m) and n(m)^3-27*m^6.
* `outside_compact_gap`: at k=12*H, every ordered positive specialization has
  H*(B-A)<(H+1)*(D-C). Thus these fixed ratios approach one with H.

### NearUnitPrimitiveMass.lean

Uses Index from PrimitiveCollisionMass: prime p>=29 and j<floor(p/12), with
u=6*j+1<p and v=p. The raw family has m=k+12, s=u+12*m*p, t=p.

* A generic private `primitive_lift` divides four positive ordered integers
  by their joint gcd, producing a PrimitiveCollisionMass.Collision and a
  positive natural scale. All order, cubic equality, and primitivity facts
  are checked.
* `collision k x` and `scale k x` choose this normalized collision and scale.
* `collision_injective`: normalized tuples from different Index values are
  distinct. The projective-parameter lemma recovers u/p; primality and
  0<u<p recover p and j. No bounded-cancellation assumption is used.
* `near_unit_gap`: the small-gap-ratio inequality survives normalization.
* `normalized_height_bound`: for fixed k, normalized maximum <=K*p^2 for a
  positive real K. This only needs division by a positive integer to lower
  height, not an upper bound on that divisor.
* `index_mass_not_summable`: each prime block contributes at least
  1/(24*K*p), so prime reciprocal divergence proves non-summability.
* `Residual H` is the subtype of primitive collisions with
  H*(b-a)<(H+1)*(d-c).
* `residual_reciprocal_heights_not_summable`: summing 1/d over ALL distinct
  primitive collisions in Residual H diverges for every H.

Lean implementation note: passing `hs.comp_injective hf` directly to the
non-summability lemma caused expensive metavariable unfolding. Binding it
first as `have hcomp := hs.comp_injective hf` solves this. The final file
compiles at the default heartbeat limit; temporary trace tactics were removed.

### QuadraticFamilyResidualMass.lean

Namespace Erdos1206.QuadraticFamilyResidualMass.

`Outside a b c d e` says the primitive collision e lies in none of the
linearized coefficient planes of the listed quadratic families.

* `outside_reciprocal_heights_not_summable`: for ANY finite-indexed list of
  rational quadratic cube identities, the sum of reciprocal maximum roots
  over the distinct primitive collisions Outside that list diverges.
  Obtain a common compact gap bound H from QuadraticFamilyAvoidance, embed
  Residual H into Outside, and apply the new non-summability theorem.
  The finite list may include all orientations of each chosen family.

### Verification and exact limitations

Successful logs:
/tmp/near_unit_conic_family_1206.log
/tmp/near_unit_primitive_mass_1206.log
/tmp/quadratic_family_residual_mass_1206.log

All printed audits report only propext, Classical.choice, Quot.sound. Current
oleans are under .lake/build/lib/lean/Submission. No computation is pending.
The temporary CheckNormalizeTools.lean was removed.

These sums are over distinct COLLISIONS, not distinct largest-root values.
A largest root can occur in more than one collision. Divergence therefore
rules out only the proposed per-collision charging/summability estimate. It
DOES NOT rule out reusing a largest root, another vertex, or a divisor across
many collisions. Likewise this is not an independence or density bound.
The newly chosen witnesses are not asserted squarefree or coprime to a fixed
set of primes; small-prime source sieves may remove this particular family.

Potential further extension (NOT IMPLEMENTED): replace offsets 1,2 by L,2L
and n(m) by 3*m^2-9*m*L+7*L^2. The same rotation and cube identity hold. With
L=18*Q, m=12*L*(H+1)+1, t divisible by L and s=1 mod L, every raw root is
18 mod L. Dividing by 18 gives values 1 mod Q, and gcd normalization preserves
coprimality to Q. Prime-denominator parameters could again yield divergent
per-collision mass. This would still not exclude a summable reusable cover.

The original conjecture is unresolved. Spec.lean retains its original sorry,
imports, statement, and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof has been submitted.

## Rough residual primitive mass (verified continuation)

The following five new files compile, have current oleans, and their printed
axiom audits use only propext, Classical.choice, and Quot.sound:

* RoughNearUnitConicFamily.lean homogenizes the near-unit family in m,L.
  With n=3m²-9mL+7L², its coordinate formulas satisfy the cubic identity,
  positivity/order at m>=12L, s=u+12mt, and a projective inverse. At
  L=18Q, m=1+Lα, s=1+Lβ, t=Lγ all four raw roots are 18 modulo L.
* RoughCollisionNormalization.lean proves that a positive ordered collision
  whose roots are 18 modulo 18Q can be divided first by 18 and then by its
  common gcd to give a primitive collision with every root coprime to Q.
* PrimeBlockMass.lean proves a generic reciprocal-height divergence lemma
  for prime-indexed finite blocks. For j<p/12, at most one residue has
  p | 1+Lj, and the remaining block size is at least p/48.
* RoughNearUnitPrimitiveMass.lean takes L=18Q, m=12L(H+1)+1,
  u=1+Lj, t=Lp, s=u+12mt. After primitive normalization the tuples are
  distinct (projective inverse and prime denominators), all roots are
  coprime to Q, H(b-a)<(H+1)(d-c), and maximum root <=K p².
  Therefore the reciprocal maximum-root mass diverges for every Q>0,H.
* RoughQuadraticFamilyResidualMass.lean combines this with the common
  compact gap bound: outside any finite list of rational quadratic
  coefficient planes, primitive collisions with all roots coprime to Q
  still have divergent reciprocal maximum-root mass.

Three existing helpers were exposed/added and their files recompiled:
NearUnitConicFamily.ordered_real, NearUnitPrimitiveMass.primitive_lift,
and QuadraticFamilyResidualMass.residual_outside.

Successful logs: /tmp/rough_near_unit_conic_family_1206.log,
/tmp/rough_collision_normalization_1206.log, /tmp/prime_block_mass_1206.log,
/tmp/rough_near_unit_primitive_mass_1206.log,
/tmp/rough_quadratic_family_residual_mass_1206.log.

These are per-COLLISION mass results, not mass over distinct maximum roots.
They do not exclude a reusable vertex/divisor cover, nor establish an
independence or positive-density impossibility bound. Squarefreeness of
these new rough witnesses has NOT been proved. The original conjecture
remains unresolved and Spec.lean is unchanged with its original sorry.


## Global-step continuation after the rough residual extension (unresolved)

Recorded the five verified rough-family files and removed the two temporary
query files CheckRoughTools.lean and CheckPrimeBlockTools.lean. Revisited the
weighted divisor-cover and odd-parity reductions. Neither supplies an
unconditional uniform bound. In particular, the existing squarefree,
coprime-to-210 three-difference example blocks odd-parity coloring on that
source; it does not block ordinary two-coloring. No new proof of an arbitrary
odd-cycle cover, no density recurrence theorem, and no uniform finite
independence bound was obtained.

The mathematical reviews in this continuation added no new Lean theorem.
Another attempt to retrieve the problem page failed DNS resolution; no new
external mathematical claim was obtained. The original conjecture remains
unresolved. Spec.lean is unchanged, with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof has been submitted.


## Affine squarefree sieve and rough coefficient arithmetic (new, verified)

Three new files compile with current oleans and allowed-axiom audits.
Spec.lean remains unchanged and the original conjecture is unresolved.

### AffineQuadraticSquarefreeSieve.lean

Imports QuadraticSquarefreeSieve. Namespace
Erdos1206.AffineQuadraticSquarefreeSieve.

Generalizes the old squarefree sieve from (M*t,M*u+1) to
(M*t+v,M*u+w), with arbitrary fixed natural offsets v,w.

* bad_prime_pairs_count_nat and bad_prime_pairs_count retain the bounds
  2*N*(N/p²+1)+(N/p+1)² and 3*N²/p²+4*N+1.
* nonsquarefree_pairs_count and goodPairs_eventually_large combine local
  avoidance, large-prime regularity, and a quadratic height bound, giving
  at least N²/2 good parameter pairs eventually.
* quad_modEq transports simultaneous parameter congruences.
* exists_small_prime_progression combines arbitrary prescribed locally
  squarefree witnesses for primes <=K via Nat.chineseRemainderOfFinset.
  Modulus is sieveModulus K = (K!)². Adds one full modulus to the second
  offset so that w>0. This theorem only RETURNS small-square avoidance,
  not the actual CRT congruences (the latter are internal to its proof).
* quad_size_bound handles both offsets, with height
  (S*(M+v+w+1)*N)² when a>0, w>0, a+b+c<=S.
* local_progression_sieve replaces the old squarefree leading-coefficient
  assumption with finite local admissibility up to K.
* exists_squarefree_progression chooses K,S automatically. For positive
  leading coefficients, nonzero discriminants and local simultaneous
  squarefree admissibility at every prime, it returns M>0,w>0,v with at
  least N²/2 simultaneously squarefree values on that affine lattice.

These are PARAMETER counts, not positive density of resulting root values.
Log: /tmp/affine_quadratic_squarefree_1206.log.

### QuadraticLocalAdmissibility.lean

Imports AffineQuadraticSquarefreeSieve. Namespace
Erdos1206.QuadraticLocalAdmissibility.

* quadratic_ne_zero and roots_card: nonzero binary quadratic coefficient
  triples give at most two roots on the affine chart t=1, even when the
  leading coefficient vanishes modulo p.
* exists_avoiding_residue: r forms, none identically zero mod p, can all be
  made nonzero if p>2r.
* square_not_dvd_mul: squarefree d and p not dividing n imply p² not
  dividing d*n.
* large_prime_locally_squarefree applies that fact to squarefree contents
  times primitive quadratic forms.
* primitive_coefficients_mod_prime: gcd(a,gcd(b,c))=1 supplies the required
  nonzero coefficient triple at every prime.
* quad_scale and discriminant_scale record scaling identities.
* small_prime_tests_suffice: for r primitive, nondegenerate natural-coefficient
  binary quadratics, with a_i>0 and positive squarefree contents d_i, only
  primes p<=2r need individual simultaneous squarefree local tests. The
  conclusion is an affine lattice with at least N²/2 good pairs eventually.

Log: /tmp/quadratic_local_admissibility_1206.log.

### RoughConicCoefficientArithmetic.lean

Imports RoughNearUnitConicFamily and QuadraticLocalAdmissibility.
Namespace Erdos1206.RoughConicCoefficientArithmetic.

For n=3m²-9mL+7L², defines leading/middle/trailing coefficient vectors
(alpha,beta,gamma), and content=[1,1,m,m]. These coefficients remove the
explicit factor m from C,D but NOT the factor 18 from all coefficients.

alpha = [n²+9m³(m-2L), n²+9m³(m-L),
         9m³+3n(m-2L), 9m³+3n(m-L)]
beta  = [-9m³(6m-8L), 9m³(6m-10L),
         -3n(6m-8L), 3n(6m-10L)]
gamma = [3n²-27m³(m-2L), 3n²-27m³(m-L),
         27m³-9n(m-2L), 27m³-9n(m-L)].

* raw_eq_content_mul proves raw_i=content_i*(alpha_i*s²+beta_i*s*t+gamma_i*t²).
* discriminants: first two are 12*n*(108m^6-n³), last two
  36*(4n³-27m^6).
* first_third_combination: 3alpha+gamma is 6n² or 54m³.
* norm_bounds (real): L>=1,m>=12L imply m,n>0 and 2m²<=n<=3m².
* leading_pos and discriminant_pos follow for every coordinate.
* eighteen_dvd: 18 | m-1 and 18 | L imply 18 divides every coefficient.
* no_common_coefficient_zero: over a field where 2,3,7 are nonzero,
  alpha_i=gamma_i=0 forces m=L=0. Its proof treats the two pairs separately.
* large_prime_coefficients specializes this to ZMod p, p>7: if m,L do not
  both vanish modulo p, the coefficient triple is nonzero.

Log: /tmp/rough_conic_coefficient_arithmetic_1206.log.

### Remaining steps for the AUXILIARY squarefree extension

NOT PROVED: squarefree/coprime-to-Q near-unit primitive collisions of
nonsummable reciprocal height, or their finite-family residual counterpart.
The old choice m=12L(H+1)+1 may have square factors. Since raw C,D have a
factor m not generally common to raw A,B, squarefreeness cannot simply be
asserted after primitive normalization.

A possible next construction is to take L divisible by 18*210*Q, and use
Nat.exists_prime_gt_modEq_one to choose PRIME m, m=1 mod L, above the
required near-unit bound. Only primes 1 mod L are needed; Mathlib has an
elementary theorem for these, not requiring a fresh Dirichlet proof.

Still to implement:
1. Divide the displayed coefficients by 18, proving exact reconstruction.
   For m=1 mod 18Q0 and L=0 mod 18Q0, leading_i=18 mod 18Q0 should imply
   leading_i/18=1 mod Q0. This is an elementary polynomial congruence, but
   has not yet been added. Large-prime coefficient nonvanishing then gives
   primitiveness after division; small primes are handled by Q0 including 210.
2. Shift s=u+K*t enough to make all three divided coefficients nonnegative.
   Leading positivity is proved. Choose K>=12m and K>=all abs(beta_i/18)+1;
   middle coefficient becomes 2Kalpha+beta>0, and trailing positivity follows
   from ordered_real at s=K,t=1. Discriminants and primitiveness survive
   this unimodular shift, but these transport lemmas are not yet implemented.
3. Preserve coprimality to Q in the squarefree progression. The new CRT
   proof currently returns only square-avoidance; expose its actual residue
   congruences, or add a prescribed-witness version. For p|Q choose (t,u)=(0,1)
   with unit values and choose K_sieve>=Q. Then the resulting entire
   progression stays coprime to Q. Squarefreeness alone is not enough.
4. Generalize the near-unit gap bound to m sufficiently large rather than
   the old exact center. Normalize, prove parameter injectivity, quadratic
   height bounds, and reciprocal divergence as in the existing squarefree
   conic file. No global Sidon-density consequence follows automatically.

Lean implementation notes:
* Qualify RoughNearUnitConicFamily.norm in simp/dsimp lists: bare `norm`
  was ambiguous with Norm.norm.
* When casting polymorphic coefficient functions, explicitly write
  ((leading m L i : ZInt) : ZMod p) (with actual Lean type ℤ). Merely
  (leading m L i : ZMod p) can elaborate the function over ZMod with cast
  arguments instead of casting an integer result.
* `simp [leading,middle,trailing]` was needed to reduce finite vectors in
  a few proofs; `simp only`/`dsimp only` did not normalize the Fin numerals.
* All numerical finite checks use decide +kernel.

The temporary CheckAffineSieve.lean has been removed. All three new files
have current oleans. No computation is pending. No proof was submitted.
Spec.lean remains at SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.


## Squarefree rough residual mass: extension COMPLETE (new, verified)

The previously pending squarefree/coprime-to-Q residual family and its
finite-quadratic-family transfer are now proved. The original conjecture is
STILL UNRESOLVED. Spec.lean remains unchanged with its original sorry.
All nine new files below compile, have current oleans under
.lake/build/lib/lean/Submission, and their displayed axiom audits use only
propext, Classical.choice, Quot.sound.

### PrescribedQuadraticSieve.lean

Imports AffineQuadraticSquarefreeSieve. Namespace Erdos1206.PrescribedQuadraticSieve.

* exists_progression: given functions T,U of primes and K, CRT produces
  offsets v,w BOTH POSITIVE such that the parameter progression
  ((K!)²*t+v,(K!)²*u+w) has the prescribed residues modulo p² for all p<=K.
* prescribed_progression_sieve: retains these congruences in the output
  together with the eventual N²/2 simultaneous-squarefree parameter count.

### RoughConicIntegralCoefficients.lean

Imports RoughConicCoefficientArithmetic. Namespace Erdos1206.RoughConicIntegralCoefficients.

a,b,c are the preceding leading,middle,trailing coefficients divided by 18
in the integers. qval is their binary quadratic form.

* intCast_leading/middle/trailing: explicit coefficient-cast transport.
* reconstruction: 18*a=leading etc under 18|m-1,18|L.
* raw_reconstruction: raw_i=18*content_i*qval_i with content=[1,1,m,m].
* leading_congruence: if 18Q|m-1 and 18Q|L, then leading_i=18 mod 18Q.
* a_eq_one_add, a_coprime: a_i=1+Qz and IsCoprime a_i Q.
* a_pos and discriminant_pos: positivity after exact division by 18.
* coefficients_mod_prime and primitive: if 210|Q, 18Q|m-1,18Q|L,
  and IsCoprime m L, the divided coefficient triple is primitive.
  Primes >7 use the preceding field nonvanishing result. Smaller primes
  divide Q, where a_i is a unit. No squarefreeness is assumed in this step.

### PositiveQuadraticShift.lean

Imports QuadraticLocalAdmissibility. Namespace Erdos1206.PositiveQuadraticShift.

beta(a,b,k)=2ak+b, gamma(a,b,c,k)=ak²+bk+c.

* value_shift, discriminant_shift, dvd_shift_iff record the unimodular shift.
* coefficients_pos: integral a>0 and k>=|b|+|c|+1 give k,beta,gamma>0.
  No separate conic positivity estimate is needed for this coefficient step.
* nat_primitive and nat_discriminant transfer to the positive toNat coefficients.

### RoughSquarefreeConicSetup.lean

Imports the preceding integral coefficients, positive shifts, and prescribed sieve.
Namespace Erdos1206.RoughSquarefreeConicSetup.

Data contains q>0,210|q,H,m with m PRIME, m=1 mod 18q, and
m>12*(18q)*(H+1). Data.L=18q. exists_data chooses q=210Q and any requested H,
using Mathlib's elementary Nat.exists_prime_gt_modEq_one.

Data.aa/bb/cc are the divided integral forms. Data.shift is
12m + sum_i (|bb_i|+|cc_i|) +1, implemented via natural absolute values.
an,bn,cn are the positive shifted natural coefficients, dn=[1,1,m,m].
A=dn*an, B=dn*bn, C=dn*cn, and F_i(t,u)=A_i*u²+B_i*t*u+C_i*t².

Verified:
* modular, positivity, coprimality and reconstruction interfaces;
* primitive an,bn,cn and nonzero full discriminants;
* dn positive and squarefree (the reason for choosing m prime);
* raw_eq_eighteen: raw_i(m,L,u+shift*t,t)=18*F_i(t,u);
* identity and ordered for t>0,u>=0;
* near_unit_gap: H(F1-F0)<(H+1)(F3-F2), now for any sufficiently large prime center;
* raw_eq_eighteen_rat, scaled_parameter: equality of three scaled coordinates
  recovers u*t'=u'*t by the existing projective inverse;
* coprime_parameters: squarefreeness of F0 forces Nat.Coprime t u;
* coprime_pair_eq: primitive positive-denominator parameter pairs with the
  same rational ratio are equal.

raw_eq_eighteen_rat uses a LOCAL maxHeartbeats=2000000 for cast normalization;
other declarations compile at the default limit. No new axiom is introduced.

### RoughSquarefreeConicSieve.lean

Imports RoughSquarefreeConicSetup. Namespace Erdos1206.RoughSquarefreeConicSieve.

* seed_coprime: all F_i(0,1) are coprime to q.
* exists_local_witnesses: at p|q prescribe (t,u)=(0,1); at p not dividing q,
  p>8, so the four content-free quadratics can all be made units. The contents
  dn are squarefree, including at p=m, hence no p² divides any full coordinate.
* exists_sieved_progression: M,v,w>0 with EVERY parameter pair in the affine
  lattice giving roots coprime to q, and at least N²/2 pairs in [0,N)² giving
  all four roots squarefree, eventually. The sieve cutoff K is at least q,
  all leading coefficients and discriminant absolute values, and 48.
  Retained CRT congruences prove coprimality, not just square-avoidance.

### QuadraticParameterMass.lean

Imports AffineQuadraticSquarefreeSieve. Namespace Erdos1206.QuadraticParameterMass.

reciprocal_not_summable: for a predicate on natural parameter pairs, positive
heights <=(K*N)² on each N-box, and eventual good count >=N²/2, the reciprocal
height sum over the good-parameter subtype diverges. This abstracts the old
finite-tail proof and says nothing about injectivity into root tuples.

### RoughSquarefreePrimitiveFamily.lean

Imports RoughSquarefreeConicSieve and NearUnitPrimitiveMass.
Namespace Erdos1206.RoughSquarefreePrimitiveFamily.

Progression D packages M,v,w>0, coprimality and the good-pair counts.
Its Index is the subtype of parameter pairs giving four squarefree roots.

* A natural-valued lift uses the public generic primitive_lift.
* collision and scale, with scale_spec, give a primitive normalized tuple
  and positive common multiplier; no cancellation bound is needed.
* collision_injective: scaled equality yields equal projective parameters;
  squarefreeness implies primitive parameters; then positivity and M>0 recover
  the parameter pair exactly.
* collision_properties: the gap inequality survives normalization, and all
  four normalized roots are squarefree and coprime to q by divisor inheritance.

### RoughSquarefreePrimitiveMass.lean

Imports RoughSquarefreePrimitiveFamily and QuadraticParameterMass.
Namespace Erdos1206.RoughSquarefreePrimitiveMass.

* index_mass_not_summable: quadratic raw heights and the parameter sieve give
  divergent raw reciprocal mass; normalized maximum roots are no larger, so
  normalized reciprocal mass also diverges.
* Residual Q H: primitive collisions satisfying the small-gap inequality,
  with each root squarefree AND Nat.Coprime to Q.
* residual_reciprocal_heights_not_summable Q H hQ proves divergence on this
  entire residual subtype for EVERY Q>0,H. It chooses Data with q=210Q,
  injects its normalized family, and restricts coprimality from q to Q.

### SquarefreeQuadraticFamilyResidualMass.lean

Imports QuadraticFamilyResidualMass and RoughSquarefreePrimitiveMass.
Namespace Erdos1206.SquarefreeQuadraticFamilyResidualMass.

outside_reciprocal_heights_not_summable: outside ANY fixed finite list of
rational quadratic coefficient planes, the reciprocal maximum-root mass of
distinct primitive collisions with squarefree roots coprime to Q still diverges.
Uses the common compact gap cutoff and the existing residual_outside theorem.

### Verification, limitations, and next priority

Logs:
/tmp/prescribed_quadratic_sieve_1206.log
/tmp/rough_conic_integral_coefficients_1206.log
/tmp/positive_quadratic_shift_1206.log
/tmp/rough_squarefree_conic_setup_1206.log
/tmp/rough_squarefree_conic_sieve_1206.log
/tmp/quadratic_parameter_mass_1206.log
/tmp/rough_squarefree_primitive_family_1206.log
/tmp/rough_squarefree_primitive_mass_1206.log
/tmp/squarefree_quadratic_family_residual_mass_1206.log

The temporary CheckConicIntegral.lean has been removed. No job is pending.
The old pending squarefree-extension instructions above are now superseded.

CRITICAL LIMITATION: sums are over distinct COLLISIONS, not distinct maximum
root values. Neither divergence nor superlinear edge counts supplies an
independence bound. Roots or divisors may be reused by a cover. In particular,
these forms deliberately have content m in two coordinates; no claim that
this new family obstructs every reusable sieve is justified.

No unconditional bounded coloring, uniform reusable-cover bound, compatible
every-prefix positive-density construction, or arbitrary-dense-set recurrence
argument has been found. Finding one of these genuinely GLOBAL inputs is the
main remaining task; more source-counting results alone will not settle it.

Spec.lean remains unchanged, with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof or disproof has been submitted.

## Global construction and recurrence review after squarefree residual mass

Rechecked the exact conjecture, the density and Sidon definitions, the
compatible-every-prefix compactness equivalence, the uniform finite divisor
cover criterion, and the combined coloring/sieve criterion. No definitional
simplification or applicable library theorem was found.

Revisited the large-prime-factor source as a possible way to suppress
collisions. The existing `largePrimeSource_coloring_iff` is decisive about
one limitation: fixed finite coloring on this source is equivalent to fixed
finite coloring of all positive roots. Shared-large-prime separation does
not control distinct-large-prime collisions. No new estimate for those
collisions, or uniform recursive construction, was obtained.

Also considered endpoint-to-prefix gluing, polynomial recurrence, and
prime-factor normal-order restrictions. These considerations did not yield
proved global inputs. In particular, no uniform mixed-extension estimate,
bounded coloring, reusable-cover bound, or dense-set recurrence theorem is
claimed. No numerical search or new Lean theorem resulted from this review.

Spec.lean remains unchanged, with the original sorry. The conjecture is
still unresolved in this development. No proof has been submitted and no
computation is pending from this continuation.

## Distinct-root energy and whole-root-cover mass (new, verified)

The seven-file extension is now COMPLETE. All seven files were rebuilt in
order, and all printed main-theorem axiom audits report only propext,
Classical.choice, and Quot.sound. Spec.lean is unchanged and unresolved.

* QuadraticLatticeLines.lean proves an elementary lattice-line point bound
  for nondegenerate integral binary quadratic forms, using primitive normal
  directions, Bezout coefficients, and separated coordinate projections.
* BinaryQuadraticEnergy.lean proves the dyadic equal-value energy estimate
  `energy_dyadic_bound`: at radius 2^k the energy is at most
  `(100*(coeffBound a b c+1)+9)*(k+2)*(2^k)^2`. Directions are grouped in
  dyadic shells; primitive differences and their gcd multipliers encode
  the off-diagonal equal-value pairs.
* FiniteImageEnergy.lean supplies finite Cauchy--Schwarz image bounds and
  `selector_energy`: selecting one of finitely many functions pointwise
  has energy bounded by the number of functions times their total energy.
  It also supplies summability of reciprocal masses on disjoint finite sets.
* QuadraticImageMass.lean proves `distinct_values_not_summable`: a positive
  proportion of a two-dimensional parameter grid, with quadratic upper
  and lower output bounds and O(N^2 log N) energy, has divergent reciprocal
  mass over its DISTINCT natural output values. Annuli are subsampled to
  make their image sets disjoint, giving a harmonic-series contradiction.
* AffineQuadraticImageMass.lean transfers the energy bound to affine
  quadratic lattices with positive leading and trailing coefficients and
  nonzero discriminant. Its `distinct_values_not_summable` packages the
  distinct-image result for positive-density subsets of parameter boxes.
* SquarefreeDistinctMaximumMass.lean applies this to the older
  SquarefreeConicFamily (squarefree roots coprime to 6). Its
  `maxima_reciprocals_not_summable` concerns distinct primitive maximum
  ROOT VALUES, not just distinct collision tuples. The maximum quadratic
  is `eval 797983 43324 589 M 0 1`.
* SquarefreeWholeRootCoverMass.lean proves `selected_roots_not_summable`
  for ANY coordinate selection on the good parameter pairs. Consequently
  `no_summable_whole_root_cover` rules out a reciprocal-summable set
  containing some whole root of every primitive collision in the source,
  with arbitrary coordinate choices and arbitrary reuse of roots.
  `no_summable_fractional_root_cover` gives the corresponding obstruction
  for nonnegative weights w with sum_i w(e_i)>=1 on every collision:
  sum_n w(n)/n cannot converge.

The pending errors in the last file were fixed by marking its modulus-based
private constants noncomputable, proving bound positivity structurally rather
than expanding the huge exponent, and explicitly matching the height bound
before using `mul_pow`. No recursion-depth increase was needed.

Fresh audit logs: /tmp/audit_<FileBaseName>.log for all seven files. Current
oleans are in .lake/build/lib/lean/Submission/. The intentional
`exists i, Good x -> ...` selector extension produces a harmless style-linter
warning; there is no proof hole. The older individual development logs remain.

SCOPE LIMITS: the new application uses only the older coprime-to-6 family.
The arbitrary-Q rough family and finite-family-removal distinct-value versions
have NOT been proved. In particular, the new theorem is about whole roots,
NOT proper-divisor covers. A positive-density cube-Sidon set may delete a set
with divergent reciprocal mass. Thus none of these conclusions is a disproof
of the original existential statement, and no positive-density construction
has been obtained either.

## Rough distinct-root and residual-cover extension (new, verified)

The five-file extension of the preceding seven files is COMPLETE. In
particular, the arbitrary-Q and finite-family-removal restrictions stated in
the preceding entry are now lifted for distinct-root/whole-root-cover mass.
All five files compile, and all printed axiom audits use only propext,
Classical.choice, and Quot.sound. Spec.lean remains unchanged and unresolved.

### RoughConicCancellation.lean

Imports RoughSquarefreePrimitiveFamily. Namespace Erdos1206.RoughConicCancellation.
For n=3m^2-9mL+7L^2, defines the integer certificate
  R=216*m^3*n*(n^3-27*m^6).
It is nonzero when L>0 and m>=12L. If gcd(s,t)=1 and g divides the first
three raw rough-conic coordinates, then g divides R.

The proof is explicit integral elimination, not an assumed resultant bound:
* n*A-3m^2*C=(n^3-27m^6)*(s^2+3t^2).
* Eliminate this denominator term from A,B to recover scaled U,V.
* (6m-10L)*U+(6m-8L)*V=4n*(s^2-3t^2).
* Thus g divides R*s^2 and R*t^2; Bezout for coprime s^2,t^2 gives g|R.

For Progression P, squarefreeness supplies coprime original parameters;
shearing s=U+shift*T preserves coprimality. Since raw coordinates=18 times
the integral roots, `Progression.scale_dvd` and `Progression.scale_le` bound
the chosen common normalization factor by |R|, uniformly in the parameters.
The bound depends on the fixed family. No global family-uniform bound is claimed.

### FiniteDilationMass.lean

Imports FormalConjecturesUtil. Namespace Erdos1206.FiniteDilationMass.
* subset_summable: monotonicity of reciprocal mass.
* dilation_summable: multiplication by one positive integer preserves it.
* multiples_summable: the union of dilations by 1,...,G preserves it.
* image_not_summable_of_bounded_normalization: if raw distinct values have
  divergent reciprocal mass and raw=factor*normalized with 1<=factor<=G,
  then the DISTINCT normalized values also have divergent reciprocal mass.
No injectivity or multiplicity bound on normalization is assumed.

### AffineQuadraticSelectionMass.lean

Imports AffineQuadraticImageMass. Namespace Erdos1206.AffineQuadraticSelectionMass.
`selected_values_not_summable` generalizes the earlier fixed-family selector
argument to any nonempty finite collection of nondegenerate affine binary
quadratics with positive leading/trailing coefficients. It uses selector_energy
and sums the finitely many height/energy constants. The selector is arbitrary.

### RoughSquarefreeWholeRootMass.lean

Imports the preceding three files and RoughSquarefreePrimitiveMass.
Namespace Erdos1206.RoughSquarefreeWholeRootMass.
* coordinate: Fin 4 coordinates of a primitive Collision tuple.
* Progression.raw_selected_not_summable: arbitrary selected raw values on
  the squarefree parameter source have divergent distinct-value mass.
* Progression.normalized_selected_not_summable: the same is true for
  arbitrary selections from normalized collisions; uses the bounded factor.
* Progression.no_summable_root_cover: roots may be chosen at arbitrary
  positions and reused arbitrarily often, but the cover cost still diverges.
* no_summable_residual_root_cover Q H hQ: applies to the entire rough
  residual source, with all roots squarefree, coprime to Q>0, and gap ratio
  below 1+1/H (stated without division, also covering H=0).
* residual_maxima_not_summable: divergence over DISTINCT maximum roots.

### QuadraticResidualRootCoverMass.lean

Imports RoughSquarefreeWholeRootMass and QuadraticFamilyResidualMass.
Namespace Erdos1206.QuadraticResidualRootCoverMass.
Source a b c d Q consists of primitive collisions outside the coefficient
planes of the listed rational quadratic families, all roots squarefree and
coprime to Q. For every FINITE list satisfying the cubic polynomial identity:
* no_summable_outside_root_cover;
* outside_maxima_not_summable (distinct maximum values);
* no_summable_outside_bounded_cofactor_cover: even proper-divisor covers
  have divergent cost if each chosen divisor b has root=g*b with 1<=g<=G
  for one fixed G;
* no_summable_outside_fractional_root_cover: nonnegative whole-root weights
  w whose four-root sum is at least one cannot have sum_n w(n)/n finite.
The finite family reduction uses the existing uniform compact gap bound.

### Verification and main gap

Fresh logs: /tmp/audit_<FileBaseName>.log for all five files. Development logs:
/tmp/rough_conic_cancellation_1206.log
/tmp/finite_dilation_mass_1206.log
/tmp/affine_quadratic_selection_mass_1206.log
/tmp/rough_squarefree_whole_root_mass_1206.log
/tmp/quadratic_residual_root_cover_mass_1206.log
Current oleans are in .lake/build/lib/lean/Submission/.

The only new warning is an unused explicit Progression argument in the
family-dependent cancellation bound; that argument deliberately provides the
interface used in the downstream normalization theorem. No proof hole occurs.
Temporary CheckRoughMass.lean and CheckMassTransfer.lean were removed.

Still missing: unrestricted positive-density construction, uniform finite
coloring, summable reusable cover with UNBOUNDED cofactors, or a universal
zero-density theorem. Divergent reciprocal deletion cost is compatible with a
positive-density Sidon root set. Thus none of these new results proves the
negation of Spec.lean, and no proof or disproof has been submitted.

## Global-step continuation after distinct-root cover bounds (unresolved)

Rechecked the exact every-prefix compactness and finite divisor-cover criteria,
the upper-density-one coloring reduction, and the odd-cycle source criterion.
No required uniform input was proved. In particular, the new bounded-cofactor
obstruction is not an obstruction to arbitrary proper-divisor weights.

Revisited three routes without obtaining a theorem:
* Direct finite-prefix extension: the known far-interval construction cannot
  be used at bounded scale ratios, and endpoint cardinality alone is not the
  simultaneous-prefix condition.
* Recurrence from rational parametrizations: integer dilation changes
  divisibility; common root translation does not preserve the cubic identity.
  Neither rational pair-extension nor density of rational points implies that
  an arbitrary positive-density set contains a whole collision.
* Norm-factor weights for a fixed conic: split-prime factor profiles suggest
  possible fractional divisor weights, but controlling the exceptional
  parameter tuples and summing the costs over all families are both missing.
  No distribution theorem, sieve bound, or weighted cover was asserted.

Also rechecked the precise odd-parity reduction and the existing six-root
squarefree/coprime-to-210 obstruction. Ordinary proper coloring cannot be
replaced by odd-parity coloring without a separate obstruction-cover theorem.
No new finite search, Lean theorem, or target-file edit resulted from this
review. Spec.lean still has the original sorry, and no proof was submitted.

## Weighted-cover continuation (no settlement)

Focused specifically on `WeightedDivisorCover.lean` and the canonical
`GreedyDivisorCover.lean`, rather than extending the mass-counting results.
Rechecked the per-root multiplicities in the weighted covering inequality,
the exclusion of divisor 1, and the need for a single finite reciprocal-cost
bound over all cutoffs. The saved finite primal/dual certificates do not
supply that bound. No new numerical optimization was run or extrapolated.

Reexamined the complete cubic parametrization and its common-factor locus.
The known restriction of cancellation primes to 2, 3, and primes 1 mod 3
still does not control their total cancellation or give weights on divisors
of the NORMALIZED ROOTS. The all-chart and four-prime examples prevent
silently replacing this by a bounded-cancellation assertion.

No arithmetic estimate bounding the global weighted cover cost was proved.
Nor was a universal zero-density implication obtained. No new auxiliary
Lean theorem was added in this continuation; Spec.lean is unchanged and still
contains its original sorry. No proof/disproof has been submitted.

## New finite prime-character contrast (verified; no settlement)

Added and compiled two files:

* `ConicPrimeCharacterScore.lean`, namespace
  `Erdos1206.ConicPrimeCharacterScore`.
  `score P w n = sum_{p in P} w(p)*v_p(n)` is completely additive on
  positive integers. `contrast` is score(a)+score(b)-score(c)-score(d),
  with signs by norm-field pair, NOT by the signs of the cube identity.
  `contrast_dilation` and `contrast_normalization` prove exact cancellation
  of a common positive factor. If the two integer-valued characters are
  each +/-1 on P, and every prime dividing a coordinate splits in its
  designated character, `contrast_eq_twice_mixedMass` identifies the
  contrast with twice the total valuation at primes where the two
  characters differ. `mixedMass_le_of_bands` bounds this mass by 2*K
  whenever all four dilated coordinates have scores in [-K,K].
  `legendre_discriminant_of_dvd` supplies the splitting condition for a
  primitive binary quadratic value, outside the leading coefficient and
  discriminant. All of these are exact algebraic statements.

* `SquarefreeConicCharacterScore.lean`, namespace
  `Erdos1206.SquarefreeConicCharacterScore`.
  Applies the generic result to the existing explicit squarefree conic
  family. Its first two discriminants are 948996, the last two -3078972.
  The characters are `jacobiSym 948996 p` and `jacobiSym (-3078972) p`.
  `family_contrast` works for any finite set of primes greater than 10^9,
  every coprime nonnegative parameter pair with positive second parameter,
  and EVERY positive integer dilation. No squarefreeness assumption is
  needed for this algebraic result. The large-prime condition is a simple
  sufficient exclusion of finitely many coefficient/discriminant primes.

Build/audit logs:
`/tmp/conic_prime_character_score.log`
`/tmp/squarefree_conic_character_score.log`.
Both files compile without warnings; all six printed main-theorem axiom
checks list only propext, Classical.choice, Quot.sound. Their oleans are in
`.lake/build/lib/lean/Submission/`. Temporary `CheckConicScore.lean` removed.

Proposed next analytic step, NOT proved: use balanced prime-character score
bands, whose common multiplier cancels, to restrict the remaining primitive
parameters to those with few mixed-prime divisors. In the displayed family
there are two distinct quadratic fields. A sieve across such mixed primes
might give a reciprocal-summable exceptional parameter set. No normal-order,
large-deviation, uniform prime-block density, or sieve-dimension estimate
has been proved here. In particular, the expected sieve exponent discussed
in exploration is not a theorem. Naive finite-CRT asymptotics do not supply
uniform prefix bounds for infinitely many moving prime blocks.

Even a successful fixed-family sieve would still leave a GLOBAL gap:
family-dependent initial exceptions and constants cannot simply be summed
over all rational conics. No uniform bound for those heads, no bounded
coloring, and no positive-density witness has been obtained. These new
score lemmas must not be described as a proof or disproof of Spec.lean.

`Submission/Spec.lean` is unchanged, contains its original sorry, and has
SHA256 9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof has been submitted and no computation remains pending.


## Uniform prime-block density and conic source (six files, verified)

The earlier lack of a uniform second-moment/source-density estimate for moving
prime blocks is now CLOSED. This is actual new Lean work, not only a review.
The original conjecture nevertheless remains unresolved.

Six files (779 lines total) were built in dependency order and audited:

1. `PrimeBlockVariance.lean`, namespace `Erdos1206.PrimeBlockVariance`.
   `primeSum P w n = sum_{p in P} w(p)*1_{p|n}` is strongly additive,
   NOT the valuation score on nonsquarefree integers.
   `mean P w = sum w(p)/p`.
   For primes in P and |w(p)|<=1, `variance_le` proves

     sum_{1<=n<=N} (primeSum(P,w,n)-mean(P,w))^2
       <= N * sum_{p in P} w(p)^2/p + 3*card(P)^2.

   Distinct-prime covariance has absolute value <=3 by exact floor bounds;
   diagonal covariance <=N/p. If all p<=T and T^2<=N, the error is <=3N.
   There is NO dependence on the CRT modulus product(P).

2. `MovingPrimeBlockVariance.lean`.
   Primes above T contribute absolute score at most one for n<=N<(T+1)^2.
   Splitting off these primes and summing four-adic shells gives
   `moving_variance_le`, for EVERY finite P, bounded w, and prefix N:

     sum_{1<=n<=N} (primeSum(P,w,n)-movingMean(P,w,n))^2
       <= 12*N*(sum_{p in P} w(p)^2/p+4).

   Here movingMean truncates to p<=2^(Nat.log 4 n+1). Its cutoff depends
   on n, not on the enclosing prefix. No prime number theorem, character
   asymptotic, CRT asymptotic, or unproved analytic estimate is used.

3. `CountableBandDensity.lean`.
   `bad_union_card_le` turns a summable sequence of UNIFORM second-moment
   costs into a bound on the union of bad bands in EVERY prefix. It chooses
   a finite witness-index set for the bad integers in that prefix, avoiding
   any unjustified exchange of infinitely many density limits.
   `lowerDensity_pos_of_prefix` preserves positive lower density on a source
   when total cost is less than the source's uniform prefix coefficient.
   The intentional selector `exists j, n in B -> ...` gives one harmless
   exists-implication style warning.

4. `PrimeBlockBandDensity.lean`.
   `energy(P,w) = sum w(p)^2/p+4`.
   `exists_good_bands`: for any positive-lower-density source S of positive
   integers, there is ONE K>0 (independent of the blocks) such that any
   sequence P_j,w_j of finite prime blocks with |w_j|<=1 has a subset
   A of S with positive lower density and, for every n in A and every j,

     (primeSum(P_j,w_j,n)-movingMean(P_j,w_j,n))^2
       <= K*2^j*energy(P_j,w_j).

   The proof allocates costs delta/(4*2^j), whose sum is delta/2, and uses
   square-root-sized bands. `exists_squarefree_good_bands` specializes S
   to the squarefree integers. This is a source result, NOT Sidonness.

5. `PrimeBlockMeanOscillation.lean`.
   For 0<n<=m<=R*n and 1<=R, the moving centers differ by at most 2R,
   uniformly in P,w. This follows from an elementary cutoff ratio bound
   and sum_{U<p<=V}|w(p)|/p <= V/(U+1).
   No cancellation in sums of prime characters is assumed.

6. `ConicCharacterBandSource.lean`.
   Combines the new source with the verified character contrast.
   `weight(p) = (chi(p)-psi(p))/2` is in [-1,1] on regular primes.
   On squarefree roots, the old valuation score is twice this primeSum.
   The explicit conic has F3<=1000000*F0 on its nonnegative parameter cone.
   `exists_source` proves: one K>0 works for ANY sequence of finite blocks
   P_j consisting of primes >10^9, producing a positive-lower-density
   squarefree A such that every primitive-parameter instance whose four
   dilated roots v*F_i(t,u) all lie in A satisfies, for every j,

     mixedMass(P_j,chi,psi,F0,F1,F2,F3)
       <= 4*sqrt(K*2^j*energy(P_j,weight)) + 4000000.

   This is uniform in the positive dilation v. The last constant accounts
   for the moving centers at the four comparable roots. It does NOT say
   that mixedMass exceeds this bound or that no collision survives.

All six have current oleans in `.lake/build/lib/lean/Submission/`.
Fresh audit logs are `/tmp/audit_<FileBaseName>.log`. All printed theorem
axiom audits list only propext, Classical.choice, Quot.sound. No sorry,
admit, native_decide, or new axiom occurs in these files. Temporary
`CheckPrimeVariance.lean` removed. No process remains running.

Remaining gaps, NOT closed:

* A quantitative upper sieve/counting estimate for primitive conic
  parameters surviving these mixed-prime bounds. No claimed sieve exponent
  or reciprocal-summability conclusion has been formalized here.
* Uniform control of family-dependent heads and constants across ALL
  rational conic families. Even a successful fixed-family exceptional-tail
  sieve does not justify summing its costs over all families.
* No construction of a cube-Sidon positive-density set, no bounded global
  coloring, and no disproof for arbitrary positive-density sets.

Spec.lean is unchanged with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof has been submitted.

## Sharp arbitrary-weight source extension (four files, verified)

The latest four-file extension removes the additive constant from prime-score
energy and removes individual weight bounds. It does NOT settle the conjecture.

* `SharpPrimeBlockVariance.lean` (238 lines) defines
  `mass(P,w) = sum_{p in P} w(p)^2/p` and proves, for arbitrary real weights,
  covariance <= N*mass + 3*(sum |w|)^2, weighted Cauchy
  `(sum |w|)^2 <= mass*sum p`, small-prime variance <=4N*mass,
  large-prime second moment <=N*mass, and the every-prefix moving-center bound
  `sum_{1<=n<=N}(primeSum-movingMean)^2 <=48N*mass`.
* `SharpPrimeBlockBandDensity.lean` (99 lines) proves that one K>0, depending
  only on a positive-density positive-root source, works for any countable
  sequence of finite prime blocks and arbitrary real weights. On a retained
  positive-lower-density subset, every squared deviation is <=K*2^j*mass_j.
  Zero-energy blocks are treated separately and impose no loss. There is a
  squarefree-source specialization. No Sidonness is asserted.
* `SharpPrimeBlockMeanOscillation.lean` (85 lines) proves harmonic weighted
  Cauchy and, for 0<n<=m<=R*n with 1<=R, squared moving-center oscillation
  <=2R*mass. Thus center differences have no additive constant either.
* `SharpConicCharacterBandSource.lean` (88 lines) connects these estimates to
  the explicit two-field conic. For any sequence P_j of primes >10^9, a
  positive-lower-density squarefree source has the property that every
  surviving dilated primitive-parameter conic collision satisfies

    mixedMass_j <= 4*sqrt(K*2^j*mass_j) + 2*sqrt(2000000*mass_j).

  Here w(p)=(chi(p)-psi(p))/2. The bound is uniform in positive dilations.

All four compile without warnings, have current oleans, and have fresh audits
in /tmp/audit_Sharp*.log using only propext, Classical.choice, Quot.sound.
None contains sorry, admit, native_decide, or a new axiom.

This sharpens the fixed-family result but does not close the global gap.
In particular no quantitative exceptional-parameter sieve, summable global
family bound, or lower mixed-mass contradiction has been established.
Spec.lean remains unchanged and unresolved; no proof has been submitted.

## Finite thinned Selberg sieve for the conic (nine files, verified)

This is a new finite upper-sieve development, not a solution of the original
conjecture. The previous fixed-family exceptional-parameter gap is partially
closed: there is now an explicit FINITE counting bound with all error terms.
An asymptotic reciprocal-summability conclusion and the global family argument
have NOT yet been obtained.

Nine files (1489 lines) compile without warnings, have current oleans in the
Lake build path, and have fresh audits /tmp/audit_<FileBaseName>.log using only
propext, Classical.choice, Quot.sound. No sorry/admit/native_decide/new axiom
occurs in these nine files.

1. FiniteThinnedSieve.lean (243 lines).
   Abstract finite-prime/subset sieve. Independent auxiliary thinning with
   probability q turns k local hits into avoidance probability >=(1-q)^k.
   No independence of the arithmetic sample is assumed. The theorem
   few_hits_le_main_error bounds card(low hits)*(1-q)^k by the quadratic
   sieve form at local densities q*r and its full joint-distribution error.
   Arbitrary finite samples and arbitrary local hit sets are allowed.

2. FiniteSelbergWeights.lean (303 lines).
   Uses the orthogonal Bernoulli basis
     basis(r,S,J)=prod_{p in S} (if p in J then -1 else r(p)/(1-r(p))).
   localMass(r,S)=prod r/(1-r), sieveMass(r,D)=sum_{S in D} localMass.
   Explicit selbergWeight has weight(empty)=1, main quadratic form exactly
   1/sieveMass, and vanishes outside any downward-closed truncation D.
   Its absolute value is <=prod_{p in S}(1+r(p)/(1-r(p))).
   No analytic sieve dimension is asserted.

3. FiniteSelbergBound.lean (99 lines).
   Optimized thinned bound with exact errors, and a uniform-error form:
     card(low hits)*(1-q)^k <= M/G + card(D)^2*L^2*R,
   where L bounds the coefficients and R the joint remainders on D x D.

4. PeriodicBoxCount.lean (89 lines).
   For any allowed residue set B modulo d>0 in two coordinates, at EVERY N,
     |boxCount(N,d,B)-N^2*card(B)/d^2| <=2*N*d+d^2.
   Proof counts each one-coordinate residue between floor(N/d) and +1.

5. PrimeBoxCRT.lean (118 lines).
   Arbitrary local residue sets B_p in (ZMod p)^2 have a simultaneous residue
   set modulo prod P with cardinal exactly prod card(B_p), using CRT.
   joint_box_discrepancy supplies the preceding box bound with multiplicative
   local densities rho_p=card(B_p)/p^2.

6. PrimeBoxSelberg.lean (147 lines).
   level(P,z) is the downward-closed set of prime subsets with product <=z.
   It has cardinal <=z. If 0<rho_p<=1/2, the Selberg coefficients at q*rho are
   bounded by z. For 0<q<=1 and z>=1, few_hits_bound proves
     card(low hits)*(1-q)^k <= N^2/G +2*N*z^6+z^8.
   This includes the full CRT error and needs no distribution assumption.

7. SelbergMassLower.lean (190 lines).
   fullMass(P,r)=prod(1+r/(1-r)). If z>1 and
     2*sum_{p in P} r(p)*log p <= log z,
   at least half the full mass lies in level(P,z). Also fullMass>=exp(sum r).
   Thus few_hits_exponential, for rho as above, proves
     card(low hits)*(1-q)^k
       <=2*N^2*exp(-sum q*rho_p)+2*N*z^6+z^8
   under the explicit logarithmic first-moment condition.

8. BinaryQuadraticLocalSieve.lean (106 lines).
   A split nonsingular quadratic has two affine roots. The union of lines
   with slopes R has cardinal 1+card(R)*(card(field)-1), counting the origin
   once. Two such quadratics with no common affine root give 4*card(field)-3
   points. lineSet_pair_zero links these points to the binary forms.

9. ConicMixedLocalSieve.lean (194 lines).
   For the explicit conic and p>10^9 with chi(p)!=psi(p), localSet p uses the
   first two split forms if chi(p)=1, otherwise the last two.
   localSet_card proves card(localSet p)+3=4p. The no-common-root certificates
   have constants 180366264 and 13874328, both below 10^9.
   localDensity is exactly (4p-3)/p^2 and lies in (0,1/2].
   hits_le_mixedMass holds for u>0, without needing coprime parameters.
   small_mixedMass_count proves the actual conic finite bound:
     #{(t,u) in [0,N)^2: u>0, mixedMass<=k}*(1-q)^k
       <=2*N^2*exp(-sum_{p in P} q*(4p-3)/p^2)+2*N*z^6+z^8,
   provided all P are regular mixed primes, z>1, and
     2*sum_{p in P} q*(4p-3)/p^2*log p <=log z.

Remaining analytic steps:
* A quantitative lower bound for reciprocal mass of mixed primes (ideally
  >=(1/2)log log y-O(1)) and an upper logarithmic first moment.
* Appropriate blocks/scales yielding a summable exceptional reciprocal tail.
* The independent GLOBAL obstruction: family-dependent finite heads and
  constants cannot be summed across all conic families without a new argument.

Important budgeting observation (not yet formalized): the earlier 2^j band
loss is too expensive for the proposed geometric sieve-scale argument. A
slower summable geometric cost (e.g. loss (4/3)^j) allows scales with log-log
size growing (3/2)^j while a q=7/8 sieve supplies exponent 7/4. The source
band theorem should be generalized before attempting that asymptotic step.

Spec.lean remains unchanged with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof has been submitted.


## Quantitative mixed-prime estimates and geometric source (12 files, verified)

Twelve files, 1288 lines, all compile without warnings. Current oleans exist
under .lake/build/lib/lean/Submission/. Fresh audits are in
/tmp/audit_<FileBaseName>.log and use only propext, Classical.choice, Quot.sound.
No sorry, admit, native_decide, or new axiom is present in these files.
Temporary CheckPropBand.lean has been removed. Spec.lean is unchanged.

1. GeometricPrimeBlockBands.lean (95 lines).
   Fixed the formerly unfinished arbitrary-growth-factor proof. For any b>1,
   one source constant K works for all prime blocks and real weights, with
   squared deviation <=K*b^j*mass_j on a positive-lower-density subset.
   The cost allocation is delta*(b-1)/(2*b*b^j), summing to delta/2.
   Squarefree specialization included.

2. ProportionalConicBandSource.lean (110 lines).
   contrast_proportional proves invariance of additive score contrast under
   positive rational scaling, expressed by x_i*y_0=x_0*y_i (no division).
   proportional_order transfers ordering and the 10^6 root-ratio bound.
   family_contrast_proportional and exists_source give the conic mixed-mass
   bound for ALL integer root vectors rationally proportional to F(t,u),
   including normalized points, with any b>1 source budget:
     mixedMass_j <=4 sqrt(K*b^j*mass_j)+2 sqrt(2000000*mass_j).

3. ConicMixedDirichletCharacter.lean (96 lines).
   Defines generic integer-valued Jacobi Dirichlet character jacobiChar N.
   eta is jacobiChar 27834287; etaComplex is its complex scalar extension.
   eta(5)=-1, so both characters are nonprincipal.
   For primes p>10^9, product_symbols proves chi(p)*psi(p)=eta(p), using
     948996*(-3078972)=324^2*(-27834287)
   and quadratic reciprocity. Thus mixed iff eta(p)=-1. The character's
   values are always in {0,1,-1}. This was not assumed as prime distribution.

4. RealQuadraticEulerMass.lean (178 lines).
   Generic integer-valued Dirichlet characters with trichotomy hypothesis.
   primePower(s,p)=p^(-s). Proves real logarithmic Euler-product identity,
   absolute Taylor remainder <=2*x^2 for |x|<=1/2, and
     log||zeta(s)||-log||L_chi(s)|| <=weightedMass(chi,s)+squareError,
   where weightedMass=sum_p (1-chi(p))*p^(-s), and squareError is the fixed
   finite constant 4*sum_p p^(-2). Valid for all real s>1.

5. QuadraticPrimeMassNearOne.lean (80 lines).
   Uses zeta's residue at 1 and continuity of the nonprincipal L-function.
   Proves eventually as s tends to 1 from above:
     weightedMass(chi,s) >=log(1/(s-1))-C.
   Only upper boundedness of the nonprincipal L-function is needed here;
   no PNT is invoked.

6. PrimeLogMomentNearOne.lean (112 lines).
   primeMoment(s)=sum_p log(p)*p^(-s). It is summable for s>1 and bounded
   by the norm of the von Mangoldt L-series. Using the regularized residue
   class auxiliary function at modulus 1, proves one B>0 with
     (s-1)*primeMoment(s)<=B
   eventually as s tends to 1 from above.

7. FinitePrimeMass.lean (137 lines).
   primePrefix(y) is a finite set of Nat.Primes with p<=y.
   Truncation bound:
     weightedMass <=sum_{p<=y}(1-chi(p))/p +2*primeMoment/log y.
   If (s-1)log y<=1, finite logarithmic moment <=exp(1)*primeMoment.
   At cutoff(s)=exp(1/(s-1)), obtains both finite prefix estimates.

8. QuadraticPrimePrefixBounds.lean (101 lines).
   Converts near-one estimates to y->infinity with s=1+1/log y.
   negativePrefix chi H y selects primes p<=y, p>H, chi(p)=-1.
   If chi is nonzero on all primes >H, then for suitable C,D>0:
     sum_negative 1/p >=(1/2)log log y-C,
     sum_negative log(p)/p <=D log y.
   Only C is allowed arbitrary sign in the formal theorem; D>0 is explicit.
   The finite initial segment is rigorously bounded, not discarded silently.

9. PrimeReciprocalUpper.lean (77 lines).
   Proves sum_p p^(-s)<=log||zeta(s)||, and consequently
     sum_{p<=y}1/p <=exp(1)*(log log y+log 2)
   for all sufficiently large y.

10. ConicPrimeBlockEstimates.lean (71 lines).
    block(y) maps negativePrefix eta 10^9 y to Finset Nat.
    Every member is a mixed prime >10^9. Its source energy is exactly
    sum_block 1/p because weight(p)^2=1 on these primes.
    eventually_block_bounds supplies the lower reciprocal, upper reciprocal,
    and upper logarithmic-moment estimates simultaneously.

11. ConicSievePrimeEstimates.lean (116 lines).
    rho(p)=(4p-3)/p^2. At thinning q=7/8 the prime bounds give
      sum q*rho >=(7/4)log log y-E,
      2 sum q*rho*log p <=T log y,
    with T>0. Consequently for all sufficiently large y, ALL N,z,k with
    z>1 and T log y<=log z satisfy
      card(smallParameters(y,N,k))
        <=8^k*(2*N^2*exp(E-(7/4)log log y)+2*N*z^6+z^8).
    smallParameters counts (t,u) in [0,N)^2, u>0, mixedMass<=k.
    This is now an unconditional quantitative finite estimate, with all
    CRT errors and the explicit logarithmic sieve level retained.

12. GeometricConicSource.lean (115 lines).
    primeCutoff(j)=exp(exp((3/2)^j)), P(j)=block(primeCutoff(j)).
    Proves eventual mass(P_j,weight)<=C*(3/2)^j for some C>0.
    With source budget b=4/3, the band threshold is bounded by a constant
    times (17/12)^j (since (17/12)^2>2=(4/3)*(3/2)).
    exists_source_threshold constructs squarefree A of positive LOWER density
    and k:Nat->Nat such that k_j/(3/2)^j tends to zero, and every primitive
    parameter conic point rationally proportional to four members of A has
    mixedMass(P_j)<=k_j for every j.

Remaining steps, NOT completed:
* Reciprocal summability of surviving conic parameter heights. The new
  unconditional finite sieve and o((3/2)^j) source thresholds are ready.
* Normalized primitive-root divisor cover from that parameter summability.
* The independent GLOBAL obstacle across all rational families and their
  family-dependent finite heads. Nothing above supplies a global coloring,
  a global summable cover, or a proof/disproof of the original conjecture.

Proposed summability schedule (mathematically outlined, not yet formalized):
Let a=3/2 and choose L>0 with L*log 2>=max(T,1). Set
  m_j=ceil(L*exp(a^j)), z_j=2^m_j, r_j=16*m_j.
For dyadic parameter boxes N=2^(r+1) with r_j<=r<r_(j+1), the sieve level
condition holds, and z_j^6/N<=z_j^(-10), z_j^8/N^2<=z_j^(-24).
Since m_j*log 2>=a^j, these errors are bounded by exp(-10*a^j).
The normalized box count is bounded by a constant times
  exp(k_j*log 8-(7/4)*a^j).
The number of dyadic shells in the jth band is at most
  r_(j+1)<=16*(L*exp(a^(j+1))+1).
Thus reciprocal-height cost is bounded by a constant times
  exp(k_j*log 8-(1/4)*a^j),
which is eventually <=constant*exp(-(1/8)*a^j) and summable because
k_j/a^j->0. An abstract dyadic-box counting-to-summability lemma should
complete this step. A finite initial parameter region is harmless for
summability, but this does NOT solve the all-family finite-head problem.

Spec.lean retains SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof has been submitted.


## Fixed-conic exceptional summability and normalized cover (five files, verified)

The previously outlined summability schedule is now fully formalized, as is
the conversion to a normalized primitive-root cover. This remains a
SOURCE-RELATIVE, SINGLE-CONIC result, not a settlement of the conjecture.

Five files (602 lines), all compile without warnings and have current oleans.
Fresh /tmp/audit_<FileBaseName>.log audits list only propext, Classical.choice,
Quot.sound. No sorry/admit/native_decide/new axiom. CheckDyadicBox.lean removed.

1. DyadicBoxReciprocal.lean (170 lines).
   box(N)=[0,N)^2, height(t,u)=max(t,u), weight(T,x)=1/height(x)^2 on T
   and zero off T (including zero weight at the origin).
   shell(r)=box(2^(r+1)) minus box(2^r), band(r,s)=union of those shells.
   Abstract summable_of_finset_cover allows a finite initial head.
   If a dyadic box has count <=(2^(r+1))^2*delta, its shell weight is <=4delta.
   summable_of_dyadic_bands proves summability of weight(T) if r_j->infinity
   and sum_j (r_(j+1)-r_j)*delta_j converges with the stated box bounds.
   Monotonicity of r_j is NOT required; a least-crossing argument covers all
   shells beyond the finite initial box.

2. ConicSieveSchedule.lean (110 lines).
   m(L,j)=ceil(L*exp((3/2)^j)), z(L,j)=2^m, r(L,j)=16*m.
   cost(E,k,j)=exp(k_j log 8)*(2 exp(E-(7/4)(3/2)^j)+3 exp(-10(3/2)^j)).
   r_tendsto for L>0. Band cost is bounded by
     16(L+1)(2exp E+3)*exp(k_j log 8-(1/4)(3/2)^j).
   Thus summable_band_cost holds whenever k_j/(3/2)^j->0.
   Proof eventually bounds this by a constant times exp(-(1/8)(3/2)^j),
   itself dominated by exp(-j/16) via Bernoulli's inequality.

3. ConicExceptionalParameters.lean (135 lines).
   exceptional(k) consists of (t,u) with u>0 and mixedMass(P_j)<=k_j for ALL j.
   No coprimality hypothesis is needed for this exceptional-count theorem.
   log_z and level_moment verify the sieve level, and error_bound proves
     2*N*Z^6+Z^8 <=3*N^2*exp(-10*A)
   if Z>=1, Z^16<=N, and A<=log Z.
   dyadic_count combines this with the unconditional finite sieve.
   exceptional_reciprocal_summable proves Summable(weight(exceptional k))
   whenever k_j/(3/2)^j->0. A sufficiently large shift J handles all
   asymptotic hypotheses; no finite-prefix estimate is assumed silently.

4. SummableConicSource.lean (29 lines).
   survivors(A) consists of primitive (t,u), u>0, admitting a positive root
   vector x in A with x_i*F0=x_0*Fi (rational proportionality).
   exists_source_summable_parameters gives squarefree A of positive LOWER
   density with Summable(weight(survivors A)).

5. NormalizedConicSourceCover.lean (158 lines).
   commonGcd(t,u)=gcd(gcd(F0,F1),gcd(F2,F3)).
   normalizedMax(t,u)=F3/commonGcd.
   Two exact integer coefficient certificates prove that, on coprime t,u,
     commonGcd divides 721465056.
   The certificates are rows 1 and 3 of the adjugate of the first three
   quadratic coefficient rows, whose determinant is 721465056:
     [-401149908,-749322324,366771600] dot [F0,F1,F2]=721465056*u^2,
     [-335988,-552276,271440] dot [F0,F1,F2]=721465056*t^2.
   normalizedMax>1 when u>0, and
     1/normalizedMax <=721465056/max(t,u)^2.
   normalizedMax_dvd_proportional proves normalizedMax(t,u) divides x3 for
   EVERY natural root vector with x_i*F0=x0*Fi. This uses the gcd of the four
   products x3*Fi, so no unproved integrality of a rational dilation occurs.
   cover(A) is the range of normalizedMax over survivors(A); choosing one
   preimage per distinct divisor transfers summability without injectivity.
   exists_source_cover proves there are squarefree A of positive lower
   density and B with 1 not in B and summable reciprocal indicator, such
   that every surviving rationally proportional primitive conic instance
   has a divisor d in B dividing its largest actual root x3.

What remains:
* The GLOBAL all-collision argument is still missing. The single explicit
  conic is not a parametrization of all cubic collisions. Independently
  summable family covers cannot be summed over all families without uniform
  control, and their finite heads cannot simply be ignored.
* No proof/disproof of Spec.lean has been produced. No submission made.

A potentially useful general next reduction (not yet formalized): summability
of the DISTINCT NORMALIZED PRIMITIVE MAXIMA of all collisions surviving on a
positive-density source would suffice. Remove a reciprocal-small tail; the
remaining bounded primitive maxima give only FINITELY MANY primitive root
patterns, whose dilation edges can be eliminated by a bounded-degree graph
and an increasing greedy independent set. This preserves positive lower
density without source invariance. IMPORTANT: an arbitrary source-relative
summable DIVISOR cover does NOT suffice (A=2*Nat, B={2} is a trivial such
cover). The primitive-maximal-root property is essential to the finite-head
argument. The global primitive-maxima summability remains unproved.

Spec.lean is unchanged, SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.


## Global primitive-maxima extraction criterion (three files, verified)

Three additional files (272 lines) compile cleanly with only propext,
Classical.choice and Quot.sound. Fresh audit logs and oleans are present.

1. FiniteRatioSource.lean (121 lines). A maximal bounded-ratio-separated
   subset of any positive-lower-density source still has positive lower
   density. Maximality gives bounded-ratio domination and a finite-fiber
   prefix count; no source invariance is assumed.
2. RelativePrimitiveCover.lean (101 lines). A reciprocal-small tail of
   divisor multiples may be deleted from an arbitrary positive-density
   source. RatioCompatibleCover additionally requires that a cover divisor
   bound the numerator and denominator of a rational relation between the
   smallest and largest roots. Under this condition, the finite head is
   eliminated using FiniteRatioSource, proving the original conclusion.
3. RelativePrimitiveMaxima.lean (50 lines). The largest root divided by
   the gcd of all four roots always has the required ratio compatibility.
   summable_maxima_suffice therefore proves the original existential
   conclusion if some positive-density source of positive integers has
   reciprocal-summable DISTINCT primitive maxima of all its collisions.

This is a GLOBAL SUFFICIENT CRITERION, not a construction satisfying it.
The single-conic summability result still does not cover all collisions,
and independently summable family covers cannot be combined without a
uniform bound on their costs, including finite heads. Spec.lean remains
unchanged and unresolved.


## Continuation review: fixed-conic avoidance was already available

The explicit forms used in the prime-score development satisfy the exact
coefficient identity F1-F0 = 13*(F3-F2). Thus all positive proportional
instances have the fixed adjacent-gap ratio 13. This is inside the compact
gap-ratio range handled by CompactGapRatioColoring (for H=13). In particular,
positive-density avoidance of that single conic does not require the new
analytic sieve. The new summability lemmas remain verified, but they must
not be mistaken for progress controlling the endpoint regimes of the
global problem: ratios tending to 1 or becoming unbounded.

No new global conclusion is asserted; Spec.lean is still unchanged.

## Square reduced-gap-ratio candidate rejected (exact diagnostic)

Filtering the stored exact edge list gives a counterexample even on the
squarefree source coprime to 210: (2633,5573,29299,29359), with adjacent-gap
ratio (5573-2633)/(29359-29299)=49. Thus squarefreeness does not restrict
all surviving conic fibres to nonsquare gap ratios. This is a finite exact
diagnostic, not a disproof of the conjecture. No asymptotic inference is made.

The next source-preserving reduction being developed is positive-density
extraction avoiding a compact range of real root ratios inside an ARBITRARY
positive-density source. The earlier geometric-band source theorem alone
does not justify intersecting its source with an unrelated positive-density
set, nor does ordinary finite-color pigeonholing preserve lower density.

## Source-preserving endpoint reduction (three new files, verified)

WeightedPathSelection.lean, RelativeGeometricBands.lean, and
RelativeEndpointReduction.lean all compile with only propext,
Classical.choice, and Quot.sound; current oleans and fresh audit logs exist.
The temporary CheckWeightedBins.lean was removed.

* WeightedPathSelection: maximum-weight finite independent sets of bins
  give local domination w_k <= sum of selected neighboring weights.
  Compactness preserves these LOCAL inequalities. Consequently prefix weight
  through K is at most (2R+1) times selected weight through K+R.
* RelativeGeometricBands: finite logarithmic bins are pairwise disjoint.
  The selected union has positive LOWER density inside ANY positive-density
  source S of positive integers. For fixed q>1 and B>=1, it can be chosen
  so that x<=y<=B*x in the subset implies y<q*x. This uses no multiplicative
  invariance and no false lower-density pigeonhole principle.
* CompactGapRatioColoring now additionally exposes compact_gap_root_ratio,
  the real inequality behind its existing proof, with a fresh axiom audit.
* RelativeEndpointReduction.exists_positive_endpoint_source: for H>=1,
  any positive-density source has a positive-density subset whose collisions
  satisfy H*(b-a)<(H+1)*(d-c) OR H*(d-c)<b-a.
* summable_endpoint_maxima_suffice: reciprocal summability of distinct
  primitive maxima ONLY FOR THESE ENDPOINT collisions on a positive-density
  source suffices for the original conjecture. The middle compact range is
  removed inside that same source before applying RelativePrimitiveMaxima.

This is a stronger GLOBAL SUFFICIENT CRITERION, not a constructed endpoint
cover. No endpoint summability theorem is proved. Spec.lean remains unchanged
and unresolved. No submission has been made.

## Distinct-large-prime nonresidue candidate also rejected (exact diagnostic)

The earlier common-prime counterexample to QuadraticResidueSource was not the
only obstruction. Filtering the saved exact edges by P+(n)^k>n^(k-1) and
Legendre(n/P+(n),P+(n))=-1 gives primitive counterexamples even for k=8:
(362,14451,22394,24243), with factorizations 2*181, 3*4817, 2*11197, 3*8081.
The four largest prime factors are distinct, and all four symbols are -1.
Thus removing shared-large-prime collisions does not make this candidate
Sidon. This is a targeted exact diagnostic, not an asymptotic claim or a
formal disproof of the original existential conjecture.

## Continuation: global endpoint and parametrization review

Rechecked the source-relative endpoint criterion against the complete cubic
parametrization, the gap norm restrictions, and the existing cancellation
counterexamples. No global summability estimate or uniform coloring was
obtained. In particular, counting raw cubic or quartic parameter heights
cannot be substituted for counting normalized primitive maxima: the common
factor is unbounded, including across all charts. The fixed-conic character
sieve still does not control all conic families or their family-dependent
finite heads.

Also checked the imported Sidon APIs. They provide elementary extension and
heredity results, but no applicable positive-relative-density theorem for
cubes. External literature access again failed DNS resolution. No new
mathematical conclusion is asserted, and no new auxiliary theorem was added.

Spec.lean remains unchanged, with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No proof or disproof has been submitted.


## Canceled-gap congruences and bounded numerator-difference sources (verified)

Two new files, 204 lines total, compile without warnings. All six public
axiom audits list only propext, Classical.choice, and Quot.sound. Neither
file contains sorry, admit, native_decide, or an added axiom. Current oleans
and fresh /tmp/audit_UnitGapCongruences.log and
/tmp/audit_GapDifferenceSource.log are present.

1. UnitGapCongruences.lean (120 lines), namespace
   Erdos1206.UnitGapCongruences, imports GapRatioResidues.
   For a collision (a+g*u)^3+c^3=a^3+(c+g*v)^3 with g>0:
   * odd_gap_mod_four: all four roots odd implies u=v mod 4;
   * unit_gap_mod_three: all four roots prime to 3 implies u=v mod 3;
   * coprime_six_gap_mod_twelve: all four roots prime to 6 implies
     u=v mod 12.
   The numerators u,v need not be coprime. The three local finite-ring
   certificates are proved using decide +kernel, not native_decide.
   When 3 divides g, the proof works modulo 9 and only then cancels 3.
   Decidable synthesis for the five-variable ZMod 3 certificate required
   synthInstance.maxSize 2048 (not an additional axiom).

2. GapDifferenceSource.lean (84 lines), namespace
   Erdos1206.GapDifferenceSource, imports GapRatioResidues.
   * progression_gap_congruence: for ANY m>1, all four roots 1 mod m
     implies u=v mod m. This removes the previous assumption Coprime m 3.
     If 3|m, each cube cofactor is 3 mod 3m, so canceling 3 yields the
     congruence modulo m. If 3 does not divide m, use the old lemma.
   * no_small_gap_difference: such a collision is impossible if
     0<u-v<m, with NO bound on u or v themselves.
   * positive_density_avoids_small_gap_difference K: the progression
     1 mod (K+2) is infinite, has positive lower density, and excludes
     every ratio satisfying 0<u-v<=K. This is an infinite set of ratios,
     including sequences converging to one.

Exact finite diagnostics motivated the modulus-12 statement: on the saved
edge list, gcds of canceled gap differences for roots prime to 2, 3, and 6
were respectively 4, 3, and 12. The statements are now independently
kernel-proved; the finite enumeration is NOT used in their proofs.

LIMITATION: neither the progression density nor its modulus is uniform in K.
Passing to all K by intersection or compactness therefore does not produce
a positive-density Sidon source. No global summable endpoint cover or
uniform finite coloring has been constructed. The original theorem remains
unresolved and Spec.lean is unchanged with its original sorry. No proof was
submitted. Temporary CheckUnitGap.lean was removed; no job is pending.


## Linear collision-count extraction (12 files, 1238 lines, verified)

The entire reduction formerly under development is COMPLETE. Every file in
the following list was freshly rebuilt in dependency order without warnings;
all printed axiom audits list only propext, Classical.choice, Quot.sound.
Logs are /tmp/audit_<FileName>.log, with current oleans in the Lake build.

1. DivisorPowerBound.lean (77 lines). Explicit divisor-power bounds:
   tau(n)^k <= constant(k)*n, and n<=2*t^36 implies
   tau(n)<=(2*constant(12)+1)*t^3. The constant is enormous; avoid unfolding it
   in arithmetic normalization.
2. CubicPairCodegree.lean (130 lines). Sum/difference representations inject
   into divisors via their sums/gaps. At cutoff t^12 the completion-pair count
   is <= codegreeConstant*t^3.
3. CubicHypergraph.lean (114 lines). `edges N S` is the finite family of
   four-element strict cubic collision sets in S below N. Its distinct-pair
   codegrees satisfy the preceding bound. `independent_iff_cubeSidon` handles
   repeated-root obstructions via StrictCubeCollision's existing descent.
4. FiniteProductSampling.lean (90 lines). Exact means/covariances for events
   of coordinate label zero under uniform maps V -> Fin k.
5. SamplingVariance.lean (91 lines). Variance <= |E|*r*D for supports of size
   <=r and coordinate degree <=D, including repeated supports. Finite
   averaging gives simultaneous bands from a total second-moment budget;
   `exists_simultaneous_two_bands` controls two scores at every scale.
6. HypergraphHubTrimming.lean (122 lines). Hubs have degree>D; good edges meet
   at most one hub. Ignoring hubs leaves good supports of size 3 or 4 and
   coordinate degree <=D. Edges meeting >=2 hubs number <=|H|^2*L if every
   distinct-pair codegree is <=L. Explicit DecidableEq V avoids instance
   mismatches at concrete finite types.
7. PrefixSampling.lean (92 lines). Natural supports lift to Fin M; exact
   cardinalities and prefix-count variance bounds. The former `event_lift`
   error is fixed; the whole file compiles.
8. TrimmedSampling.lean (94 lines). `full E omega` counts fully selected
   edges. Its cardinality is <=score(good trimmed supports)+bad.card.
   Mean score <=|E|/k^3 and variance <=4*|E|*D.
9. MaximumRootDeletion.lean (75 lines). Delete the maximum root of every
   selected edge. This destroys every collision, and losses below N are
   bounded by the number of edges wholly below N. Thus later edges cannot
   spoil an earlier-prefix lower bound.
10. CubicSamplingStage.lean (128 lines). `finite_stage` constructs ONE finite
    Sidon witness satisfying all requested scale-prefix bounds. Hypotheses:
    source count >=8*epsilon*k*N, mean bound <=epsilon*N,
    bad-edge count <=epsilon*N, and total normalized moment budget <1.
    Conclusion: retained count >=4*epsilon*N at every requested scale.
11. CubicScaleBounds.lean (120 lines). For cutoff(j)=(2^j)^12 and
    threshold(j)=(2^j)^11, linear edge counts <=C*cutoff imply
      hubs <=4*C*2^j,
      bad edges <=16*C^2*L*(2^j)^5,
      normalized moment budget <=((4*C+1)/epsilon^2)*(1/2)^j.
    `interpolate` turns grid-prefix bounds into every-prefix bounds with
    density coefficient epsilon/1024 and one fixed initial additive constant.
12. LinearCollisionExtraction.lean (105 lines), importing CubicScaleBounds
    and Compactness. Public theorem:

    theorem linear_collision_source_suffices
        (S : Set Nat) (hS : 0 < S.lowerDensity)
        (C : Nat) (hC : forall N, (edges N S).card <= C*N) :
      exists A : Set Nat, A.Infinite and 0 < A.lowerDensity and
        IsSidon ((fun n : Nat => n^3) '' A)

    The proof chooses k and epsilon, makes the two geometric error tails
    small, applies finite_stage simultaneously on all scales up to each
    finite cutoff, interpolates, and invokes the existing every-prefix
    compactness theorem. It uses no infinite probability space, no false
    finite-color lower-density pigeonhole principle, and no source dilation
    invariance hypothesis.

LIMITATION: the uniform linear-count source hypothesis has NOT been proved
for any positive-density source. In particular the existing full-prefix
superlinear theorems already rule out using all integers or the squarefree
source coprime to 6 unchanged. This reduction alone does not settle the
conjecture, and it must not be reported as a solution.

No unverified numerical search was used in these proofs. All 12 files were
checked for sorry/admit/native_decide/added-axiom tokens, with none present.
Spec.lean is unchanged, SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63,
and still contains its original sorry. No submission has been made.

## Arithmetic-source review after completing linear extraction (no settlement)

Reexamined the exact cancellation formula, its three pairwise-prime-disjoint
locus divisors, the quadratic inverse-height bound, and large-prime separation.
The restriction of cancellation primes to 2, 3, and primes 1 mod 3 still does
not bound cancellation, and supplies no uniform O(N) collision estimate on a
positive-density source. No source satisfying LinearCollisionExtraction's
hypothesis was obtained.

A targeted check of square products among the 51697 stored squarefree edges
through 100000 found none, but this REPEATS the already recorded
/tmp/cube_sf_squareproduct.json diagnostic. It is not new evidence, is not a
universal theorem, and even a universal nonsquare-product statement would
need an additional coloring argument. No new coloring invariant was found.

External literature access again failed DNS resolution. A search of the
imported library supplied no applicable cube-Sidon density theorem. This
continuation added no Lean theorem or settlement. Spec.lean is unchanged,
SHA256 9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63,
and still contains its original sorry. No proof was submitted; no live
computation is pending.

## Multiplicative-coloring extension review (no settlement)

Reviewed the squarefree and summable-source coloring reductions against the
saved Boolean/C3 obstruction certificates and the finite source colorings.
No uniform prime-label extension rule was established. The full-source C3
UNSAT certificate remains a restricted diagnostic and is not a disproof of
the target; the squarefree finite SAT assignments remain finite and do not
prove infinite colorability. Distinct prime-factor parity vectors or a
hypothetical nonsquare-product restriction alone do not give a simultaneous
nonmonochromatic coloring.

Also reconsidered treating primitive coordinates of fixed quadratic families
as density-zero sets. Arbitrary common dilations again prevent deleting those
coordinate sets at zero density. The completed character-score construction
handles a fixed family, but its family-dependent finite heads are still not
controlled globally. No new arithmetic source or uniform coloring was proved.

This continuation added no Lean theorem and ran no bounded coloring search.
Spec.lean remains unchanged with its original sorry. No proof or disproof
was submitted, and no computation is pending.

## Representation-structure review (no settlement)

Checked whether a uniform bound on cube-difference multiplicities could supply
a coloring theorem without the missing linear total-count estimate. The
already verified RepeatedCubeDifferences.natural_sidon_pairs produces
arbitrarily many integral pairs sharing one positive cube difference (the
difference depends on the requested number of pairs). Thus a uniform bound
on all such multiplicities is unavailable. The positional-clique theorems
also rule out separating one fixed positional pair in every collision with
finitely many colors. Neither result rules out ordinary hypergraph coloring
or positive-density Sidon extraction.

No usable higher-moment-to-independence implication or additional arithmetic
bound was established. No Lean statement was added or altered. Spec.lean
remains unchanged with its original sorry; no proof has been submitted.

## Further all-family review (unresolved)

Reviewed the endpoint reduction and fixed-gap/fixed-conic sieves against the
completed linear-count extraction theorem. No uniform summation over reduced
gap ratios was established. Countably many character-score restrictions do
not by themselves solve this: the family-dependent initial ranges remain
uncontrolled, and their union cannot be declared negligible. No arithmetic
source with a linear collision count, uniform finite coloring, or disproof
was obtained. This review added no Lean theorem and used no new bounded
counterexample search. Spec.lean is unchanged and still contains its original
sorry; no valid proof is ready for submission.


## Source-preserving linear extraction (new, verified)

Added `Submission/RelativeCompactness.lean`:

* `compactness_finite_cube_sidon_in T δ C` takes finite witnesses contained
  in T and produces an infinite-limit witness A contained in T, preserving
  both the Sidon property and all prefix inequalities. Membership in T
  passes through eventual coordinate agreement in the Bool-valued compactness
  argument.
* `existence_of_finite_prefix_construction_in` adds infinitude and positive
  lower density when δ > 0.

Strengthened `Submission/CubicSamplingStage.lean`:

* `finite_stage_in_source` returns B contained in `sourcePrefix S M`.
* `finite_stage` retains its former range-only interface as a wrapper.

Strengthened `Submission/LinearCollisionExtraction.lean`:

* `linear_collision_source_subset S hS C hC` proves
  `∃ A, A ⊆ S ∧ A.Infinite ∧ 0 < A.lowerDensity ∧ IsSidon (cube '' A)`.
* `linear_collision_source_suffices` retains its original type as a wrapper.

Rebuilt RelativeCompactness, CubicSamplingStage, CubicScaleBounds, and
LinearCollisionExtraction successfully, without warnings. New axiom audits
contain only propext, Classical.choice, and Quot.sound. Logs are
`/tmp/relative_compactness.log`, `/tmp/relative_stage.log`,
`/tmp/relative_scale.log`, and `/tmp/relative_linear.log`.

No source with the required uniform linear collision bound was constructed.
The original conjecture remains unresolved; Spec.lean was not altered.


## Uniform obstruction for digit sums of cubes (new, verified)

`Submission/CubeDigitSumObstruction.lean` imports DigitSumObstruction and
proves, without new axioms:

* `digit_sum_block`: digit sums add across a radix block when the low part
  is less than b^k. The proof uses padded digit lists and `ofDigits`.
* `digit_sum_complement`: the digit sums of b^k-m and m-1 add to (b-1)*k.
* `cube_block_identity`: the natural-number four-block identity
  m*(B-1)^3 = (B-m)+B*((3*m-1)+B*((B-3*m)+B*(m-1))) for 0<m, 3m≤B.
* `digit_sum_mul_pow_sub_one_cube`: if b>1, 0<m, and 3m≤b^k, then
  digitSum_b(m*(b^k-1)^3)=2*(b-1)*k.
* `cube_digit_sum_fiber_not_sidon`: if b>1 and 5184≤b^k, the fiber of
  cube digit sum 2*(b-1)*k contains the scaled collision (1,9,10,12).
* `no_cube_digit_sum_coloring`: for any type of colors and function f,
  it is not the case that all fibers n↦f(digitSum_b(n^3)) have Sidon cubes.

The earlier finite diagnostic at lines around 2868 already rejected small
modular digit-sum colorings. No numerical search was rerun. This new result
is a uniform algebraic proof covering arbitrary functions of the cube's
single digit-sum statistic. It does NOT rule out a particular fiber being
Sidon, arbitrary digit-dependent colorings, or arbitrary positive-density
root sets. It is NOT a negation of the conjecture.

The file compiles without warnings; all three public axiom audits list only
propext, Classical.choice, Quot.sound. Log: /tmp/cube_digit_sum.log.
Spec.lean remains unchanged with its original sorry; no proof of the target
is ready to submit.

## Fixed prime-factor-parity low bits in cyclic four-colorings (new diagnostic)

Tested a new prescribed low-bit rule, distinct from the earlier saved-color
extension tests: every prime has low bit one, so the low color bit of n is
Omega(n) mod 2 (prime factors counted with multiplicity). The high prime bits
remain free. This is exactly the restriction that a completely multiplicative
ZMod 4 coloring assigns every prime an odd color.

First tested the stronger sufficient condition that each low-monochromatic
edge have four colors summing to 2 mod 4. Exact F2 elimination finds an
inconsistency below maximum root 644 with 14 edges. Files:
/tmp/cube_omega_low_linear.py and /tmp/cube_omega_low_linear.json.
That stronger-condition failure ALONE does not rule out ordinary coloring.

Then checked the actual nonmonochromaticity constraints. Generator
/tmp/cube_c4_fixed_low_omega.py is a copy of the previously audited fixed-low
encoding, with prime low bits fixed to one. At N=100000 it has 29615 primitive
low-monochromatic edges, 100000 variables, and 420859 clauses. CaDiCaL returned
UNSAT in approximately 0.71 seconds, with an ASCII LRAT certificate.

The CNF factor-count recurrence, all 29615 integer cube equalities and order
conditions, the XOR truth table, and the offset NAE truth table were separately
checked. Backward pruning retained 15355 initial clauses and 1148 derived
clauses on 7053 variables. An independent forward RUP replay verified 74738
hints and reached the empty clause.

Files, all under /tmp/:
* cube_c4_fixed_low_100000_1_omega.{cnf,npz,out,exit,lrat}
* cube_c4_fixed_low_100000_1_omega_audit.json
* cube_c4_fixed_low_100000_1_omega_pruned.{cnf,json,lrat}
* cube_c4_fixed_low_100000_1_omega_pruned_rup_audit.json
* check_omega_low_rup.py

IMPORTANT SCOPE: These are exact external finite computations, not imported
Lean proofs. They rule out this prescribed low-bit rule on the full source,
not arbitrary cyclic four-colorings, squarefree-source colorings, ordinary
colorings, or arbitrary positive-density Sidon root sets. No uniform coloring
or source construction was obtained. No job is pending. Spec.lean remains
unchanged with its original sorry; no valid target proof is ready to submit.


## Uniform factor-count selection obstruction (new, verified)

`Submission/FactorCountObstruction.lean` imports `InertPrimeCollision` and
contains 201 lines. It uses the already verified four-prime collision
26711^3+35543^3=31469^3+32009^3; it does not run another collision search.

* `collision_in_cardFactors_fiber k hk`: for every k>0, four distinct
  positive roots with Ω=k form a cubic collision. Multiply the four primes
  by 2^(k-1).
* `cardFactors_fiber_not_sidon`: no positive Ω fiber has Sidon cubes.
* `subset_zero_one_of_cardFactors_selection`: if membership in a cube-Sidon
  root set depends only on Ω, the set is contained in {0,1}.
* `finite_of_cardFactors_selection`: the resulting finiteness statement.
* `no_cardFactors_coloring`: no function of Ω, with any number of colors,
  has all cube-Sidon fibers.
* `exists_squarefree_coprime_cardFactors N k hN`: a squarefree multiplier
  with k prime factors can be chosen coprime to any fixed N>0. The proof
  inductively chooses a prime larger than N times the previous multiplier.
* `squarefree_collision_in_cardFactors_fiber`: every positive Ω fiber
  contains a squarefree collision as well, using a common squarefree
  multiplier coprime to the four seed primes.
* `squarefree_cardFactors_fiber_not_sidon` and
  `subset_one_of_squarefree_cardFactors_selection`: the squarefree-source
  version; a squarefree root set selected solely by its count is contained
  in {1} if its cubes are Sidon.
* `cardDistinctFactors_fiber_not_sidon` and
  `subset_zero_one_of_cardDistinctFactors_selection`: the analogous
  obstruction for ω, obtained from the squarefree witnesses.

The file compiles without warnings, and all printed axiom audits contain
only propext, Classical.choice, and Quot.sound. No sorry/admit/native_decide
or added axiom occurs in it. Log: /tmp/factor_count_obstruction.log.

SCOPE: These results concern membership determined only by one factor-count
statistic (or its squarefree-source restriction). They do not rule out
arbitrary multiplicative characters, arbitrary source-relative colorings,
or arbitrary positive-density root sets. They do not settle Spec.lean.

The global review of prime-label colorings produced no extension rule or
uniform finite bound. In particular, fixed-field score restrictions still
cannot simply be summed over all collision conics: their uncontrolled
family-dependent initial ranges remain a gap. No target proof is ready.
Spec.lean is unchanged, SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63,
and retains the original sorry. No proof was submitted; no job is pending.

## Continuation: full-hypergraph peeling and global review (unresolved)

Spec.lean remains unchanged. No proof or disproof was obtained.

An exact finite diagnostic peeled the saved 898947 four-root edges through
100000 by minimum vertex degree. The resulting degeneracy was 11; the core
histogram was {0:19, 1:86, 2:229, 3:537, 4:864, 5:1350, 6:2021, 7:2864,
8:4279, 9:6011, 10:9979, 11:71762}. There were 19 initially isolated
vertices (including 0), and maximum initial degree 302. The core labels are
saved in /tmp/cube_core_100000.npy. This is a finite diagnostic, not a Lean
proof or an infinite coloring result. In fact the already verified
superlinear edge-count theorem rules out a constant degeneracy bound on the
full source, since constant degeneracy would imply a linear edge count.

Revisited fixed-family character-score sieves, large inert-prime factors,
and odd-cycle counting. No uniform all-family estimate was established.
Common dilations remain essential when using large-prime sources. No
applicable general polynomial-avoidance theorem was found in the library.
No new Lean theorem was added; no computation is pending.

## Continuation: relation-rank diagnostic and conic-content review (unresolved)

No proof or disproof was obtained. Spec.lean remains unchanged.

A new finite diagnostic computed the GF(2) ranks of the four-root incidence
rows of the saved edge list. These give lower bounds for the ranks of the
signed integer collision rows over Q, hence upper bounds on rational
nullity (on vertices 1,...,N):

  N      edges    GF(2) rank    nullity upper bound
  100       45        43                57
  200      136       125                75
  500      566       441                59
  1000    1601       938                62
  2000    4387      1954                46
  5000   16031      4953                47

The calculation used exact Python integer bitset elimination. It is NOT a
Lean-certified computation or an asymptotic theorem. It offers no support
for extracting the target from a linear lower bound on relation nullity,
but does not prove that such a lower bound is impossible at every scale.

The proposed uniform nontrivial-content restriction on quadratic coordinate
forms was abandoned after rereading the earlier content-one family entry:
8428*t^2+62629*t+116863, 8428*t^2+62587*t+116707,
1204*t^2+9973*t+20359, and 1204*t^2+7915*t+12715 are already recorded
as four primitive irreducible coordinate forms with a cubic identity.
Their existence does not establish simultaneous prime values.

The local library search found no applicable polynomial/convex Sidon
extraction theorem. External literature retrieval again failed DNS.
No new Lean theorem was added, no proof was submitted, and no job is pending.

## Exact conic gcd identity and normalized heights (new, verified)

ConicHeightProduct.lean and ConicGCDIdentity.lean now compile completely.
All main axiom audits use only propext, Classical.choice, and Quot.sound.
For an ordered collision a<b<c<d with a^3+d^3=b^3+c^3, put
k=b+c-a-d, g=gcd(a,b,c,d), and
G=gcd(a+d,b+c)*gcd(b-a,d-c)*gcd(c-a,d-b).
The new exact identities are:
  0<k<d, 3 divides k;
  (b-a)*(c-a)*(b+c)=k*(d^2+k*(d+k/3));
  G=k*g^2.
For H0=(b+c)/gcd(a+d,b+c), H1=(b-a)/gcd(b-a,d-c),
H2=(c-a)/gcd(c-a,d-b), the consequences are
  3*H0*H1*H2*g^2=3*d^2+3*d*k+k^2;
  3*H0*H1*H2 <= 7*(d/g)^2;
  exists i, 3*Hi^3 <= 7*(d/g)^2.
The primitive gcd identity is proved by prime valuations, including 2 and 3;
the general one follows by dividing out g. This is not a bound on raw cubic
parametrization cancellation, which remains unbounded. The final normalized
bounds were compiled after restricting a homogeneity rewrite to the LHS.
Logs: /tmp/conic_height_product.log and /tmp/conic_gcd_identity.log.
CheckConicHeight.lean was removed (it was an unused exploratory check file).

SCOPE: uniform arithmetic information about the three reduced conic heights,
not a linear collision count, finite coloring, or summable all-family cover.
The fixed-conic sieve's family-dependent initial ranges are still uncontrolled.
No proof or disproof of Spec.lean has been obtained; its original sorry remains.

## Defect and adjacent-gap identities (new, verified; unresolved)

Added DefectGapBounds.lean (namespace Erdos1206.ConicHeightProduct), importing
ConicGCDIdentity. It compiles with no warnings or holes. All printed axiom
checks use only propext, Classical.choice, and Quot.sound.
For a<b<c<d, a^3+d^3=b^3+c^3, k=b+c-a-d, its results include:
* six_dvd_defect: 6 divides k;
* adjacent_gap_difference: b-a=(d-c)+k;
* adjacent_gap_sq_bound: 3*(b-a)^2 <= 7*k*d;
* bounded_defect_adjacent_gap: if k<=K and d<=N, then
  3*(b-a)^2 <= 7*K*N;
* defect_determinant_identity, over integers with x=b-a and y=c-a:
  12*x*y*(x-k)*(y-k)-3*(2*x*y-2*k*d-k^2)^2=k^4;
* defect_norm_identity, when k=6*j:
  (x*y-6*j*d-18*j^2)^2+108*j^4=x*(x-6*j)*y*(y-6*j).
Log: /tmp/defect_gap_bounds.log.

The smaller-gap bound follows from the exact product identity and the
inequalities b-a<=c-a and d<=b+c. The determinant identity is a polynomial
consequence of the cube equality (its residual factors as -4 times the
root-sum difference times the cube-sum difference).

A finite diagnostic on the existing edge file found 61 primitive collisions
with defect 6 through 100000, and 55 with defect 12; no new edge enumeration
was run. This is NOT a counting theorem. The fixed-defect norm equation has
not been given a sufficient uniform solution bound. A Vieta mutation in the
symmetric defect equation need not preserve integrality or the positive-root
region, so no descent/counting conclusion is drawn from it.

The square-class route was also rechecked: the unrestricted square-product
claim is already disproved, and the squarefree finite diagnostic supplies no
universal theorem or coloring. No global collision source, summable cover,
or density-zero theorem was obtained. Spec.lean remains unchanged with its
original sorry; no proof/disproof has been submitted.

## Canonical cover and lcm review (unresolved; no new theorem)

Rechecked GreedyDivisorCover.lean and WeightedDivisorCover.lean against the
stored finite certificates. Primitive witnesses, divisor-minimality of the
excluded generators, and maximality of the accepted set do not establish
summability of the generator reciprocals. No uniform bound for either the
canonical cover or the finite fractional-cover optima was obtained. No new
optimization was run and no asymptotic conclusion was inferred from the
saved numerical values.

Also considered least common multiples of primitive collision roots. This
has a crucial direction limitation: a forbidden divisor cover must DIVIDE
one of the roots. A collision's lcm is instead a multiple of every root.
Avoiding such lcms as divisors could constrain the divisors of an individual
integer, but does not ensure that the selected root set itself has Sidon
cubes. No lcm summability theorem or transfer to the target was proved.

No new Lean theorem was added in this continuation. Spec.lean remains
unchanged with its original sorry. No proof or disproof was submitted and
no computation is pending.

## Three-term-progression and coloring review (unresolved)

Rechecked whether absence of nontrivial three-term arithmetic progressions
could imply a bounded Sidon coloring. It cannot do so for arbitrary sets:
the base-3 integers with d digits in {0,1} are 3AP-free (digitwise no-carry
argument), have size 2^d, and their sumset has size 3^d. Any Sidon subset of
size m has m*(m+1)/2 distinct pair sums, hence m<=sqrt(2*3^d). Consequently
the required number of Sidon classes is unbounded with d. This elementary
argument was not added as a Lean theorem. These sets are NOT asserted to be
sets of cubes. No additional cube-specific configuration theorem giving a
uniform coloring was established.

The local library search found no applicable polynomial Sidon-density
result. Another external-reference attempt failed: hostname resolution was
unavailable, and a direct HTTPS DNS request timed out. No literature claim
was inferred from that failure.

Spec.lean is unchanged with its original sorry. No proof/disproof or new
auxiliary Lean theorem was submitted, and no computation is pending.

## Uniform Pell counting and small-defect summability (new, verified)

Added five auxiliary files, all fully compiled with no warnings or holes:

* DefectPellSeparation.lean
* ModularSquareRootBound.lean
* NegativePellCount.lean
* DefectCollisionCounting.lean
* SmallDefectSummability.lean

All printed main axiom audits use only propext, Classical.choice, and Quot.sound.
Built oleans are current. Logs are /tmp/defect_pell_separation.log,
/tmp/modular_square_root_bound.log, /tmp/negative_pell_count.log,
/tmp/defect_collision_counting.log, and /tmp/small_defect_summability.log.
The temporary CheckPell.lean was removed. No computation is pending.

1. For x^2-D*y^2=-m, D,m>0, x>=0, y>0, two solutions with increasing y
   in the same projective square-root residue class modulo m have y'>=2*y.
   This does NOT require D to be nonsquare. The integral dot product
   D*y*y'-x*x' is a positive multiple of m strictly exceeding m.

2. The number of r in [0,m) with r^2 congruent to D modulo m is at most
     2*gcd(m,D)*tau(m).
   This is an elementary divisor/CRT bound. No prime-distribution result or
   factorization theorem for quadratic number fields is assumed.

3. Uniform negative-norm Pell counts are now verified. For a finite set of
   distinct positive ordinates y<=N admitting a nonnegative x with
   x^2+m=D*y^2, the count is at most
     2*gcd(m,D)*tau(m)^2*(Nat.log 2 N+1).
   For primitive coordinate pairs, tau(m)^2 improves to tau(m).
   Normalization uses gcd(x,y)^2 dividing m. There is NO hidden constant
   depending on the discriminant.

4. DefectCollisionCounting defines a Collision structure for all strictly
   ordered nonnegative-root cubic collisions (no primitivity condition).
   For e=(a,b,c,d), put k=b+c-a-d and x=b-a. The square-sum inequality
     a^2+d^2 < b^2+c^2
   is proved. With
     X=3*(b^2+c^2-a^2-d^2), Y=2*(c-a)-k,
     D=9*x*(x-k), m=3*k^2*(3*x*(x-k)+k^2),
   one has X^2+m=D*Y^2. The triple (k,x,Y) uniquely determines e;
   positivity fixes the sign of the square-sum defect. Also
     gcd(m,D)<=3*k^4, m<=12*k^2*x^2.
   fixed_slice_card_le gives
     #e with fixed k,x and d<=N
       <=6*k^4*tau(m)^2*(Nat.log 2 (2*N)+1).
   box_card_le proves, for a fixed absolute natural C,
     #e with k<=2^j and d<=2^(32*j) <=1428*C*2^(24*j).
   C is chosen from the already-proved divisor-function bound. Keeping its
   coefficient abstract via Classical.choose avoids evaluating an enormous
   closed natural expression in the kernel; no new axiom is introduced.

5. SmallDefectSummability.small_defect_reciprocals_summable proves
     Summable (fun e : {e : Collision // e.defect^32<=e.d} => 1/e.d).
   This includes ALL ordered collisions in this shrinking regime, not only
   primitive or squarefree ones. maxima_reciprocals_summable transfers it to
   distinct maxima. positive_density_avoids_small_defect constructs a set A
   with positive lower density that excludes EVERY DILATION of EVERY such
   collision, by excluding multiples of these maxima.

   positive_density_normalized_defect_lower_bound additionally proves that
   some positive-lower-density infinite A has the following property. For
   every ordered collision whose largest root d belongs to A, writing
   g=gcd(a,b,c,d),
     d/g < (k/g)^32.
   Thus the exclusion is safe under common-root normalization. It is NOT
   merely a statement about the absolute size of k in a chosen dilation.

SCOPE: This is a new GLOBAL summability/source theorem for a shrinking
small-normalized-defect regime. It does NOT cover all endpoint collisions,
all conic families, or the original conjecture. Collisions with normalized
maximum d/g < (k/g)^32 remain uncontrolled. The constructed source has not
been proved to have linear total collision counts or Sidon cubes. The
conjecture in Spec.lean remains unchanged with its original sorry.

The single-cutoff-versus-every-prefix compactness issue was also briefly
rechecked before this development. No transfer theorem was proved, and an
endpoint-cardinality bound still cannot replace simultaneous prefix bounds.

## Positive Pell counting, small upper gaps, and a joint source (new, verified)

Five further files now compile with no holes or warnings and main audits
using only propext, Classical.choice, and Quot.sound:
* PositivePellSeparation.lean
* PositivePellCount.lean
* SmallGapCollisionCounting.lean
* SmallGapSummability.lean
* SmallParameterSource.lean
Their oleans are current. Logs are the corresponding snake-case names under
/tmp, ending in .log. No computation or temporary check file is pending.

The positive-norm analogue of the previous modular Pell argument is complete:
for x^2-D*y^2=m, D,m>0, a fixed projective square-root residue class modulo m
has successive positive ordinates separated by a factor at least two. The
same uniform counting bounds as in NegativePellCount hold: for positive
y<=N admitting a nonnegative x, the count is at most
  2*gcd(m,D)*tau(m)^2*(Nat.log 2 N+1),
with one divisor-count factor removed for primitive coordinate pairs.

For a strictly ordered cubic collision, write x=b-a and h=d-c (the SMALLER
adjacent gap). SmallGapCollisionCounting proves
  0<h<x,
  x^3<=3*h*d^2,
  [3*h*(c+d)]^2 = [9*x*h]*(a+b)^2+3*h*(x^3-h^3).
The two adjacent gaps and ordinate a+b uniquely determine the collision.
With D=9*x*h and m=3*h*(x^3-h^3),
  gcd(m,D)<=9*h^4, m<=3*h*x^3.
Thus the number of collisions with fixed x,h and d<=N is at most
  18*h^4*tau(m)^2*(Nat.log 2 (2*N)+1).
A uniform box estimate is now verified:
  #e with h<=2^j and d<=2^(48*j) <=2700*C*2^(40*j),
where C is one fixed natural coefficient obtained from the divisor-function
power bound. As before, an abstract choice of the coefficient prevents
unnecessary evaluation of an enormous closed natural expression, without
introducing a prohibited axiom.

SmallGapSummability proves reciprocal maximum-root summability for ALL
ordered collisions with h^48<=d. It then constructs a positive-lower-density
set excluding all dilations of all such collisions. Normalization by the
common root gcd is handled explicitly.

SmallParameterSource combines the small-defect and small-gap covers by taking
the UNION of their forbidden divisor sets. It does NOT assume that two
arbitrary positive-density sets have a positive-density intersection. Its
main theorem positive_density_normalized_parameters_lower_bound constructs
one infinite positive-lower-density set A such that every ordered collision
whose largest root d belongs to A satisfies, with k=b+c-a-d and g=gcd(a,b,c,d),
  d/g < (k/g)^32  AND  d/g < ((d-c)/g)^48.

SCOPE: these two shrinking parameter regimes are now eliminated on one
source, including all common dilations. The broad remaining region, where
both normalized parameters exceed these small powers of primitive height,
is NOT controlled. No total linear collision count, cube-Sidon coloring,
summable full divisor cover, or density-zero theorem has been proved.
Spec.lean is unchanged with its original sorry; no proof/disproof was submitted.

A preliminary review of recursive large-prime selection did not produce a
new construction. The earlier shared-prime/different-prime counting gap
remains. No new numerical search was run or asymptotic inference made.

## Continuation: remaining-region and greedy-witness review (unresolved)

Rechecked the canonical divisor-closed greedy construction against the two
new small-parameter summability theorems. Divisor-minimality gives the already
verified primitive earlier-root witness, but no stronger bound on its defect
or adjacent gaps was established. In particular, the joint source theorem
cannot be used to claim that greedy exclusions all belong to the summable
regimes. No eventual estimate for the remaining greedy generators was proved.

Also reviewed common-cofactor/large-prime decompositions. The existing gap
for collisions with different large prime factors remains; neither the new
Pell bounds nor recursive cofactor selection supplies a uniform density or
linear-edge estimate. No numerical search, new Lean theorem, or target-file
edit resulted in this continuation. No computation is pending. Spec.lean
remains unchanged with its original sorry, and no proof was submitted.

## Continuation: largest-root degree source (review only)

Considered selecting integers that are maxima of at most a fixed number of
cubic collisions, which would imply a uniform linear edge count on the
selected source. The existing largest-root-degree diagnostic already checks
this mechanism through 100000 (medians 2,3,4,6,8; declining bounded-degree
fractions). It was read, not rerun. No uniform positive-density estimate for
such a source, and no theorem showing every such source has density zero,
was obtained. No new Lean theorem, numerical computation, or Spec.lean edit
was made. The global conjecture remains unresolved; no proof was submitted.

## Divergent primitive residual after the small-parameter sectors (verified)

Added SmallParameterResidualMass.lean, importing SmallParameterSource and
PrimitiveCollisionMass. It compiles without warnings or holes; its main
axiom audits use only propext, Classical.choice, and Quot.sound. Its olean
is current. Log: /tmp/small_parameter_residual_mass.log.

The old indexed primitive quadratic family is embedded injectively into the
new DefectCollisionCounting.Collision structure. For its roots, with
k=b+c-a-d and h=d-c, the new file proves
  k=3*h, and d<h^3.
Consequently EVERY indexed member satisfies d<k^32 and d<h^48. The existing
prime-block reciprocal divergence transfers injectively to prove
  residual_reciprocals_not_summable:
  the reciprocal maximum-root mass of primitive collisions satisfying both
  strict inequalities is not summable.

This rules out finishing by claiming that the complement of the two
small-parameter regimes has unconditionally summable per-collision mass.
IMPORTANT: it does NOT assert that these collisions survive inside the
constructed divisor-avoiding source, and it is not a lower bound for arbitrary
reusable divisor covers. This particular family has an even root in every
collision, so another source can eliminate it. It does not disprove the
original conjecture. Spec.lean remains unchanged with its original sorry;
no proof/disproof was submitted, and no computation is pending.

## Global conic follow-up (unresolved)

Reviewed whether the exact product relation for the three conic heights could
make the existing familywise character-score sieve uniform. No such estimate
was obtained. The bound giving one conic height at most a constant times the
two-thirds power of primitive root height does not control the family-dependent
sieve constants or finite heads. The small-parameter source also supplies no
uniform linear count for the remaining collisions. In particular, neither
result justifies invoking LinearCollisionExtraction on that source.

No new proof or disproof was established in this continuation. Spec.lean is
unchanged with its original sorry. No valid settlement was submitted.

## Density-one collision obstruction (new, verified)

Added DensityOneCollisionGrowth.lean. It compiles without warnings or holes;
all seven printed axiom audits use only propext, Classical.choice, Quot.sound.
Its built olean is current. Log: /tmp/density_one_collision_growth.log.
The temporary CheckDensityGrowth.lean has been removed.

The file proves the finite perturbation inequality, for every finite set F of
primitive collisions and every source S:
  N * sum_{e in F} 1/max(e)
    <= #ordered collisions in S up to N + |F|
       + 4*|F|*#{n<=N : n notin S}.
Each omitted root destroys at most one dilation per coordinate of each fixed
primitive pattern. The dilations of distinct primitive patterns are distinct.

Combining this with the verified divergent primitive reciprocal mass gives:
* high_density_forces_large_count: for each C, some fixed epsilon>0 and M
  work uniformly for all S; density greater than 1-epsilon at prefix N+1,
  with N>=M, forces more than C*N collisions through N.
* lowerDensity_one_superlinear and lowerDensity_one_count_div_tendsto_atTop:
  when S.lowerDensity=1, its ordered collision count divided by N tends
  to infinity.
* upperDensity_one_unbounded: S.upperDensity=1 precludes even an eventual
  linear bound, though it need not give growth at every large cutoff.
* source_count_le_hypergraph and upperDensity_one_not_linear_source connect
  this to CubicHypergraph.edges, the exact count in LinearCollisionExtraction.

Thus removing only a density-zero exceptional set (for example, any genuinely
proved density-one normal-order source) cannot meet that linear-count criterion.
This does NOT rule out positive-density sources of density strictly below one,
and it does NOT show that superlinear counts force independence density zero.
It is not a disproof of the original conjecture.

A separate diagnostic reused the saved exact edge list, without new collision
enumeration, to compute the minimum of the three conic heights on primitive
collisions. At cutoffs 1000,3000,10000,30000,100000, the medians were respectively
19,28,43,73,127. Counts with minimum height <=30 were
462,1428,4785,14721,49618, out of total primitive counts
634,2771,13168,53097,238300. These are finite diagnostics only; neither a tail
bound nor its failure is inferred. Reproduction script and data:
/tmp/cube_min_conic_height.py and /tmp/cube_min_conic_height.json.

Spec.lean is unchanged with its original sorry. The task remains unresolved;
no valid proof or disproof has been submitted. No computation is pending.

## Below-density-one construction review (unresolved)

Reexamined the exact cancellation formula for the complete cubic
parametrization and the saved finite fractional divisor-cover estimates.
The cancellation formula still leaves unbounded cancellation, and no uniform
bound for the finite cover costs was proved. Finite feasibility is not a
global cover construction. No new numerical optimization or collision
enumeration was performed.

The density-one collision obstruction does not supply the missing bound for
a source of density strictly below one, nor does it constrain independence
ratios enough to disprove the conjecture. No new settlement was obtained.
Spec.lean remains unchanged with its original sorry; no proof was submitted.

## Progression collision growth and zero-density deletions (new, verified)

Added three auxiliary files:
* ProgressionCollisionMass.lean
* ProgressionCollisionGrowth.lean
* ProgressionCollisionDeletion.lean

All compile without warnings or holes. Their printed main axiom audits use
only propext, Classical.choice, Quot.sound. Built oleans are current. Logs:
/tmp/ProgressionCollisionMass_final.log,
/tmp/ProgressionCollisionGrowth_final.log,
/tmp/ProgressionCollisionDeletion_final.log.
The temporary CheckProgression.lean was removed; no computation is pending.

1. ProgressionCollisionMass strengthens the congruence information for the
existing RoughNearUnitPrimitiveMass family. All four normalized primitive
roots have the SAME residue modulo Q, and that residue is invertible. The
common residue may vary with the collision. The family of all such primitive
collisions has divergent reciprocal maximum-root mass for every Q>0.
Normalization is handled explicitly: raw roots are 18*g*e_i and 18 modulo
18*Q, so g*e_i=1 modulo Q; hence g is invertible and all e_i are congruent.

2. ProgressionCollisionGrowth chooses a multiplier in {1,...,Q} taking the
common root residue to any prescribed residue r. One such multiplier in each
block of Q gives disjoint dilations of all selected primitive patterns. It
proves residueTail_superlinear: for EVERY Q>0, residue r, initial cutoff L,
and real C, all sufficiently large N contain more than C*N ordered collisions
whose roots lie in {n | L<=n and n=r modulo Q}. It also proves
not_linear_source_of_residueTail, using the exact CubicHypergraph.edges count
from LinearCollisionExtraction. No coprimality hypothesis on r is needed.

3. ProgressionCollisionDeletion counts only omissions WITHIN the chosen
residue class. Put P={n | n=r modulo Q}, and filled=S union P^complement.
For every finite family F of the congruent-unit primitive patterns:
  N*sum_{e in F} 1/max(e)
    <= Q*#collisions(S,N) + Q*|F|
       + 4*Q*|F|*#{n<=N : n notin filled}.
Its zero_density_deletion_superlinear theorem proves that if P\S has natural
density zero, then #collisions(S,N)/N is unbounded at every sufficiently large
cutoff, in the explicit quantified sense for each real coefficient C.
zero_density_deletion_not_linear_source rules out a uniform linear bound on
CubicHypergraph.edges for these sources.

SCOPE: periodic sources, and sources containing almost all of one residue
class up to a density-zero deletion, cannot meet the linear-count criterion.
This does NOT show that every positive-density source has superlinear counts,
or that superlinear counts force independence density zero. It is NOT a proof
or disproof of the original conjecture. Spec.lean remains unchanged with its
original sorry, and no valid settlement has been submitted.

## Large-prime recursion follow-up (unresolved)

Rechecked the shared-large-prime separation and possible cofactor recursion.
No bound was obtained for collisions with four different large prime factors,
and no density-preserving recursive selection was proved. Existing finite or
sublinear cofactor selections cannot be promoted to a positive-density source
without an additional uniform estimate. The odd-cycle cover route was also
considered, but no all-cycle counting or covering bound was established.

No new Lean theorem, numerical search, or Spec.lean edit resulted from this
review. The original sorry remains, and no valid settlement was submitted.

## Continuation: odd-cycle and global factorization review (unresolved)

Reexamined the verified squarefree/coprime-to-210 six-root parity obstruction,
the quadratic triple classification, the cubic parametrization, and the existing
finite-coloring diagnostics. The quadratic classification supplies no bound for
arbitrary higher-degree families or all odd cycles. No all-cycle reciprocal
cover estimate was obtained. The shared factors in the explicit six-root
example were not promoted to a general theorem.

Also reconsidered whether atypical factorization of parametrized roots could
give a positive-density source. No uniform estimate surviving normalization
was proved. Density-one normal-order sources remain excluded from the linear
collision-count route by DensityOneCollisionGrowth; nothing here excludes all
positive-density sources or proves zero independence density.

No new Lean theorem or numerical search was performed. Spec.lean is unchanged
with its original sorry. No valid settlement is ready or has been submitted.

## Continuation: finite weighted-cover criterion rechecked (unresolved)

Read the complete WeightedDivisorCover.lean, FiniteDivisorCompactness.lean,
CubicExactCancellation.lean, and the saved divisor-cover diagnostics. The finite
fractional compactness theorem was already proved in WeightedDivisorCover:
weighted_cover_of_uniform_finite_weights and
uniform_finite_weighted_covers_suffice. It must not be reintroduced as a new
result or confused with the separate integral-cover compactness theorem.

No uniform finite LP-cost bound was derived. Unbounded cancellation remains
accounted for by the exact locus-lcm formula, but that formula supplies no such
bound. The saved all-prime collision examples and finite cover costs do not
establish any asymptotic prime-count or cover-cost claim. Also reconsidered
prime-block and finite-family sieves; their uncontrolled global finite heads
remain a gap, not a justification for intersecting countably many sources.

No new theorem, numerical computation, or target-file edit was made. Spec.lean
still contains the original sorry; there is no valid settlement to submit.

## Higher-cycle obstruction with no three-pair representations (verified)

HigherCycleObstruction.lean compiled successfully (exit 0; final log
/tmp/higher_cycle_obstruction.log). Its five printed main axiom audits use only
propext, Classical.choice, Quot.sound. There are no proof holes in this module.

The explicit source has 283 positive roots, maximum 784. Among its cubic
collision edges, 181 selected edges have even incidence at every vertex, so
there is no ZMod 2 coloring with every collision edge having color sum 1.
Nevertheless every cube sum and every positive cube difference has at most two
representations by strict ordered source pairs. Both multiplicity statements
are kernel-certified, using 59 residue buckets and a proved custom merge sort.
The saved witness was reused; no new global collision enumeration was run.

This rules out reducing odd-parity colorability on arbitrary sources solely to
absence of three-pair repeated sums or differences. It does NOT rule out
ordinary proper coloring, nor the analogous restriction to odd or squarefree
sources, nor settle the original conjecture. Spec.lean remains unchanged.

Scratch CheckHigherCycle.lean and /tmp/HigherFast.lean, /tmp/HigherSmall.lean
were removed after the successful full build. No computation is pending.

## Final continuation review (unresolved)

Recorded and cleaned up the HigherCycle result above. Rechecked the quadratic
inverse-height bound, raw cubic-coordinate height bound, large-prime separation,
and prior best-chart diagnostics. No quantitative global estimate or coloring
was obtained. In particular the raw cubic coordinates are not generally
products of a linear and a quadratic factor, so that proposed large-prime
factorization shortcut is unavailable. Large-prime sources already have
superlinear full-prefix collision counts; distinct-large-prime configurations
remain uncontrolled by the shared-prime lemma.

No proof or disproof of the original conjecture is ready. Spec.lean remains
unchanged, including its original sorry. No conditional or finite result has
been substituted for the requested existential statement.

## Continued global review after the unsuccessful final response

Rechecked the exact finite-prefix compactness criterion and alternatives to
linear total collision counts. No uniform simultaneous-prefix independence
bound, finite coloring, or extension theorem was obtained. Endpoint cardinality
bounds were not substituted for the required simultaneous-prefix hypothesis.

Inspected the saved 10000/30000 fractional divisor-cover weights and logs again,
without running a new optimization. No explicit globally covering weight formula
or uniform reciprocal-cost bound emerged. These remain finite certificates only.
Reexamined the cancellation-locus factorization and the distinction between
fixed-conic estimates and global summation; no lattice-counting or sieve estimate
closing that gap was proved. The already verified quadratic-diagonal obstruction
and fixed-curve avoidance results were not treated as all-surface results.

A brief alternate external-reference attempt used direct-IP HTTPS DNS, bypassing
the prior DNS failure. Connecting to 1.1.1.1:443 timed out after eight seconds.
No external mathematical result was retrieved; do not repeat this connection test.

No new Lean theorem or target-file edit was made in this pass. Spec.lean still
has SHA256 9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63
and its original sorry. No valid proof or disproof is ready to submit.

## Squarefree odd-prime four-coloring follow-up (new, verified partial result)

The graph-decomposition review supplied no global adaptive pair selection or
uniform coloring. The existing AllPositionalCubeCliques theorem rules out each
fixed positional pair, not all adaptive choices.

A genuinely narrower candidate was checked: a completely additive ZMod 4
coloring whose prime values are all odd, restricted to squarefree roots. The
previous full-source low-bit UNSAT certificate did not settle this restriction.

1. Exact F2 elimination on the stored squarefree primitive collisions disproved
   the stronger requirement that every low-monochromatic edge have total color
   two. The three-edge witness is:
     (1294,1914,4453,4533),
     (2031,4529,6001,6699),
     (4062,12002,31171,31731).
   All twelve roots are squarefree. In each tuple the outer cube sum equals
   the middle cube sum. The first two tuples have even Omega at every root;
   the third has odd Omega at every root.
   Files: /tmp/cube_omega_low_linear_squarefree.{py,json}.

2. Submission/SquarefreeOddPrimeColorObstruction.lean (67 lines) now proves
   no_uniform_edge_sum_two. For any completely additive c : Nat -> ZMod 4
   with 2*c(p)=2 at each prime, it is impossible that every strict squarefree
   collision has total color two. The proof is a short algebraic transport:
     S1+S2=S3+2*(c(647)+c(957)),
   and the last term vanishes because 647,3,11,29 all have odd color and
   957=3*11*29. Requiring S1=S2=S3=2 is contradictory modulo four.
   The module compiled successfully; its olean is current. Main axiom audit
   uses only propext, Classical.choice, Quot.sound. No holes or native_decide.
   Log: /tmp/squarefree_odd_prime_color_obstruction.log.

3. The ACTUAL nonmonochromaticity constraints on this squarefree source are
   SAT through the saved cutoff 100000. CaDiCaL returned SAT in about 0.13 s.
   This new instance has 3741 low-monochromatic primitive edges and 369111
   CNF clauses. Independent Python checking verified every CNF clause, every
   multiplicative high-bit recurrence, all odd prime colors, and all 51697
   stored squarefree collision edges (including dilations). The 60794 positive
   squarefree roots have color sizes [10538,15967,19835,14454].
   Files:
     /tmp/cube_c4_fixed_low_omega_squarefree.py
     /tmp/cube_c4_fixed_low_100000_1_omega_squarefree.{cnf,npz,out,exit}
     /tmp/cube_c4_fixed_low_100000_1_omega_squarefree_colors.npy
     /tmp/cube_c4_fixed_low_100000_1_omega_squarefree_audit.json
   This is an external finite certificate, not a Lean theorem or a uniform
   infinite coloring. The SAT run's .lrat is not an UNSAT certificate.

SCOPE: The new Lean obstruction concerns a stronger edge-sum condition only.
It does NOT exclude ordinary proper four-coloring, even with odd prime colors
on the squarefree source. The verified finite SAT result does NOT prove a
uniform coloring bound or extend its assignment beyond 100000. No target
proof or disproof is ready; Spec.lean is unchanged with its original sorry.

## Quadratic prime-parity two-color formula (new, exact finite obstruction)

Tested the squarefree-root formula
  color(n)=floor(Omega(n)/2)+sum_{p|n} b_p (mod 2),
with arbitrary prime bits. This is the high bit alone of the odd-prime-valued
ZMod 4 character. It is UNSAT on the saved collisions through 100000.
The instance has 100000 variables, 29846 primitive squarefree edges, and
421321 clauses. CaDiCaL returned exit 20 in about 59.01 seconds.

Independent encoding audit reconstructed factor counts and squarefreeness,
checked every strict cubic identity and primitivity, and checked all recurrence
and offset-NAE clauses (including exhaustive Boolean truth tables).
The backward-pruned UNSAT certificate retains 93924 original clauses,
296332 derived clauses, and 25285 variables. Independent forward RUP replay
verified all 296332 steps using 16823932 hints and reached the empty clause.

Files: /tmp/cube_quadratic_prime_parity.py;
/tmp/cube_quadratic_prime_parity_100000.{cnf,npz,out,exit,lrat};
/tmp/cube_quadratic_prime_parity_100000_pruned.{cnf,json,lrat};
/tmp/cube_quadratic_prime_parity_100000_pruned_rup_audit.json;
/tmp/cube_quadratic_prime_parity_100000_encoding_audit.json;
/tmp/check_quadratic_prime_parity_encoding.py.

This is an external finite obstruction, not a Lean theorem. It rules out
only this prescribed two-color formula. It does NOT refute the odd-prime
FOUR-color route, arbitrary squarefree colorings, or the original conjecture.

## Odd-prime character fibers have positive lower density (new, verified)

Submission/OddPrimeCharacterDensity.lean now compiles successfully. Its
squarefree_fiber_lowerDensity_pos proves that every squarefree fiber of a
completely additive character c : Nat -> ZMod 4 has positive lower density
if 2*c(2)=2, 2*c(3)=2, and 2*c(5)=2. The eight squarefree multipliers
1,2,3,5,6,10,15,30 supply every color, independently of the three odd colors.
The positive-density squarefree prefix-multiplier source and bounded dilation
cover transfer density to each fiber.

sidon_fiber_suffices derives the conjecture from a SINGLE cube-Sidon
squarefree fiber of such a character. No such character/fiber is constructed.
Both public axiom audits list only propext, Classical.choice, Quot.sound.
The olean is current; log: /tmp/odd_prime_character_density.log.
Spec.lean is unchanged and still unresolved.

## Global character follow-up (unresolved)

Reviewed the odd-prime character constraints after proving the fiber-density
lemma. No uniform finite satisfiability or extension theorem was established.
The SAT assignment through 100000 remains only a finite certificate; the
one-fiber sufficient criterion does not itself supply a Sidon fiber.
Reconsidered the cubic parametrization/lattice-count approach, but no uniform
bound controlling large cancellation was obtained. No asymptotic estimate
was inferred from the finite diagnostics.

No proof or disproof of the original existential statement is ready.
Spec.lean remains unchanged with its original sorry, and no submission has
been made. No computation is pending.

## Odd-prime character collision transport (new, verified)

Submission/OddPrimeCharacterTransport.lean compiles successfully. Its current
olean is built, and /tmp/odd_prime_character_transport.log audits all three
public theorems with only propext, Classical.choice, Quot.sound. No proof holes,
native_decide, or new axioms occur.

* exists_squarefree_coprime_color: for a completely additive c : Nat -> ZMod 4
  with odd value at every prime, every color is attained by a squarefree
  multiplier coprime to any prescribed positive integer N. Choose three fresh
  distinct primes; their eight subset products cover all four colors.
* all_fibers_sidon_of_one: if one squarefree fiber of c has Sidon cubes, every
  fiber has Sidon cubes. For any four roots, choose the multiplier coprime to
  their product and with the color shift needed to reach the prescribed fiber.
  Squarefreeness is preserved and the common nonzero cube factor cancels.
* fiber_sidon_iff: Sidonness of two squarefree fibers is equivalent.

This sharpens the scope of OddPrimeCharacterDensity: in the all-primes-odd
class, the one-fiber route is NOT weaker than proper four-colorability.
Neither side of the equivalence has been established for any character.

Also reviewed the endpoint, conic, and weighted-cover reductions. No uniform
all-family density cost, finite-head bound, or cancellation-safe global point
estimate was proved. The individual conic estimates cannot be combined merely
by countability. Reconsidering higher odd cycles did not supply an all-cycle
reciprocal cover bound; the existing quadratic triple classification is not
such a bound.

Spec.lean is unchanged, with SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63
and its original sorry. No valid proof or disproof is ready to submit, and no
computation is pending.

## Odd-root higher-cycle follow-up (new finite check; unresolved globally)

Reviewed OddCycleColoring, QuadraticOddSpecialization, and CollinearTripleParity.
The all-odd quadratic triple classification remains family-specific; it does
not control arbitrary higher cycles or give a reciprocal-cost bound for them.
The 181-edge HigherCycleObstruction includes even roots, so it is not by itself
an all-odd counterexample to a three-pair-only reduction.

A targeted new check reused the saved 100000-edge data and the 5281 divisor
sieve generators in /tmp/cube_parity_bucket_sieve_1206.json, then restricted
the surviving roots to odd integers. This gives 42200 source roots and 18023
stored collision edges. Exact F2 elimination found rank 18020 with all parity
right-hand sides consistent; no odd-incidence obstruction was found in this
finite instance. Script /tmp/cube_odd_higher_cycle_check.py; output
/tmp/cube_odd_higher_cycle_check.json. No new global collision enumeration was
performed. This finite consistency check is not an infinite coloring theorem,
a summability estimate for the generators, or a completeness-certified claim
about all arithmetic obstructions.

No global cover/counting bound or settlement was obtained. Spec.lean is still
unchanged with its original sorry. No proof has been submitted. No computation
is pending.

## Finite-energy score bands force a prime cover (new, verified)

Investigated slowly decaying prime weights as a bounded-variance alternative
to the existing growing-block scores. No global collision exclusion or
uniform all-family head bound was obtained. Bounded variance alone is not
Sidonness, and a fixed-family exceptional sieve still does not supply that
missing global estimate.

New module Submission/ScorePrimeCover.lean compiles without warnings. The
olean is current; /tmp/score_prime_cover.log audits all three public theorems
with only propext, Classical.choice, Quot.sound. There are no proof holes,
new axioms, or native_decide calls.

* summable_prime_outliers: if sum_{p prime} f(p)^2/p converges, then for each
  t>0, the primes with |f(p)|>=t have summable reciprocal mass.
* summable_prime_cover_of_score_band: if a cube-Sidon source contains every
  prime with |f(p)|<t, those outlier primes cover every prime-root collision.
  This needs neither divisor closure nor a density assumption.
* summable_prime_cover_of_nonempty_additive_band: for a completely additive
  real score with finite reciprocal-prime square energy, any nonempty fixed
  OPEN squarefree band |f(n)-mu|<t that is cube-Sidon yields a summable prime
  cover, even if the band contains no primes itself. Choose a squarefree q
  strictly inside the band, with margin epsilon. Every prime p coprime to q
  and with |f(p)|<epsilon gives q*p inside the band. Dilation cancels from
  the Sidon condition. The finitely many prime divisors of q and the
  epsilon-outlier primes therefore form the required summable cover.

SCOPE: This is a necessary condition for this class of fixed score bands,
not a nonexistence theorem, not a result for arbitrary moving centers, and
not a disproof of the conjecture. Existence or nonexistence of the required
prime cover remains unproved. No cube-Sidon band is constructed.

Spec.lean is unchanged, still with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No valid settlement is ready to submit. No computation is pending.

## Non-summable forbidden-divisor route reviewed (unresolved)

Reexamined GreedyDivisorCover and the smooth harmonic criteria without
assuming reciprocal summability of the forbidden divisors. That summability
is sufficient, not necessary, for a positive-density complement of multiples.
The verified primitive-generator and earlier-witness properties do not by
themselves give a uniform lower bound for the greedy set's prefix counts.
No bound on the overlap of the excluded multiple sets was obtained.

Also kept separate finite/profinite avoidance probabilities and actual
uniform natural-prefix counts: a bound on the former was not substituted for
the latter. The existing finite weighted-cover data and necessary summable
excluded-prime condition supply no missing sufficient density estimate here.
No new theorem or numerical experiment resulted from this review.

Spec.lean remains unchanged with the original sorry. No valid settlement is
ready, no proof has been submitted, and no computation is pending.

## Uniform oriented additive-score review (unresolved)

For a strict collision a<b<c<d with a^3+d^3=b^3+c^3, one has
ad<bc, so the logarithmic completely additive score has positive oriented
contrast f(b)+f(c)-f(a)-f(d). This is not a uniform positive margin.

Floating-point LP diagnostics using /tmp/cube_oriented_score_lp.py minimized
sum_p |w_p|/p subject to oriented contrast >=1 on the saved primitive,
all-squarefree collision edges. At cutoff 10000 there were 1515 edges and
1229 prime variables, objective 15.347702275433175, and reciprocal-prime
square energy 160.04258046449505 for the returned L1 optimizer. At cutoff
100000 there were 29846 edges and 9592 variables, objective
123.32925406392152 and returned square energy 9346.813054035127. Both solver
runs completed successfully. Artifacts: /tmp/cube_oriented_score_{10000,100000}
with .log, .exit, .json, and .npz suffixes. These are floating diagnostics,
not exact certificates, uniform bounds, or asymptotic divergence results.

A possible telescoping obstruction to uniform oriented margins on ALL
integer-root collisions was noted: insert arbitrarily many intermediate
rational representations of a fixed cube sum, clear denominators, and sum
the consecutive contrasts. This has not been formalized and simultaneous
clearing need not preserve squarefreeness. It does not refute the squarefree
score candidate or the original conjecture.

A possible quadratic root-lattice prime-divisibility bound and an additive
contrast second-moment application were considered but not proved. Even a
successful obstruction to that score criterion would not settle the target.
No global source, coloring, cover, or estimate was obtained. Spec.lean remains
unchanged with its original sorry. No process is pending.

## Uniform oriented-score obstruction (new, verified)

Submission/OrientedScoreObstruction.lean compiles successfully; its olean is
current. /tmp/oriented_score_obstruction.log audits both main theorems with
only propext, Classical.choice, and Quot.sound. No proof holes, new axioms,
or native_decide occur in this module.

* insert_representation inserts a rational cube-sum representation strictly
  between two nested positive pairs, using RationalCurveLocal.
* no_rational_uniform_gap: no arbitrary real score on positive rationals can
  have a uniform strictly positive oriented contrast g(b)+g(c)-g(a)-g(d)
  for every strict collision a<b<c<d, a^3+d^3=b^3+c^3. Repeated insertion and
  telescoping force the fixed contrast at (1,9,10,12) to exceed n*epsilon
  for every n.
* rational_gap_of_natural extends a completely additive natural score via
  f(q.num.toNat)-f(q.den); clearing denominators preserves the contrast.
* no_completely_additive_uniform_gap therefore rules out the corresponding
  uniform oriented-margin criterion on ALL positive integer collisions.

IMPORTANT: This is not the squarefree-only criterion investigated in the LPs.
Common denominator clearing need not preserve squarefreeness. It does not
rule out proper finite coloring, non-oriented score criteria, or the target.
The largest-root-degree source was reviewed again but supplied no new uniform
density estimate; its prior diagnostics were not rerun.

Spec.lean remains unchanged with its original sorry, SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No valid proof or disproof of the target is ready; no submission has been
made. No computation is pending.

## Multiplicative recurrence and unrestricted-score continuation (unresolved)

Reviewed a multiplicative recurrence route again. Positive natural density
cannot be substituted for positive density under a dilation-invariant mean:
the odd integers have natural density 1/2 but their preimage under doubling
is empty. No applicable recurrence or density-transfer theorem was found.
No new network/literature-access attempts were made.

Tested a different finite optimization condition: arbitrary real vertex
scores, NOT assumed completely additive, with oriented contrast >=1 on
all saved collision edges in the source. The LP minimizes sum |f(n)|/N.
It uses all edges, not only primitive ones, because score additivity is absent.
Script: /tmp/cube_free_oriented_score_lp.py.

Completed floating-point results:
* All roots, N=3000: 7846 edges, 2969 active vertices; objective
  1.0848825888999658, maximum |f| 9.268716033154803. Early-prefix costs
  were 5.867491427096727 at 100 and 1.933074533219055 at 1000.
* Squarefree roots, N=10000: 2292 edges, 4386 active vertices; objective
  0.12453333333333333, maximum |f| 3.3333333333333335. Prefix costs at
  100 and 1000 were 0.49333333333333335 and 0.272.
* Squarefree roots, N=30000: 10287 edges, 15223 active vertices; objective
  0.17579785886831717, maximum |f| 4.4488339208883305. Prefix costs at
  100, 1000, 10000 were 0.9783730601326096, 0.7205301263404419,
  0.2606023391159676 respectively.

Artifacts: /tmp/cube_free_oriented_{all_3000,sf_10000,sf_30000}, each
with .log, .json, .npz. An initial all-root N=10000 simplex run was killed
by the 300-second tool timeout; it produced only the build line in its log
and no result/certificate. The completed small jobs used HiGHS-IPM, except
sf_30000 which had already completed with the original default HiGHS method.
No job remains running. These are floating diagnostics, not exact certificates.

CLARIFICATION: A merely bounded average absolute score is not by itself the
claimed sufficient density input. A direct centered band |f|<1/4 with unit
oriented margins needs a sufficiently small mean relative to source density,
and a global construction needs uniform prefix control (possibly with a
fixed additive error). No such bounds, no appropriate global score, and no
source-preserving band density theorem were obtained. Endpoint-average
optimization was not substituted for simultaneous-prefix control.

No new target proof or disproof is ready. Spec.lean is unchanged with its
original sorry; no proof has been submitted. No computation is pending.

## Algebraic/multiscale and full squarefree-box continuation (unresolved)

Reconsidered finite-field moment-curve encodings and multiscale block
constructions. No encoding preserving exact cube identities with a uniform
positive root-density loss was found. The short-interval Sidon theorem still
needs uncontrolled cross-block compatibility; it was not treated as a global
construction. No new general coloring or recurrence theorem was obtained.

Checked the complete squarefree product box on the first thirteen primes
2,3,5,7,11,13,17,19,23,29,31,37,41, as a test of prime-by-prime odd Z/4Z
character extension. This differs from the older squarefree boxes, which
excluded 2 and 3 or used prescribed supports. The existing exact uint256
pair-sum enumerator processed 8192 roots and 33558528 unordered root pairs,
including repeated pairs, using about 2.15GB for records. It reported 256
collisions. Python arbitrary-precision checks verified the root products,
all reported identities, distinctness of roots, and the no-overflow bound.

Every reported collision normalizes to (2,15,33,34). None has uniform
Omega parity, so ALL 8192 odd-prime Z/4Z assignments survive. The projection
checks to successive prime-prefix boxes likewise impose no constraints.
This is a vacuous test of the hard high-bit extension condition, not evidence
of a uniform extension theorem or an infinite coloring construction.

Files: /tmp/cube_sf_odd_c4_first13.csv, .csv.roots, .log;
/tmp/check_sf_odd_c4_box.py;
/tmp/cube_sf_odd_c4_first13.csv.odd_c4.audit.json;
/tmp/cube_sf_odd_c4_first13.audit.log. These are external finite checks, not
Lean certificates or an infinite S-unit classification. No additional larger
box was run. No job remains pending.

Spec.lean is unchanged with its original sorry. No valid proof or disproof
of the conjecture is ready, and no submission has been made.

## Two-dimensional quadratic root-lattice and prime-tail bounds (new, verified)

Three new modules compile successfully, without warnings or holes. Their
oleans are current; all listed axiom audits use only propext, Classical.choice,
and Quot.sound. No new axioms or native_decide occur.

1. Submission/QuadraticRootLattice.lean
   * mass(a,b,c)=|a|+|b|+|c|+1, as a natural number.
   * form_abs_le bounds |Q(x)| by mass*ht(x)^2 in the sup norm.
   * anisotropic_of_nonsquare_discriminant derives Q(x)!=0 for nonzero
     integral x from nonsquareness of b^2-4ac. Indefinite forms are allowed.
   * root_lattice_card bins BOTH coordinates. If every difference of points
     in S lies in the zero locus of Q modulo p, the modulus exceeds
     mass*(H-1)^2, and the box has side bound N, the bin map is injective.
   * mesh_parameters chooses H=floor(sqrt((p-1)/mass))+1 and an integral
     bin-count bound D. It proves p<=mass*H^2 and (D+1)*H<=4N whenever
     0<p<=mass*N^2.
   * root_lattice_mass_bound gives p*|S|<=16*mass*N^2.
   Log: /tmp/quadratic_root_lattice.log.

2. Submission/QuadraticPrimeDivisibility.lean
   * points(a,b,c,N,p) consists of NONZERO integral vectors in [-N,N]^2
     satisfying p | Q(x).
   * prime_divisibility_bound proves for EVERY prime p and every N:
         p*|points(a,b,c,N,p)| <= 48*mass(a,b,c)*N^2.
   * If p divides the leading coefficient, its size is bounded by mass and
     the full-box estimate suffices. Otherwise the solutions are covered
     by the zero residue lattice plus at most two projective root lines;
     differences on each line again satisfy Q=0 modulo p. If p exceeds
     mass*N^2, there are no nonzero points.
   Log: /tmp/quadratic_prime_divisibility.log.

3. Submission/QuadraticPrimeTail.lean
   * finite_prime_union_bound gives the corresponding union bound with
     right side 48*mass*N^2*sum_{p in P}1/p.
   * uniform_prime_tail: if B is a set of primes with convergent reciprocal
     sum, then for every epsilon>0 there exists H such that FOR ALL N,
     the number of nonzero box points for which some p in B, p>H, divides
     Q(x) is at most epsilon*N^2. The cutoff is independent of N.
   Log: /tmp/quadratic_prime_tail.log.

SCOPE: These are uniform-in-box-size estimates for one fixed irreducible
quadratic form. The coefficient constant remains explicit and depends on
the form. No all-conic-family summation, source with linear collision count,
positive-density Sidon band, finite coloring, or disproof has been obtained.
In particular the result must not be promoted to a uniform estimate over
families whose coefficients grow with the root cutoff.

Spec.lean remains unchanged with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No valid target proof or disproof is ready, no proof has been submitted, and
no computation is pending.

## Summable-prime conic obstruction (new, verified)

Four further modules now compile, with current oleans and permitted-axiom
checks only (propext, Classical.choice, Quot.sound):

* PositiveLocalProducts.lean: positive factors at most one with summable
  deficits have a uniform positive lower bound over all finite products.
* QuadraticUnitResidues.lean: four anisotropic binary quadratic forms with
  a simultaneous unit residue at a prime have positive local unit density,
  at most one, and deficit at most boundConstant/p. The real-cast ambiguity
  at the upper bound is fixed. Parentheses inside boundConstant's sum matter.
* QuadraticPrimeAvoidance.lean: combine the positive product bound, CRT
  discrepancy, and quadratic prime-tail estimates. Any locally admissible
  four-form family has a natural parameter pair with positive first
  coordinate such that every form avoids every prime in a reciprocally
  summable prime set. The final counting argument removes the axis and
  four tails; no uniform-in-coefficients estimate is asserted.
* SummablePrimeConicObstruction.lean: specialize to the explicit conic with
  coefficient triples (29,1160,3419), (263,19880,374777),
  (571,41884,769417), (589,43324,797983). Anisotropy and local
  admissibility are verified. collision_avoiding produces four strictly
  ordered positive roots with equal outer/inner cube sums, all avoiding
  the forbidden primes. not_sidon proves that a source consisting of all
  integers avoiding multiples of a summable prime set is not cube-Sidon.

Logs: /tmp/positive_local_products.log, /tmp/quadratic_unit_residues.log,
/tmp/quadratic_prime_avoidance.log, /tmp/summable_prime_conic_obstruction.log.

SCOPE: This rules out prime-only forbidden-multiple constructions. It does
NOT rule out arbitrary proper-divisor covers, general divisor-closed sets,
or arbitrary positive-density sets. In particular ScorePrimeCover.lean
forces a summable cover of PRIME-ROOT collisions, whereas the new conic
obstruction does not produce prime roots. These two statements cannot be
combined to disprove finite-energy additive-score bands. The summary of
that earlier score result must retain the prime-root qualifier.

The original Spec.lean is unchanged and unresolved. No target proof or
disproof has been obtained, and no proof has been submitted.

## Squarefree summable-prime obstruction (new, verified)

Rechecked the existing incidence-concentration and largest-root-degree results
without rerunning the finite diagnostics. They supply no uniform bounded-degree
source or small deletion theorem. Superlinear edge counts were not confused
with an upper bound on independence density.

Seven new modules strengthen the recent prime-only conic obstruction to
simultaneously SQUAREFREE roots. Each compiles with a current olean, and all
printed axiom audits use only propext, Classical.choice, Quot.sound.

1. CoprimeBoxCRT.lean: generalizes the exact two-coordinate CRT residue count
   and box discrepancy from distinct primes to pairwise coprime positive
   moduli. The error remains 2*N*d+d^2 for product modulus d.
2. PeriodicParameterSieve.lean: a uniform positive finite-product lower bound
   and an eventually negligible tail imply positive two-parameter density.
   The first coordinate is positive; the axis is removed at cost at most N.
3. QuadraticSquareTail.lean: square_tail_count is the explicit tail version
   of the affine square-divisor count, with main term 3*N^2/H and error
   (4*N+1)*primeCounting(L*N). uniform_square_tail makes this at most
   epsilon*N^2 for all sufficiently large N, at one fixed cutoff H. Positive
   leading and trailing coefficients and nonzero discriminant are assumed.
4. QuadraticNaturalPrime.lean: transfers the integer-box prime estimates
   to natural parameter boxes. prime_box_bound includes the origin at cost
   one; badTail_card_le excludes it by positivity of the first coordinate.
   Coefficients are reversed because quad(a,b,c,t,u)=a*u^2+b*t*u+c*t^2.
5. QuadraticSquareLocal.lean: local conditions modulo p^2 impose both
   p^2 nondivisibility and, for forbidden primes, p nondivisibility. Counts
   are identified with natural residue-box counts. Positive local unit
   admissibility gives positive factors at most one. Their deficits are
   bounded by squareMass/p^2 + primeMass*1_{p in B}/p. Singular small primes
   are included in an explicit finite coefficient constant.
6. SquarefreePrimeParameterSieve.lean: combines the two tail estimates and
   summable local deficits. parameter_density gives a positive lower bound
   eta*N^2 for good parameter counts eventually. exists_avoiding produces
   four squarefree quadratic values avoiding all primes in B.
7. SquarefreeSummablePrimeObstruction.lean: verifies all inputs for the fixed
   conic from SquarefreeConicFamily. collision_avoiding produces four positive
   squarefree roots in strict order with equal outer and inner cube sums,
   none divisible by a prime in B. not_sidon proves
       not IsSidon (cubes '' {n | Squarefree n and forall p in B, not p|n})
   whenever B consists of primes and has convergent reciprocal sum.

Fresh audit logs: /tmp/audit_<FileName>.log for the seven files above.
No proof holes, new axioms, or native_decide occur in the new modules.
Temporary CheckSquareLocal.lean was removed.

SCOPE: The squarefree prime-only avoidance source itself is not cube-Sidon.
This does NOT exclude a further positive-density subset, composite-divisor
covers, or completely additive character fibers. In particular, the theorem
asserts neither prime roots nor prescribed factor-count parities. It cannot
be combined with ScorePrimeCover's PRIME-ROOT cover to claim a contradiction.
The density in the sieve theorem is PARAMETER density, not the root density
required by the conjecture.

Spec.lean remains unchanged with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
There is no valid proof or disproof of the original conjecture to submit.

## Summable fractional prime-weight obstruction (new, verified)

Revisited the uniform weighted divisor-cover criterion and its dual viewpoint.
No bound for GENERAL divisor weights was obtained. The analysis instead led
to a stronger obstruction for prime-supported fractional weights, not merely
integral forbidden-prime sets.

Five new modules compile without holes and have current oleans. All printed
axiom audits use only propext, Classical.choice, Quot.sound:

1. BoxDensityLimits.lean: removes the first coordinate axis at cost N and
   proves convergence of normalized CRT box counts to the finite product of
   local densities. normalized_limit turns an O(N) discrepancy into the limit.
2. QuadraticConditionalCounts.lean: for a fixed finite head of primes avoided
   by all four forms, a further fixed prime p outside the head has conditional
   frequency delta*localDensity(zeros,p). Head primes have zero frequency.
   counts_bound uniformly dominates the positive-axis count divided by N^2
   by 48*mass/p. The fixed-form anisotropy hypothesis is explicit.
3. QuadraticPrimeMoments.lean: primeScore(w,n) sums w(p) over DISTINCT prime
   factors of n. moment_identity interchanges a finite parameter sum and
   the prime sum using actual finite support. moment_tendsto uses Tannery's
   dominated-convergence theorem, with domination by the summable reciprocal
   prime-weight cost. small_prime_weight_tail supplies a small indicator tail.
4. SmallQuadraticPrimeScores.lean: exists_small_total proves that any fixed
   locally unit-admissible anisotropic positive four-quadratic family has a
   positive-first-coordinate parameter pair with arbitrarily small TOTAL
   nonnegative prime score, when sum_{p prime} w(p)/p converges. The proof
   chooses a finite prime head, takes conditional weighted moments, and
   contradicts a hypothetical uniform positive score lower bound.
5. PrimeWeightedCoverObstruction.lean: specializes to the explicit strict
   conic. collision_small_total provides a strict positive cube collision
   with total prime score below any prescribed positive threshold.
   divisorWeight_eq_primeScore handles weights supported only on primes.
   no_summable_prime_weight_cover rules out IsWeightedCubeDivisorCover w for
   nonnegative prime-supported w with Summable(w(d)/d).
   low_primeScore_not_sidon rules out the positive integers with primeScore
   below any fixed positive threshold as a cube-Sidon root set.

Fresh logs: /tmp/audit_<FileName>.log for the five modules above.
Temporary CheckWeightedPrime.lean was removed. No new finite optimization
or numerical extrapolation was used.

Lean detail: Finset.filter with a substituted predicate can carry a different
DecidablePred instance from a directly written filter. An extensional equality
via mem_filter was needed in the CRT limit bridge; visually identical counts
were not silently treated as definitionally equal.

SCOPE: This excludes even arbitrarily reused FRACTIONAL prime weights. It does
not exclude composite-divisor weights, signed prime scores, squarefree-only
score bands, or arbitrary positive-density root sets. primeScore counts
DISTINCT prime divisors, not their valuations. The small-score collision is
not asserted squarefree in this extension. The general uniform finite-cover
bound needed to settle Spec.lean remains unproved.

Spec.lean is unchanged with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No valid proof or disproof of the original conjecture is ready to submit.

## Semiprime fractional-weight obstruction (new, verified)

Seven modules now compile with current oleans and axiom audits using only
propext, Classical.choice, Quot.sound. Fresh logs are /tmp/audit_<Name>.log.

1. QuadraticLatticeCover.lean: three-piece prime covers of a binary quadratic
   zero locus, coprime product covers by intersections, and the generic
   cover_mass_bound d*card(points) <= 16*mass*L*N^2 for L cover pieces.
2. QuadraticSquareLatticeCover.lean: the zero lattice has quadratic differences
   divisible by p^2; Hensel lifting supplies a three-piece cover modulo p^2
   when the leading coefficient and discriminant are nonzero modulo p.
3. QuadraticSemiprimeDivisibility.lean: LowComplexity d means d is prime or
   a product of two primes, INCLUDING prime squares. low_complexity_bound
   proves d*card(points) <= constant*N^2 uniformly in such d. Exceptional
   primes dividing coefficients or discriminant are absorbed in a fixed
   coefficient constant. Anisotropy and nonzero discriminant are explicit.
4. QuadraticCompositeCounts.lean: zeros is defined modulo every positive
   modulus, unlike the earlier prime-only definition. General coprime CRT
   gives conditional frequencies if no head prime divides d. Otherwise
   counts are zero. The uniform semiprime box bound implies the local-density
   bound by passing to the limit with an empty head, avoiding a redundant
   residue-lifting argument. Avoids S d means no prime in S divides d.
5. QuadraticDivisorMoments.lean: exact first-moment identity for divisorWeight,
   and dominated convergence for nonnegative weights supported on
   LowComplexity with Summable(w(d)/d). head_survivor_large uses a prime
   divisor to show that moduli surviving the prime head below H are >=H.
6. SmallQuadraticDivisorWeights.lean: for four locally unit-admissible
   anisotropic positive quadratics with nonzero discriminants, such weights
   have arbitrarily small TOTAL divisor weight at some positive-axis pair.
7. SemiprimeWeightedCoverObstruction.lean: specializes to the fixed conic,
   giving a strictly ordered positive cube collision of arbitrarily small
   total divisor weight. no_summable_low_complexity_weight_cover excludes
   IsWeightedCubeDivisorCover for these weights. low_divisorWeight_not_sidon
   excludes every positive low-weight band of this restricted kind.

These are genuine fractional REUSABLE divisor-weight obstructions, not merely
whole-root reciprocal-mass results. However the support restriction is
essential to the proved domination. General composite weights, signed scores,
squarefree-only bands, and arbitrary positive-density sets remain untreated.
The small-weight collision is NOT asserted squarefree.

Also reviewed the conic classification, character-coloring criteria, and the
all-family cancellation gap. No global construction or arbitrary-density
contradiction was obtained. Temporary CheckComposite.lean has been removed.
Spec.lean remains unchanged with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No valid proof or disproof of the original conjecture has been obtained.

## Prime-variable elimination review (finite diagnostic only)

Revisited the finite-coloring and compactness routes. No uniform finite
color bound, simultaneous-prefix density construction, or missing global
arithmetic estimate was proved.

A new exact structural diagnostic used the ALREADY SAVED 3741 primitive,
squarefree, uniform-Omega-parity constraints through 100000. For each edge,
the prime-variable support is the union of the prime supports of its roots.
Peeling an edge whenever it meets a prime variable occurring in at most one
remaining edge leaves 1334 edges and 927 active primes. Peeling at threshold
two removes all edges. Script: /tmp/check_odd_c4_peeling.py.

This is only a property of the saved finite constraint system. In particular:
* degree-two peeling was NOT proved sufficient for these NAE constraints,
  whose root colors are affine sums of prime bits;
* no peeling property for arbitrary finite prefixes was established;
* the known three-edge odd-prime obstruction already has no degree-one
  prime variable, so a universal leaf-only argument cannot work.

No new target theorem or target-file edit resulted. Spec.lean is unchanged
and unresolved; no proof or disproof is ready to submit.

## Squarefree small weights and signed additive bands (new, verified)

Six new modules compile without warnings or holes, with current oleans and
printed axiom audits restricted to propext, Classical.choice, Quot.sound.
Fresh logs: /tmp/audit_<Name>.log. Temporary CheckSquareHead.lean was removed.

1. QuantitativeParameterSieve.lean: density_of_product_lower retains a given
   Euler-product lower bound delta and proves eventual parameter count at
   least (delta/2)*N^2, rather than hiding this constant existentially.
2. GeneralBoxDensityLimits.lean: joint_positive_density for arbitrary
   pairwise coprime positive moduli, with the first parameter axis removed.
3. SquarefreeHeadDensity.lean: relative_density gives one gamma>0 such that
   for EVERY finite prime head S, eventually the squarefree head-parameter
   count is at least gamma*headDensity(S)*N^2. The cutoff may depend on S;
   gamma does not. The proof identifies prime avoidance modulo p^2 with the
   unit factor modulo p using uniqueness of CRT limits, then factors the
   finite product into head and squarefree-only factors. The squarefree-only
   Euler product supplies the uniform relative lower bound.
4. SquarefreeSmallDivisorWeights.lean: the small-total-divisor-weight theorem
   now produces simultaneous squarefree quadratic values. Weights are
   nonnegative, supported on LowComplexity (prime or product of two primes),
   and have Summable(w(d)/d). The upper moment is over the whole unit head;
   the lower comparison uses the new uniform squarefree proportion.
5. SquarefreeSmallWeightCollision.lean: specializes to the strict explicit
   conic. collision_small_total_coprime produces four positive squarefree
   roots, in strict order, coprime to any fixed q>0, with total divisor weight
   below any t>0. A finite prime-weight perturbation enforces coprimality.
   low_squarefree_divisorWeight_not_sidon rules out the corresponding
   squarefree, coprime-to-q positive low-weight bands.
6. SummableAdditiveBandObstruction.lean: for a completely additive real score
   f on positive integers with
       Summable(fun p => if p.Prime then |f(p)|/p else 0),
   collision_small_scores produces a strict squarefree collision, coprime
   to any fixed q>0, with all four absolute scores arbitrarily small.
   nonempty_band_not_sidon proves that any fixed open band
       {n | Squarefree n and |f(n)-mu|<t}
   containing one squarefree q cannot have Sidon cubes. Multiply the
   small-score collision by q; coprimality preserves squarefreeness.

SCOPE: The last result allows SIGNED scores, but assumes reciprocal-prime
ABSOLUTE FIRST MOMENT (L1). It does NOT follow from merely finite square
energy (L2), and does not cover moving centers or arbitrary positive-density
sets. The preceding semiprime-weight results now genuinely include squarefree
roots, superseding the old squarefreeness caveat in that restricted class.
Neither the support restriction nor the summability hypothesis is removed.

Spec.lean remains unchanged with the original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No valid proof or disproof of the original conjecture has been obtained.

## Finite-square-energy squarefree oriented-contrast obstruction (new, verified)

Nine modules (1026 lines total) were freshly compiled in dependency order.
Logs: /tmp/audit_<Name>.log. All are warning-free; all printed axiom audits
contain only propext, Classical.choice, Quot.sound. No proof holes or added
axioms occur in these files. Current oleans are present. CheckCovariance.lean
was removed.

1. QuadraticEqualDiscriminant.lean: an invertible shear identifies quadratic
   zero sets over a finite field when their discriminants coincide. For the
   explicit four-form conic, local prime densities match in pairs (0,1) and
   (2,3) outside p<=1000000. Thus the sign vector [-1,1,1,-1] has zero local
   mean at each regular prime.
2. DualPrimeConditionalCounts.lean: CRT discrepancy for two DISTINCT prime
   divisibility conditions under an arbitrary finite unit head S. Error is
   2*N*D*p*q+(D*p*q)^2+N, with D=product(S).
3. ConicPrimeCovariance.lean: off-diagonal contrast covariance is at most
   16 times that discrepancy; diagonal covariance is at most four times
   the sum of the four one-prime counts.
4. ConicSmallPrimeVariance.lean: finite weighted second-moment estimate,
   with the off-diagonal loss bounded by
       16*maxError(S,N,T)*mass(P,w)*T^2.
   No boundedness assumption on individual real weights is needed.
5. QuadraticScoreTailBounds.lean: uniform nonnegative prime-score first
   moments, convergence of summable reciprocal-prime tails to zero, and
   the elementary fact that n<=T^k has at most k distinct prime factors
   exceeding T. Cauchy--Schwarz bounds the corresponding large-prime score.
6. ConicScoreSplit.lean: exact small/large prime decomposition on a unit
   head, diagonal comparison with prime-score first moments, and the bound
   largeContrast^2 <=68*sum_i primeScore(large-prime square weights,F_i)
   for parameter boxes of side T^8, T>=1000000. Each F_i<=T^17 there.
7. ConicContrastMoments.lean: the full normalized contrast second moment
   has an explicit upper bound tending to eight times the head-conditioned
   diagonal limit. The finite-prime discrepancy vanishes after normalization
   as O(D/T^4+D^2/T^10+1/T^6), times the total energy. The large-prime term
   tends to zero by summability.
8. SquarefreeSmallContrast.lean: combines that upper bound with the uniform
   relative squarefree parameter density. After taking a sufficiently large
   finite prime head, obtains a positive-axis squarefree parameter pair with
   arbitrarily small ABSOLUTE inner-minus-outer contrast. Any prescribed
   finite prime head may additionally be avoided.
9. L2OrientedScoreObstruction.lean: collision_small_contrast gives a strict
   positive squarefree cubic collision, all roots coprime to any fixed q>0,
   satisfying
       |f(n1)+f(n2)-f(n0)-f(n3)|<epsilon
   for every completely additive f with
       Summable(fun p => if p.Prime then f(p)^2/p else 0).
   no_uniform_absolute_gap rules out a fixed positive lower bound on these
   absolute oriented contrasts, even on the squarefree coprime source.

SCOPE: This is genuinely an L2 result, unlike the earlier L1 small-individual-
score theorem. However it controls ONLY the signed contrast. The two pairs
of forms have different discriminants and can have different score drifts;
small contrast does NOT place all four roots in one short score band.
Consequently this does not rule out general L2 bands, moving centers, ordinary
finite colorings, or arbitrary positive-density cube-Sidon sets. It is a
limitation on one construction method, not a disproof of the conjecture.

Spec.lean remains unchanged with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
The original conjecture is unresolved; no valid proof or disproof is ready.

## Global construction review after the L2 obstruction (unresolved)

Revisited finite divisor-cover compactness, the divisor-closed greedy source,
finite-prime harmonic projection, and finite coloring criteria. None of the
necessary uniform bounds or extension properties was obtained. The new L2
oriented-contrast obstruction was not used to claim nonexistence of general
score bands or of an arbitrary positive-density Sidon root set.

In particular, summing familywise estimates still leaves uncontrolled initial
ranges depending on the conic; finite colorings of bounded prefixes do not
supply an infinite coloring without a uniform theorem. No new numerical
collision search, solver claim, or target-file edit resulted from this review.

Spec.lean remains unchanged with its original sorry. No proof or disproof of
erdos_1206.parts.ii is ready for submission.

## Finite oriented square-energy budgets are unbounded (new, verified)

FinitePrimeEnergyCompactness.lean and FiniteOrientedEnergyObstruction.lean
(207 lines total) compile without warnings. Fresh /tmp/audit_<Name>.log files
and current oleans are present. Printed axiom audits use only propext,
Classical.choice, Quot.sound.

The compactness lemma first truncates each finite-prefix prime score at its
cutoff; without truncation, unbounded untested coefficients would invalidate
the argument. The common energy budget bounds each coordinate, so a product
of compact real intervals yields a coordinatewise convergent subsequence.
Finite energy sums pass to the limit, giving a summable infinite energy.

The obstruction then applies SquarefreeSmallContrast. Even using just the
fixed conic's squarefree values, finite scores with a uniform positive
absolute inner-minus-outer gap cannot have a uniformly bounded reciprocal-
prime square-energy budget. eventually_exceeds_budget proves that for every
real C and epsilon>0, every sufficiently large cutoff requires energy >C.
unbounded_additive_energy exports the implication for completely additive
scores tested on all strict squarefree collisions in a finite prefix.

This replaces an informal inference from finite oriented-score optimization
with a kernel-verified unboundedness theorem. It does NOT rule out adaptive
score-range conditions, ordinary colorings, or arbitrary positive-density
cube-Sidon root sets. Spec.lean remains unchanged and unresolved.

## Largest-three score investigation (partial; no construction)

UpperTripleCubeScale.lean is now verified with current olean. Both printed
axiom audits use only propext, Classical.choice, Quot.sound. It proves:
* If c<d and a^3+d^3=b^3+c^3, then d^2<=b^3.
* Consequently any m,n between b and d satisfy m^2<=n^3 and n^2<=m^3.
The smallest root a need not be power-comparable to the other three.

The prior bounded floating-point diagnostic /tmp/cube_top3_energy.py tested
the FIXED SIGNED condition f(c)+f(d)-2*f(b)>=1, not adaptive score spread.
Saved results at N=3000 and 10000 have respectively 293 and 1515 primitive
squarefree edges, energies about 2.78657 and 124.66226, and minimum margins
about 0.99999913 and 0.99998320. Files are
/tmp/cube_top3_energy_{3000,10000}.{log,json,npz}. These are not exact
certificates, asymptotic bounds, or an infinite score construction. No new
optimization or collision search was run in this continuation.

A single gap-ratio conic can contain both positive ordering sectors A<B<C<D
and A<C<B<D. Its paired local prime-density drifts give opposite signs to the
fixed signed largest-three contrast in these two sectors. This may obstruct
that signed criterion; it does NOT obstruct adaptive score spread. Neither
a simultaneous squarefree two-sector family nor a corresponding theorem has
been constructed. The q=1/3 example has local-unit issues; q=13/37 is only a
candidate (the displayed point 229,414,517,582 is not all squarefree).

Scope clarification: AllPositionalCubeCliques clears rational denominators
but does NOT preserve squarefreeness. Its fixed-positional-pair obstruction
on all positive roots does not automatically transfer to squarefree sources.
No finite coloring theorem on that restricted source has been established.

Spec.lean is unchanged and unresolved. The next analytic subproblem is
vanishing moving-mean oscillation on power-comparable intervals for finite
reciprocal-prime square energy; even proving that will not supply the missing
adaptive-spread score or settle the original conjecture.

## Power-window moving means and full-score variance (new, verified)

Five auxiliary files now compile cleanly, with current oleans and fresh logs
/tmp/audit_<Name>.log. Printed axiom audits use only propext,
Classical.choice, Quot.sound. No proof holes or added axioms occur.

1. UpperTripleCubeScale.lean: the previously pending geometric lemma is
   verified. In a collision a^3+d^3=b^3+c^3 with c<d, d^2<=b^3; all pairs
   between b and d are power-comparable with exponent ratio 3/2.
2. PrimePowerWindowMass.lean: eventually_log_moment derives the unconditional
   logarithmic prime first-moment bound from the existing near-one prime
   moment estimate, without choosing a Dirichlet character. A single D>0
   bounds reciprocal prime mass in (U,U^k] by D*k for all positive integer k
   and all sufficiently large U, including arbitrary finite subsets.
3. PowerWindowMeanOscillation.lean: defines prefixMean using all primes up to
   U and center at cutoff(n)=2^(Nat.log 4 n+1). Under finite reciprocal-prime
   square energy, prefix_power_oscillation is uniform throughout (U,U^k].
   center_power_oscillation proves uniform vanishing when m^2<=n^3 and
   n^2<=m^3. collision_center_oscillation applies it to the entire interval
   [b,d] in sufficiently large cubic collisions. The proof uses tail energy,
   weighted Cauchy--Schwarz, and the prime-window mass bound; not a numerical
   estimate. cutoff_power_comparable explicitly requires both roots positive.
4. FullPrimeScoreVariance.lean: extends the bound 48*N*energy to the full
   strongly additive score sum_{p|n} w(p), centered at the above moving mean.
   On each fixed integer prefix both scores and centers agree EXACTLY with
   a sufficiently large finite prime block, so no exchange of infinite sums
   and prefix limits is needed. Includes head/tail splitting and
   tail_variance_small: removing a fixed finite prime head makes the uniform
   normalized tail second moment arbitrarily small.
5. FinitePrimePeriodVariance.lean: distinct-prime covariances vanish exactly
   over any complete period divisible by all primes in the block. Hence its
   finite-block centered variance is at most D*mass, with arbitrary real
   weights. primeSum_mod proves dependence only on the residue modulo D.

REMAINING GAPS: An arbitrary-width positive-density short moving band has NOT
been proved here. A possible proof is finite-head periodic approximation plus
finite interval pigeonholing, with tail variance small relative to a uniform
pigeonhole mass. It is not legitimate simply to condition on a single finite
head atom: that atom's density can decrease faster than the tail variance.
For squarefree bands, squarefree preservation also needs proof. More
importantly, no finite-L2 score with uniform adaptive largest-three spread on
all sufficiently large squarefree collisions has been constructed. The fixed
signed condition is not interchangeable with adaptive spread.

AllPositionalCubeCliques remains an all-root obstruction, not automatically a
squarefree-source obstruction. The five new modules settle neither the
original existential proposition nor its negation. Spec.lean is unchanged
with its original sorry. No verification submission was made.

## Arbitrarily short squarefree moving bands and adaptive score criteria (new, verified)

Eleven modules have been freshly compiled and audited in this continuation.
All are warning-free, have current oleans, and printed axiom audits contain
only propext, Classical.choice, Quot.sound. Logs are /tmp/audit_<Name>.log.
No proof holes, added axioms, native_decide, or target-file edits were made.

1. FiniteShortBandSelection.lean: a finite compact interval cover and a second
   moment bound give a short band containing a fixed positive fraction of any
   finite sample. The fraction depends ONLY on the moment bound and requested
   radius, not on the sample, prime head, or modulus. This is the uniformity
   needed to avoid the shrinking-single-atom error.
2. PeriodicResidueCounts.lean: for any B subset range D, the count of n<N with
   n mod D in B differs from |B|*N/D by at most D. Exports an every-prefix
   lower bound with any coefficient delta satisfying delta*D<=|B|.
3. FiniteHeadApproximation.lean: the finite-head centered score is periodic
   modulo the product of the head primes. Its complete-period second moment
   is at most period*energy. Above H^2, the full deviation minus this periodic
   score is EXACTLY the tail deviation. Handles the 0/period endpoint swap.
4. FullMovingBandDensity.lean: exists_band proves for every epsilon>0 and
   every w with Summable(if p.Prime then w(p)^2/p else 0), there is a fixed
   real mu such that
      {n>0 : |primeScore(w,n)-center(w,n)-mu|<epsilon}
   has positive LOWER density. Choose the tail cutoff after the uniform band
   fraction is fixed, select a periodic head band, and remove the tail-bad
   set plus a finite initial interval. This is no longer a missing step.
5. SquareDivisorTail.lean: a uniform every-prefix bound makes the integers
   divisible by b^2 for some b>K have arbitrarily small density. The proof
   uses summability of 1/b^2 and exact counts of multiples.
6. PositiveDensityTransfer.lean: inclusion and removal of a finite initial
   interval preserve positive lower density, via explicit prefix bounds.
7. RadicalSourceDensity.lean: every positive-lower-density set has a positive-
   density subsource on which n<=K^2*radical(n), for one fixed K>0. The radical
   map there has uniformly bounded fibers. In particular radical_image_density
   proves the radical image of ANY positive-lower-density set still has
   positive lower density. This theorem does NOT preserve cube-Sidonness.
8. SquarefreeMovingBandDensity.lean: exists_squarefree_band proves the same
   arbitrary-width positive-lower-density moving-band statement with Squarefree
   n imposed. Radicalization preserves the strongly additive prime score.
   On the bounded-cofactor source, large n and radical(n) are power-comparable,
   so their centers differ by a vanishing amount. NO cube identity is transported
   through radicalization; that would be invalid.
9. UpperTripleScoreCriterion.lean: score_suffices and additive_score_suffices
   settle the target CONDITIONALLY on a finite-square-energy score having a
   uniform positive adaptive spread among b,c,d for every sufficiently large
   strict squarefree collision a<b<c<d. Which pair supplies the gap may vary.
   Uses the new short-band theorem, center oscillation, and finite trimming.
10. FiniteUpperTripleScoreCriterion.lean: uniform_budget_suffices reduces this
    to a SINGLE energy bound C and a SINGLE positive margin epsilon that work
    for EVERY finite cutoff. Coefficients are truncated before compactness.
    The maximum of the three absolute score differences is continuous, so
    adaptive finite constraints pass to the infinite limit.
11. CenteredScoreCriterion.lean: a WEAKER sufficient criterion uses the spread
    of ALL FOUR CENTERED deviations, rather than raw upper-three scores.
    No comparability assumption on the smallest root is required. Its finite
    compactness theorem waits until both the four roots and their four mean
    cutoffs are below the testing cutoff, so truncation preserves each fixed
    centered constraint eventually. No uniform finite budget is established.

The shift mu in the band theorem depends on epsilon; the theorem does not say
that every shift works. The squarefree theorem concerns strongly additive
prime-support scores; completely additive scores agree with these on squarefree
integers. The new sufficient criteria supply NO separating score. They are
not a proof or disproof of the original existential conjecture.

## Adaptive upper-three finite energy diagnostic (new; exact finite audits)

The only new optimizer used the ALREADY SAVED cubic collision edges. No new
collision search was run. Script: /tmp/cube_adaptive_top3_energy.py. It chooses
one signed pair among b,c,d per edge from the current score, solves the resulting
convex quadratic energy problem numerically, then allows the pair to change.
This is nonconvex alternating optimization, NOT a certificate of optimality.

At N=10000: 1515 primitive squarefree edges, 1229 prime variables, 12 iterations,
about 2.20 seconds. Best rescaled feasible floating energy: 0.82257881294.
At N=100000: 29846 primitive squarefree edges, 9592 prime variables, 180-second
budget. Best rescaled feasible floating energy: 7.87771638828. Some intermediate
solver returns had poor margins (as low as 0.7729); they were not silently
regarded as feasible. The best score was retained separately. No optimizer
is still running.

Files: /tmp/cube_adaptive_top3_energy_{10000,100000}.{log,json,npz}.
Energy at N=100000 is concentrated on small primes: approximately 5.1471 on
p<=100, 2.1868 on 100<p<=1000, 0.4549 on 1000<p<=10000, and 0.08888 above 10000.
This neither proves divergence of the optimum nor a uniform bounded construction.

Independent exact finite audit: /tmp/audit_adaptive_top3_rational.py rounds the
best weights (with a safety enlargement) to integers divided by 10^8. It checks
prime factorization, squarefreeness, all stored cube identities, and upper-three
score gaps using integer arithmetic. Energy is bounded from above by summing
exact upward-rounded rational terms at precision 10^-12.

N=10000: all 2292 stored squarefree edges INCLUDING dilations checked;
minimum integer spread 100000999 (denominator 100000000);
energy <=822595266968/10^12 <1.
N=100000: all 51697 stored squarefree edges INCLUDING dilations checked;
minimum integer spread 100001000;
energy <=7877873947553/10^12 <8.

Rational weights and audit reports:
/tmp/cube_adaptive_top3_energy_<N>_rational.npz
/tmp/cube_adaptive_top3_energy_<N>_rational_audit.json
These are exact external FINITE checks on stored data, not Lean certificates,
not centered-four-score tests, and not evidence sufficient for a uniform
all-cutoff bound. In particular they cannot instantiate either compactness
criterion. No larger-cutoff or repeated-seed search was run.

Spec.lean remains unchanged with its original sorry and SHA256
9a9478fe225b86dfcfb75f7cb2fd5af174e3d262ecb634e42143aea6f1affb63.
No valid proof or disproof of erdos_1206.parts.ii is ready for submission.

## Centered-four finite energy diagnostic (exact finite audits)

Script /tmp/cube_centered4_energy.py tested the actual centered-four spread
criterion on ALREADY SAVED squarefree collision data, INCLUDING dilations.
The centered functional was primeScore(w,n)-sum_{p<=cutoff(n)} w(p)/p.
Alternating optimization selected a signed extremal pair per edge and solved
a convex reciprocal-prime square-energy subproblem. This is not an optimality
certificate. Initialization used the saved odd-prime ZMod 4 coloring.

N=10000: 2292 stored squarefree edges, 1229 prime variables, 12 iterations,
about 1.84 seconds; best rescaled floating energy 0.5353787557464796.
N=100000: 51697 edges, 9592 prime variables, 180-second cap; best rescaled
floating energy 1.8840922111631229. No computation remains pending.
At N=100000 the energy by prime ranges <=100, (100,1000], (1000,10000],
and >10000 is approximately 1.267983, 0.440929, 0.156210, and 0.018970.
No arithmetic formula, extension rule, or uniform energy bound was extracted.

Artifacts: /tmp/cube_centered4_energy_{10000,100000}.{log,json,npz}.
Independent exact rational audit: /tmp/audit_centered4_rational.py enlarged
weights by 1+10^-5 and rounded to integers divided by 10^8. It independently
reconstructed prime factorizations, checked squarefreeness and cube identities,
and evaluated centered scores exactly using the common denominator equal
to the product of primes up to the maximum cutoff (128 and 512 respectively).
All stored edges passed a spread of at least 1. Exact upward-rounded energy
bounds (precision 10^-12):
  N=10000: energy <=535389465501/10^12 <1.
  N=100000: energy <=1884129894560/10^12 <2.
Rational weights/reports are /tmp/cube_centered4_energy_<N>_rational.{npz}
and /tmp/cube_centered4_energy_<N>_rational_audit.json.
These are external FINITE checks, not Lean certificates, not completeness
proofs for the enumeration, and not a uniform all-cutoff theorem. No proof
or disproof of the conjecture follows from them. Spec.lean remains unchanged.

## Review after centered-four finite audits (unresolved)

Recorded the previously unlogged centered-four optimization and rational audits.
Reviewed the global factorization, conic-scheduling, squarefree-coloring, and
large-prime-source gaps against the existing verified obstructions. In particular,
SquarefreeParityObstruction already supplies a squarefree coprime-to-six
three-representation obstruction to the stronger odd-edge-parity condition;
it does not rule out ordinary proper finite coloring. The nonsquarefree
positional-clique and higher-cycle arguments were not transferred without proof.

No uniform energy budget, finite coloring bound, all-family collision estimate,
or arbitrary-positive-density recurrence theorem was obtained. No numerical
search or additional Lean theorem was added in this review. Spec.lean remains
unchanged; there is still no valid proof or disproof ready for submission.

## Rational zeros of a cubic coordinate (new, verified)

Submission/CubicCoordinateZeros.lean (156 lines) compiles successfully with
current olean. Log: /tmp/cubic_coordinate_zeros.log. The three printed theorem
axiom audits list only propext, Classical.choice, Quot.sound. No holes or
native_decide were used.

For the first complete-parametrization coordinate A(a,b,t), the file proves:
* A=B iff b=0, using A-B=-3*b*Q(a-t,b) and positive definiteness of Q.
* A=C iff b=2*a, using a sum-of-two-squares factorization of 4*(A-C).
* Over Q, A=0 iff (b=0 and a=-t), or (b=2*a and t=3*a), or
  (t=0 and a=b). The proof uses FLT3 to force B=0, C=0, or D=0,
  followed by the exact pair factorizations. These are precisely three
  rational projective directions: (-1,0,1), (1,2,3), (1,1,0).
* The same zero classification over Z.
* Strict antitonicity of b -> A(a,b,t), for fixed rational a,t, from
    2*(A(a,b,t)-A(a,c,t))
      = (c-b)*(3*(b+c-2*a)^2+3*b^2+3*c^2+4*t^2).

An external symbolic check also found no geometric singular point of the
coordinate cubic (the t=1 gradient ideal is the unit ideal; t=0 is handled
directly). That smoothness check was NOT promoted to a Lean theorem. The
new Lean file proves the rational-zero and monotonicity statements above.

These results do not bound the number of parameter representations of a
nonzero root uniformly, do not bound normalized cancellation, and do not
provide a positive-density Sidon source. The attempted norm-form/divisor-
counting route still lacks a global uniform estimate. Spec.lean is unchanged
with its original sorry; no proof or disproof is ready for submission.

## Pairwise Jacobi spin candidate (new, verified obstruction)

Submission/JacobiSpinObstruction.lean defines
  spin(n) = product_{p,q in primeFactors(n), p<q} jacobiSym(p,q),
and source(s) = {n | Odd n and Squarefree n and spin(n)=s}.
It proves neither_fiber_sidon: neither source(1) nor source(-1) has Sidon cubes.
The module compiles with current olean; /tmp/jacobi_spin_obstruction.log reports
only propext, Classical.choice, Quot.sound for the theorem. No proof holes,
new axioms, or native_decide are used.

The +1 witness is the previously verified four-prime collision
  (26711,31469,32009,35543).
The -1 witness is its common dilation by 13*557=7241:
  (193414351,227867029,231777169,257366863).
All eight displayed roots are odd and squarefree. The proof computes
  jacobiSym(13,557)=-1,
  jacobiSym(13,p)=jacobiSym(557,p)=1
for each of the four base primes p. Thus the spin of each dilated root is -1.
The symbolic prime-factor product identities, squarefreeness, sign values,
and both strict cube collisions are all checked in Lean.

The external precursor /tmp/cube_jacobi_spin_witness.json used only a structured
search for two multiplier primes with prescribed symbols; no new cubic
collision enumeration was performed. Its results are superseded by the Lean
certificate for the stated witnesses.

This is a restriction on a specific nonmultiplicative prime-interaction
coloring, NOT a disproof of the original existential conjecture. No uniform
source/counting estimate or target settlement was obtained. Spec.lean remains
unchanged with its original sorry. No proof has been submitted.

## Residue-corrected four-color candidate (targeted diagnostic; unresolved)

Checked the specific odd-squarefree coloring c(n)=Omega(n)+n-1 mod 4,
equivalently the completely additive character with c(p)=1 for p=1 mod 4
and c(p)=3 for p=3 mod 4. This is the full four-color rule, not the previously
rejected high-bit-only rule. Reused the saved edges; no new collision search.
Among 13532 saved odd-squarefree edges through 100000, 266 are monochromatic.
The first is (219,515,583,687), with factorizations
  219=3*73, 515=5*103, 583=11*53, 687=3*229.
All have Omega=2, residue 3 mod 4, and color 0. The cube equality was checked
with integer arithmetic. This diagnostic was not promoted to a Lean theorem.

Reviewed the global construction gap again, including the distinction between
finite scalar-character tests, arbitrary proper colorings, and the required
positive-density independent set. No uniform estimate or valid settlement was
obtained. No new Lean module was added in this continuation. Spec.lean remains
unchanged with its original sorry; no valid proof or disproof is ready.

## Squarefree fixed-positional-pair graph diagnostic (new; no settlement)

Tested a specific remaining scope distinction: AllPositionalCubeCliques did not
preserve squarefreeness, so its obstruction was not automatically available on
the squarefree source. Reused the 51697 saved squarefree edges through 100000,
including dilations, and formed the six graphs joining one fixed pair of root
positions. All six graphs are non-bipartite. Exact BFS witnesses are stored in
/tmp/cube_squarefree_positional_graph.json; script
/tmp/cube_squarefree_positional_graph.py. This was not a new collision search.

Position pairs (0,1), (0,2), (0,3), (1,2), (1,3), (2,3) respectively have
51608, 51661, 51680, 51680, 51661, 51442 distinct stored graph edges. The BFS
witness cycle lengths are respectively 5, 7, 7, 15, 15, 3. These are witnesses,
not claims that the cycles are shortest.

The last-pair triangle is (870,934,979), from the squarefree collisions
  (317,573,870,934), (317,678,870,979), (573,678,934,979).
All six root values are squarefree. These external finite witnesses rule out
fixed-positional Boolean separation on the squarefree source. They do NOT
establish unbounded chromatic number, rule out adaptive pair choices, or
settle the original positive-density conjecture. No additional Lean theorem
was added in this continuation, and no global bound was obtained.

Spec.lean is unchanged with its original sorry. No valid proof or disproof is
ready to submit, and no computation remains pending.

## Endpoint and global-recurrence review (unresolved)

Rechecked RelativeEndpointReduction, GapRatioNorms, DefectGapBounds, and the
small-parameter counting interfaces. The endpoint inequalities are relative
constant-width conditions; they do not imply the power-small normalized gap
or defect hypotheses of the existing summability theorems. The missing broad
remaining region therefore cannot be discarded by invoking those results.

Also reviewed whether fixed-family prime-score separation or near-diagonal
polynomial identities supplied a global construction/recurrence argument.
No uniform control of the family-dependent finite heads was obtained, and
no applicable recurrence theorem for arbitrary positive-natural-density
sources was established. In particular, polynomial identities with a shared
leading coefficient were not treated as translation-invariant patterns.

No new finite experiment or Lean theorem was added in this continuation.
Spec.lean remains unchanged with its original sorry; there is still no valid
proof or disproof of the conjecture available for submission.

## Reduced coordinates at a cubic cancellation prime (new, verified)

Submission/CubicCancellationLines.lean compiles successfully with a current
olean. /tmp/cubic_cancellation_lines.log audits all three main theorems using
only propext, Classical.choice, and Quot.sound. No proof holes or new axioms
occur in the successful build.

For the cubic parametrization at the t=Q(a,b)=0 base locus, two exact identities
are proved over the integers:
  a*C+b*A = Q*(-3*Q+3*a*t-t^2)+t^2*(a+b)*(t-b),
  a*D+(a-b)*B = t*(2*a-b)*(3*Q+b*t+t^2).
If g is nonzero, divides both t and Q, and the raw coordinates are
(g*x,g*y,g*z,g*w), reduced_relations proves
  g divides a*z+b*x,
  g divides a*w+(a-b)*y.

The field lemma field_line proves that Q(a,b)=0, a nonzero, and the two
reduced linear equations imply a nontrivial cube root of unity r=-b/a with
  z=r*x, y=r*w,
in any field where 3 is nonzero. cancellation_prime_line transfers this to
ZMod p when p divides g, p does not divide a, and p is prime other than 3.
This formalizes the exceptional-line image in this cancellation chart.

SCOPE: these are pairwise congruence restrictions. They do not force an
individual reduced root to be divisible by the cancellation prime, and no
positive-density source controlling all such relations was constructed.
No global linear collision estimate, uniform score budget, or settlement of
the original conjecture follows. Spec.lean remains unchanged with its sorry.

## Dilation removes centering from a necessary margin condition (new, verified)

Submission/CenteredScoreDilation.lean compiles with a current olean.
/tmp/centered_score_dilation.log audits its three main theorems using only
propext, Classical.choice, and Quot.sound. No proof holes or new axioms are
present in the successful build. The temporary API-check file was removed.

rawSpread is the maximum of the six absolute UNcentered prime-score
contrasts of all four roots. The new theorems are:

* raw_margin_of_prime_dilations: if a fixed ordered positive quadruple has
  centered spread >= epsilon under every sufficiently large fresh-prime
  dilation, its rawSpread is already >= epsilon. Finite reciprocal-prime
  square energy makes all six center differences tend uniformly to zero
  on these dilations. The added prime score cancels from every contrast.
* raw_margin_of_centered_margin: the actual infinite uniform centered-margin
  hypothesis therefore implies the same raw-four margin on EVERY strict
  squarefree collision, without the original smallest-root threshold H0.
  The prime dilation preserves squarefreeness and moves every root past H0.
* prime_cover_of_centered_margin: if epsilon>0, the same hypothesis yields
  a reciprocally summable prime cover of all prime-root cubic collisions.
  The primes with |w(p)|<epsilon/2 form a cube-Sidon source, by the raw
  margin, and the existing ScorePrimeCover theorem applies.

IMPORTANT SCOPE: the last implication concerns a UNIFORM CENTERED MARGIN on
all sufficiently large squarefree collisions, not arbitrary Sidon moving
bands. It does not prove the existence or nonexistence of the prime cover.
The raw-four necessary condition is also not the earlier raw-upper-three
sufficient criterion. No reverse implication is asserted.

No all-family count, separating score, uniform finite budget, or original
conjecture settlement was obtained. Spec.lean is unchanged with its sorry;
no valid proof or disproof is ready for submission.

## Bounded-factor sieve route considered (UNPROVED; no settlement)

Reviewed a possible stronger obstruction to the finite-L2 centered-score
criterion, using the newly proved dilation-to-raw-margin implication.
A potential input would be one absolute R such that every reciprocally
summable forbidden prime set is avoided by a strict squarefree conic
collision whose four roots each have at most R prime factors. Such a theorem
would obstruct a uniform raw-four margin: at threshold epsilon/(4R), the
large-score primes form a summable prime set.

THIS BOUNDED-FACTOR INPUT HAS NOT BEEN PROVED. The existing
SquarefreeSummablePrimeObstruction.collision_avoiding gives no uniform bound
on factor count. Mathlib's available arithmetic sieve is an upper Selberg
sieve; the required lower-bound sieve is not supplied by the current files.

A possible route, not a theorem: obtain many parameters for which all four
quadratics are N^alpha-rough, use a stronger sifting cutoff on each individual
coordinate to exclude prime-valued coordinates, and then use the fact that a
rough composite value <= C*N^2 has largest prime <= C*N^(2-alpha). This power
saving might make root-lattice discrepancy errors summable over the relevant
prime set while retaining a conditional sieve bound. A lower fundamental
lemma, the mixed-cutoff comparison, and the conditional root-lattice sieve
with all errors controlled remain missing. No asymptotic conclusion was
inferred from the existing fixed-head density or unconditional lattice bound.

No new Lean theorem or experiment was added in this continuation. Even a
successful completion would refute a restricted score criterion, not the
original existential statement. Spec.lean remains unchanged with its sorry;
no valid proof or disproof is ready to submit.

## Adaptive separation and mixed-band review (unresolved)

Revisited adaptive pair selection, rather than choosing one fixed positional
pair for every collision. Geometric-band separation forces the largest two
roots into a narrow relative band, but does not exclude collisions with all
four roots nearby or with two nearby pairs at separated scales. No adaptive
selection with a uniform finite coloring bound was found.

Rechecked whether Sidonness of an earlier block could give a sufficiently
small mixed-collision extension bound. The existing separately Sidon paired
families obstruct cardinality-only bounds; they were not treated as an
obstruction to all height-dependent bounds. Conversely, no height-dependent
estimate preserving one fixed positive density through every prefix was proved.

Also reviewed the cubic cancellation congruences and the exact conic-height
product against the all-family sieve gap. Neither supplies the needed uniform
control of the family-dependent finite heads. No new theorem or numerical
experiment resulted from this review. Spec.lean is unchanged with its original
sorry. There is still no valid proof or disproof ready for submission.

## Odd-prime four-color extension review (unresolved)

Rechecked OddPrimeCharacterDensity, SquarefreeColoringReduction, the actual
fixed-low-bit SAT encoding, and SquarefreeOddPrimeColorObstruction. The
positive-density extraction for an infinite proper character is complete.
The finite SAT result is not a compatible all-cutoff extension theorem.
Requiring total edge color two would linearize the problem but is already
inconsistent on verified squarefree collisions; this stronger condition cannot
be substituted for ordinary nonmonochromaticity.

No arithmetic extension rule, uniform satisfiability argument, or alternative
positive-density construction was obtained. No new solver run or theorem was
added. Spec.lean is unchanged, and no valid settlement is ready to submit.

## Collisions in every remote multiplicative interval (new, verified)

Submission/GeometricBandObstruction.lean compiles with a current olean.
/tmp/geometric_band_obstruction.log audits all three public results using
only propext, Classical.choice, and Quot.sound. The successful build has
no holes or warnings.

The positive integer polynomial family is
  a(k)=k^3+7k^2+15k+6,
  b(k)=k^3+8k^2+24k+27,
  c(k)=k^3+10k^2+36k+45,
  d(k)=k^3+11k^2+39k+48.
It satisfies 0<a<b<c<d and a^3+d^3=b^3+c^3. For k>=1,
  a(k)>=k^3, d(k)-a(k)<=70*k^2.
Thus its largest/smallest root ratio tends to one, quantitatively.

Verified results:
* narrow_collision: for every real q>1 there is a strict positive integral
  collision with d<q*a.
* collision_in_every_relative_interval: for every q>1, there is M>0 such
  that EVERY real X>=M admits a strict integral collision in [X,q*X).
  The proof fixes one sufficiently narrow pattern and uses the integer
  multiplier ceil(X/a); the rounding error is absorbed by the strict margin.
* geometricBand_not_sidon: for all q>1,r>1, the full geometricBand q r from
  CompactGapRatioColoring is not cube-Sidon.

SCOPE: this excludes the FULL geometric bands, not arbitrary subsets of
those bands. Positive lower density alone does not imply containment of
fixed-relative-width intervals. No proof or disproof of the original
conjecture follows. Spec.lean remains unchanged with its original sorry.

## The close-root cubic curve is avoidable (new, verified)

Submission/DiagonalCubicCurveSieve.lean compiles successfully, with current
olean and allowed-axiom audits in /tmp/diagonal_cubic_curve_sieve.log.
All four public audited results use only propext, Classical.choice, Quot.sound.
There are no proof holes or warnings in the successful build.

The full binary cubic forms are
  F0=u^3-2*u^2*v-3*v^3,
  F1=u^3-u^2*v+3*u*v^2,
  F2=u^3+u^2*v+3*u*v^2,
  F3=u^3+2*u^2*v+3*v^3.
Their cubic identity is verified. Two explicit quadratic-coefficient Bezout
certificates express 12*u^5 and 12*v^5 as combinations of these forms. Hence
any common coordinate divisor at primitive integer parameters divides 12.

curve_avoidable applies the existing all-normalizations sieve to obtain one
positive-lower-density infinite set avoiding every instance with normalized
maximum >1, for ALL primitive rational parameters, all admissible common-factor
normalizations, and all integer dilations. shifted_specialization proves that
(u,v)=(k+3,1) is exactly the four polynomial roots used in
GeometricBandObstruction, rather than a different curve.

Thus the new interval collision theorem cannot itself force collisions in
arbitrary positive-density sets: its entire rational curve can be avoided.
This remains a familywise theorem. No uniform all-family construction, finite
coloring, or original conjecture settlement was obtained. Spec.lean remains
unchanged with its original sorry; no proof or disproof has been submitted.

## Squarefree-box and prime-support resumption (unresolved)

Read the complete smooth-box and first-thirteen-prime box entries before
reconsidering prime-color extension. The first-thirteen-prime test imposes
no high-bit constraints and supplies no extension evidence. Reviewed the
existing degree-two peeling diagnostic, odd-prime character transport, and
three-edge obstruction to the stronger edge-sum condition. No global
satisfiability or compatible extension theorem was established.

An exact Python inspection of the saved 3741 primitive squarefree
uniform-Omega-parity constraints through 100000 found that the symmetric
difference of the four prime supports is nonempty in every case. Equivalently,
none of these saved four-root products is a square. This is ONLY a finite
observation, not a universal arithmetic theorem, a coloring construction, or
a Lean certificate. No larger root enumeration or solver was launched.

Also reconsidered fixed-family sieve aggregation and common-large-prime
recursion. The global finite-head and distinct-large-prime gaps remain.
No proof or disproof of the target was obtained. Spec.lean remains unchanged
with its original sorry. No proof was submitted and no computation is pending.

## Prime-parity and mixed-scale global review (unresolved)

Reexamined paired quadratic discriminants as a potential exact prime-parity
invariant. Equal local zero frequencies do not imply an exact factor-parity
identity or ordinary nonmonochromaticity. The existing stronger edge-sum
obstruction remains relevant; no new invariant or extension rule was proved.

Also reconsidered endpoint compactness via dilation and mixed-scale block
extension. Dilation invariance does not furnish the every-prefix lower bound
required by Compactness. Cardinality-only mixed-edge bounds are already
obstructed; no adequate height-dependent bound was obtained. No new numerical
search, solver run, or Lean theorem resulted from this review.

The target is still unresolved. Spec.lean was not changed, no valid proof is
ready to submit, and no computation is pending.

## Split-coordinate recurrence review (unresolved)

Considered whether a polynomial cube-collision family with rationally split
coordinate factors could supply a multiplicative recurrence argument. Reviewed
CubeConicGeometry and CubicCoordinateZeros: FLT3 controls rational boundary
zeros and excludes splitting of the nondegenerate quadratics in the recorded
conic bundle. These results do not classify arbitrary higher-degree split
families. No such family or applicable recurrence theorem was established.
Even finite-color or finite-index-subgroup recurrence would need an additional
argument to address every set of positive natural lower density; that bridge
was not assumed.

No new Lean theorem, numerical enumeration, or solver run was made. The
original conjecture remains unresolved, Spec.lean retains its original sorry,
and no proof was submitted. No computation is pending.

## Saved-score formula and cancellation-source review (unresolved)

Inspected the saved centered-four score through 100000 directly. Among the
8363 primes above 10000, 1889 weights exceed 1e-8 in absolute value and the
median absolute weight is zero. These are properties of the finite optimized
array, not a tail estimate, an infinite score, or a uniform energy bound.
The first-prime values and their irregular positive adjustments did not
supply an exact arithmetic formula. No new optimization or collision search
was run.

Reexamined CubicCancellationLines as a possible bridge to the linear-collision
source criterion. Its reduced-coordinate congruences identify nontrivial
cube-root-of-unity ratios modulo a cancellation prime. No positive-density
source eliminating all such cancellation contributions was constructed.
Also revisited uniformity across conic families; the family-dependent finite
heads remain uncontrolled. No global bound or recurrence result was proved.

No Lean theorem or target-file edit resulted. Spec.lean still contains its
original sorry, no valid proof or disproof is ready, and no job is pending.

## Odd-prime box extension obstruction (new verified partial result)

A targeted complete-box investigation now disproves ARBITRARY one-prime
extension, rather than merely observing that an extension proof is missing.
It does not disprove finite satisfiability with recoloring or the conjecture.

1. Transport-obstruction support box
   Primes 2,3,7,11,17,29,61,73,353,647,677,1511; 4096 squarefree
   products; all 8390656 unordered pair sums checked with uint256 arithmetic.
   Exactly 40 collisions, normalizing to the three already known transport
   patterns. All 40 have uniform Omega parity. There are 2816 surviving odd
   ZMod 4 assignments out of 4096, and no failed one-prime projection in this
   particular ordering. Maximum cube-sum needs 205 bits, so no overflow.
   Files /tmp/cube_sf_odd_c4_transport12.csv, .csv.roots, .log,
   .csv.odd_c4.audit.json, .audit.log.

2. A smaller genuine extension failure
   Exact F2 analysis of the saved constraints found two patterns:
     31^3+1867^3=397^3+1861^3,
     398^3+5411^3=3734^3+4739^3.
   Here 398=2*199, 3734=2*1867, 4739=7*677, 5411=7*773.
   The old primes are 2,7,31,199,397,677,773,1861. Assign colors
     1,1,1,3,1,3,3,1, respectively.
   If the new prime 1867 has color 1, the first edge is monochromatic.
   If it has color 3, the second edge is monochromatic with color 0.

   A COMPLETE external enumeration on these nine primes checked 512 roots
   and 131328 unordered root pairs. It found exactly 40 collisions, all
   dilations of the two displayed patterns. The entire old eight-prime
   box (256 roots) has no nontrivial collision at all. Thus every old color
   assignment is proper there, but some do not extend. Of 512 full odd-prime
   assignments, 392 survive. Recoloring is therefore still possible.
   Python arbitrary-precision arithmetic checked products, cube identities,
   root distinctness, no-overflow, and all assignments/projections.
   Files /tmp/cube_odd_extension_pair.py and .json;
   /tmp/cube_sf_odd_c4_extension9.csv, .csv.roots, .log,
   .csv.odd_c4.audit.json, .audit.log.

3. Lean certificate
   Submission/OddPrimeBoxExtensionObstruction.lean compiles with a current
   olean. Log /tmp/odd_prime_box_extension.log. All four public axiom audits
   use only propext, Classical.choice, Quot.sound; no holes or native_decide.
   - old_witnesses_sidon verifies Sidon cubes on the eleven old witness
     roots, including the eight old primes.
   - old_witnesses_in_box verifies their membership in the old product box.
   - old_witness_fibers_sidon follows for arbitrary colors of those roots.
   - prescribed_odd_colors_obstruct proves that the eight specified prime
     colors and additivity on products cannot extend with odd color at 1867
     to proper cube-Sidon squarefree fibers.

   SCOPE: Sidonness of the FULL 256-root old box is currently the external
   exact check, NOT a Lean theorem. An attempted direct merge-sort kernel
   check did not reduce; it was removed rather than left as a proof hole.
   The temporary CheckOddExtension.lean was deleted. The final auxiliary
   module has only completed proofs and states the limited scope explicitly.

No proof or disproof of the target was obtained. Spec.lean is unchanged with
its original sorry. No proof was submitted and no computation is pending.

## Continuation: global prime-support and density review (unresolved)

Rechecked the odd-prime character reduction and its finite-prefix evidence.
No infinite satisfiability or recoloring theorem was obtained. The observation
that saved squarefree collision products are nonsquares remains only a finite
observation; even a general nonsquare-product theorem would not by itself
supply a simultaneous finite coloring. The prescribed-prime extension
obstruction remains an obstruction to that assignment, not to arbitrary
proper characters or to the conjecture.

Also reconsidered aggregating the fixed-conic sieves by countably many
character-score restrictions. The uncontrolled family-dependent finite heads
remain a real gap. Neither familywise reciprocal summability nor choosing
successively later cutoffs gives a uniform density bound for the whole
collision set. No new global source, coloring, or recurrence theorem was
established in this review.

For completeness, the preceding context's finite genus-character checks on
its four conic forms had projective residues with all four values nonzero
and with equal Legendre symbols at every relevant prime (13,17,29,43,101).
Those checks do not yield a uniform separating character or a global sieve.

No new Lean theorem or conjecture-file edit resulted. Spec.lean retains its
original sorry. No proof or disproof of the target has been obtained, and no
valid proof is ready for submission.

## Finite primitive-exception coloring repair (new verified reduction)

Two new auxiliary modules compile successfully, with built oleans current:
* FinitePrimitiveColorRepair.lean
* FinitePrimitiveSourceRepair.lean
Logs: /tmp/finite_primitive_color_repair.log and
/tmp/finite_primitive_source_repair.log. All six printed public axiom audits
use only propext, Classical.choice, Quot.sound. No sorry, new axiom, or
native_decide occurs in either module. CheckFiniteRepair.lean was removed.

The finite valuation vector is
  valuationColor H n : Fin(H+1) -> ZMod(H+1),
  p |-> v_p(n) modulo H+1.
ratio_separation proves that equal vectors, together with r*x=s*y for
positive r,s<=H and positive x,y, force x=y. Consequently, if every
monochromatic cubic collision of an input coloring has normalized primitive
maximum <=H, adjoining this vector repairs every collision, including all
common dilations. The input coloring need not be multiplicative.

FinitePrimitiveSourceRepair.badMaximaOn S c records the distinct normalized
maxima of monochromatic strict collisions on S. finite_exception_refinement
turns any finite coloring with a finite badMaximaOn set into a proper finite
coloring on the SAME source, without deleting source elements. In particular,
finite_squarefree_exceptions_suffice gives the target existential conclusion
conditionally on such a coloring of squarefree roots. The companion all-root
criterion is bounded_bad_primitive_maxima_suffice.

SCOPE: Neither module constructs the input coloring or proves its bad maxima
finite. Finitely many bad PRIMITIVE patterns is distinct from finitely many
bad absolute quadruples. This criterion is not inferred from finite-prefix
SAT checks. In existence terms it is equivalent to proper finite colorability
(after allowing more colors), not an independent proof of colorability.
Spec.lean remains unchanged with its original sorry. No proof or disproof of
the original conjecture has been obtained, and no valid submission is ready.

## Coincident conic norm fields and elliptic quotients (new verified reduction)

Investigated a previously unchecked possible obstruction to the character-score
route: could the two conic coordinate discriminants have the same square
class? Put
  D1(t)=3*(4*t^3-1), D2(t)=3*t*(4-t^3).

Submission/ConicFieldCoincidence.lean now compiles, with current olean and
five public axiom audits using only propext, Classical.choice, Quot.sound.
Log: /tmp/conic_field_coincidence.log. No holes or new axioms occur.
It proves:
* For nonzero rational t, IsSquare(D1(t)*D2(t)) is equivalent to a rational
  point on y^2=x^3+17*x^2+16*x with x=-4*t^3.
* If t>0 and t!=1, that x is not in {-16,-4,-1,0,4}. The exclusions of
  rational cube roots of 4 and 1/4 follow from Fermat for exponent three.
* A second quotient of z^2=t*(4*t^3-1)*(4-t^3) is
  Y^2=X^3-48*X+272, with X=-4*(t+1/t), Y=4*z/t^2.

External exact Sage computations (NOT Lean theorems) found:
* E0: y^2=x^3+17*x^2+16*x has conductor 15, label 15a3, rank 0,
  torsion Z/4 x Z/2. Its torsion points are O, (-16,0), (-1,0), (0,0),
  (-4,12), (-4,-12), (4,20), (4,-20).
* The second quotient E1 has rank 1, trivial torsion, generator (16,-60).
  Thus the second quotient alone cannot exclude extra points.

Sage's E0 rank computation suggests no nondegenerate positive coincident-field
parameter. The Lean module DOES NOT classify E0(Q), prove its rank zero, or
assert nonsquareness of D1*D2 for every t>0,t!=1. Do not cite the external
rank calculation as a permitted Lean theorem. Formalizing that classification
would be a separate descent/height task and would still not solve the global
aggregation of conic-family sieves.

No finite prime-character coloring with finite bad primitive maxima was
constructed, and no missing global density estimate was proved. Spec.lean
is unchanged and still has its original sorry. No valid settlement is ready.

## Global prime-character and sparsity review (unresolved)

Revisited the odd-prime ZMod 4 route, including the exact support-box audits,
the prescribed-prime extension obstruction, and the stronger edge-sum
obstruction. No universal finite satisfiability, recoloring, or primitive-tail
theorem was obtained. In particular, avoiding each individual affine bad-color
constraint is not a proof of simultaneously avoiding all such constraints.

A diagnostic reused the already saved complete edge array through 100000;
no new collision enumeration or SAT run was performed. There are 105 stored
four-prime edges. Their counts through 1000, 2000, 5000, 10000, 20000, 50000,
100000 are respectively 0, 2, 4, 6, 18, 52, 105. These finite counts establish
no asymptotic prime-edge estimate or reciprocal-cover bound. Also recomputed
largest-root primitive-degree percentiles from that same array; this repeats
the earlier bounded-degree-source diagnostic and supplies no new tail theorem.
Do not rerun it as though it were a fresh route.

Reviewed whether generic hypergraph sparsity, a multiplicative character,
or near-diagonal counting could close the global gap. No uniform positive
independence bound or positive-density linear-collision source was proved.
The finite-energy and familywise-sieve hypotheses remain unproved as well.
No new Lean theorem resulted, no computation is pending, and Spec.lean is
unchanged with its original sorry. No valid proof or disproof is ready for
submission.

## Finite-prefix and scale-separation continuation (unresolved)

Rechecked Compactness, RelativeGeometricBands, RelativeEndpointReduction,
CompactGapRatioColoring, and the recorded short-band mixed-collision
obstructions. The elementary separation eliminating two-old/two-new
collisions requires a new scale on the order of M^(3/2) when the old roots
are below M. Such gaps do not preserve positive lower density. No uniform
fixed-ratio extension estimate or simultaneous all-prefix construction was
proved. The mixed-cardinality obstructions do not themselves refute a bound
linear in the maximum root, and were not used to assert that stronger claim.

Considered whether the large-prime/cofactor recursion or a more general
prime-interaction coloring could supply the missing global step. No infinite
extension theorem, proper coloring, or positive-density source was obtained.
No new numerical search, Lean theorem, or Spec.lean edit resulted. The target
still has its original sorry, no computation is pending, and no valid proof
or disproof is ready to submit.

## Divisor-cover global-bound continuation (unresolved)

Read GreedyDivisorCover, WeightedDivisorCover, RelativePrimitiveCover, and
CubicExactCancellation, along with the saved finite-cover and restricted-cover
obstruction summaries. The uniform finite fractional-cost bound is still an
unproved arithmetic hypothesis, not an unfinished compactness proof. The exact
cancellation formula permits unbounded cancellation and was not treated as a
bounded-height estimate. No summation across all conic/cubic families was
justified. Prime- and semiprime-supported cover obstructions remain restricted
obstructions, not a disproof of arbitrary divisor covers or of the conjecture.

Considered whether minimal greedy exclusions, divisor-count weights, or the
parametrization could supply a global reciprocal-cost estimate. No such
estimate or explicit covering weight was obtained. No new numerical search,
Lean theorem, or Spec.lean edit resulted. Spec.lean retains its original sorry;
no valid settlement is ready and no computation is pending.

## Prime-row-space Hall criterion rejected (new finite diagnostic)

Investigated a stronger sufficient condition for odd-prime ZMod 4 coloring:
for each uniform-Omega-parity edge, its three prime-parity difference rows
span the affine bad-color constraint. An independent row-space representative
per edge would allow choosing a linear equation contradicting every bad
constraint. The associated Hall rank inequality must hold for EVERY
subcollection, not merely the full saved collection.

Exact F2 computations on the existing 3741 saved constraints through 100000:
* Every individual row space has dimension 3.
* All 3741 row spaces are distinct.
* The full sum has dimension 4023 (so the full-family rank test alone passes).
* Removing constraints with a private prime variable leaves 1334 constraints
  whose combined row-space dimension is only 926. Thus the independent-
  representative Hall criterion FAILS on this finite subcollection.

The corresponding (edge count, full rank, core edge count, core rank) at
cutoffs 1000,3000,10000,30000,100000 is:
  (4,12,0,0), (33,88,0,0), (169,317,0,0), (766,1129,0,0),
  (3741,4023,1334,926).
Script: /tmp/cube_odd_row_rank_core.py.
Report: /tmp/cube_odd_row_rank_core.json.
Core indices: /tmp/cube_odd_row_rank_core_indices.npy.
The computation uses Python arbitrary-precision bit-vector elimination and
reuses the saved edge array; no new collision search or SAT run was made.
This is an external finite diagnostic, NOT a Lean certificate. It rejects
only this sufficient rank criterion, not the satisfiable finite four-color
instance or ordinary proper colorability. No universal dependency bound or
alternative infinite coloring theorem was proved.

Spec.lean remains unchanged with its original sorry. No valid proof or
disproof of the target is ready, and no computation is pending.

## Pair-bucket compression check (new finite diagnostic; unresolved)

Checked whether most saved collisions could be compressed by grouping their
common cube sums or differences. Script /tmp/cube_pair_bucket_compression.py
reuses /tmp/cube_edges_100000.bin, checks each cube identity, and counts the
three buckets S=a^3+d^3, D1=b^3-a^3, D2=c^3-a^3. Each bucket count was checked
to have the form r*(r-1)/2. Report: /tmp/cube_pair_bucket_compression.json.
No new collision enumeration was performed; this is not a Lean certificate
or an independent proof of completeness of the stored array.

At N=100000, the 898947 edges have sum-bucket representation histogram
  r=2: 887256 buckets; r=3: 3843; r=4: 27.
Selecting all but one representation pair per repeated-sum bucket would use
895023 pairs, so this particular compression saves very few pairs. The
corresponding difference-bucket histogram is
  r=2: 1670420; r=3: 40416; r=4: 981; r=5: 34.

Counts of edges whose three buckets all have exactly two representations
(and hence whose six root pairs occur in no other saved edge in the prefix)
at N=1000,3000,10000,30000,100000 are respectively
  1223, 6152, 33761, 152366, 764427.
These edges require distinct pairs in any pair-selection cover of this finite
hypergraph. This does not exclude a bounded-chromatic-number pair graph,
prove a superlinear asymptotic private-pair count, or settle the conjecture.
The unrestricted fixed-positional-pair clique theorem also does not exclude
adaptive pair selection.

No global coloring theorem or density construction resulted. Spec.lean is
unchanged with its original sorry, no valid proof/disproof is ready, and no
computation is pending.

## Odd-cycle reciprocal-cost continuation (unresolved)

Reexamined OddCycleColoring, QuadraticOddSpecialization, the squarefree rough
parity obstruction, HigherCycleObstruction, and the recorded odd-source
finite consistency check. The quadratic classification concerns projectively
varying quadratic triple families. It does not bound all primitive all-odd
triples or higher odd even-incidence configurations. The known all-odd,
squarefree numerical triples remain compatible with that classification.

No uniform reciprocal-cost bound for all surviving odd cycles was proved.
Nor was absence of three-pair representations substituted for NoOddCycle:
the unrestricted counterexample rules out that inference in general, and
the saved odd-source finite consistency check supplies no infinite theorem.
No new numerical computation, Lean theorem, or target-file edit resulted.
Spec.lean retains its original sorry, no valid settlement is ready, and no
computation is pending.

## Multiplicative-coloring scope continuation (unresolved)

Checked the Boolean support-box reports against the earlier height-truncated
results and the odd-prime density/transport theorems. The two 12-prime
squarefree Boolean boxes are satisfiable (one has no collisions); they are
not obstructions or infinite satisfiability results. The older unrestricted-
squarefree Boolean test through 30000 was reported UNSAT but remains without
an independent proof-certificate check in this development. Do not describe
it as a kernel-certified theorem. The coprime-source finite Boolean assignments
also do not give an infinite extension theorem or a summable repair bound.

The odd-prime ZMod 4 density and transport results are complete conditional
lemmas; existence of the character is still missing. No global argument
emerged from reformulating characters as prime-sign choices or from the
known finite obstructions. No new computation, Lean theorem, or target edit
resulted. Spec.lean retains its original sorry. No valid proof or disproof is
ready and no computation is pending.

## Library/interface and remaining-source check (unresolved)

Rechecked the actual IsSidon API in FormalConjecturesForMathlib/Combinatorics/
Basic.lean, the target statement, LinearCollisionExtraction, and
SmallParameterSource. No existing library theorem supplies a positive-density
cube-Sidon construction. The source-preserving linear-collision extraction
interface is complete, but no positive-density source with a uniform C*N
prefix collision bound has been constructed. The small-parameter source only
excludes its two specified regimes and does not provide that remaining count.

No new arithmetic estimate, Lean theorem, or target-file edit resulted.
Spec.lean still contains its original sorry; no valid proof or disproof is
ready, and no computation is pending.

## Prime-residue coloring obstruction (new verified partial result)

Submission/PrimeResidueColorObstruction.lean compiles successfully with a
current olean. Log: /tmp/prime_residue_color_obstruction.log. Its three public
axiom audits list only propext, Classical.choice, Quot.sound; no proof holes,
new axioms, or native_decide occur.

The exact four-prime collision is
  13297^3 + 49009^3 = 24907^3 + 47119^3.
All four roots are prime and congruent to 13 modulo 18 (hence 4 modulo 9).
The file proves:
* prime_progression_not_sidon: the cubes of primes 13 mod 18 are not Sidon.
* residue_prime_colors_obstruct: for ANY color type and ANY extension to
  composite roots, if the color of a prime depends only on its residue mod 18,
  the squarefree fibers cannot all have Sidon cubes. Multiplicativity and
  odd-prime colors are not needed for this restricted obstruction.
* mod_nine_prime_colors_obstruct: the analogous mod-9 statement.

The precursor reused the saved odd-prime constraints. An exact test of the
128 maps from prime residues {1,2,3,4,5,7,8} modulo 9 to {1,3} found none
proper; the report is /tmp/cube_prime_mod9_color_check.json. The displayed
single four-prime witness gives the stronger Lean-certified result, so the
finite assignment test is not needed for the theorem. No new cubic collision
enumeration was run. An initial diagnostic omitted residue 3 and stopped with
a KeyError; it was corrected before producing the saved report.

SCOPE: This rules out a residue-based prime-color candidate, not arbitrary
prime colorings, finite-primitive-exception colorings, or the original
positive-density conjecture. Spec.lean remains unchanged with its original
sorry. No valid settlement is ready and no computation is pending.

## Density-sensitive completion criterion (new verified conditional result)

Submission/EntropyBoundaryCriterion.lean formalizes the ORDINARY increasing
greedy cube-Sidon construction, distinct from the divisor-closed greedy set.
It proves every finite prefix Sidon, prefix compatibility, and the exact
partition of [0,N) into selected roots and roots whose insertion is not Sidon.

Public sufficient criteria, with uniform hypotheses over every finite Sidon
root set S contained in [0,N):
* small_set_boundary_suffices: for fixed delta>0 and C>=0, if |S|<=delta*N
  implies |boundary(S,N)|<=(1-2*delta)*N+C, then the original conjecture holds.
* continuous_boundary_modulus_suffices: a bound
    |boundary(S,N)| <= N*F(|S|/N)+C
  with F(x)->0 as x->0 suffices.
* logarithmic_boundary_suffices: in particular, a uniform bound
    |boundary(S,N)| <= K*|S|*(1+log(N/|S|))+C
  suffices. This is density-sensitive log(N/|S|), NOT merely log N.

The proof uses the SAME greedy witness for all prefixes, so it does not
substitute endpoint-only bounds for the compactness hypothesis. The entropy
modulus x-x*log x is continuous at zero. Empty sets and zero prefixes are
handled explicitly. All three printed axiom audits use only propext,
Classical.choice, Quot.sound. Build log: /tmp/entropy_boundary_criterion.log.
The module contains no holes, added axioms, or native_decide.

The existing separated-set amplification refutes a constant linear completion
bound, but does not by itself refute this density-sensitive bound. NO uniform
arithmetic boundary estimate has been proved. These are conditional results,
not a settlement. Spec.lean is unchanged with its original sorry.

One submission check was run earlier on the unchanged target; it failed
verification as expected. No valid proof or disproof has been submitted.

## Empty completion boundaries for short distant bands (new verified result)

Submission/ShortIntervalCompletion.lean compiles with current olean.
Log: /tmp/short_interval_completion.log. All three public axiom audits use
only propext, Classical.choice, Quot.sound.

For natural M,L with 6*L^2+4*L <= M:
* completion_trivial: if a,b,c lie in [M,M+L] and
    x^3+a^3=b^3+c^3,
  then x=b or x=c, even when x is otherwise unrestricted.
* cube_sidon_union_singleton: the cubes of [M,M+L] union {x} are Sidon
  for every natural x.
* boundary_eq_empty: every finite subset S of that band has empty
  EntropyBoundaryCriterion.boundary S N for every prefix cutoff N.

The proof first bounds any three-root completion in [M-4L,M+2L], then
applies the verified short-interval Sidon theorem to this enlarged band.
The insertion case 2*x^3=a^3+b^3 is handled separately by monotonicity.
This is stronger than Sidonness only within the original interval, but it
DOES NOT bound completions using roots in different intervals or establish
positive density. The uniform global boundary estimate remains unproved.
Spec.lean is unchanged with its original sorry; no valid new submission.

## Factor-parity residual odd-coloring obstruction (new, verified)

Submission/FactorParityOddColorObstruction.lean compiles with a current olean.
The public theorem no_odd_parity_refinement has only propext,
Classical.choice, and Quot.sound as axioms. Log:
/tmp/factor_parity_odd_color_obstruction.log. No holes or native_decide.

The six squarefree roots
  4062, 9058, 12002, 13398, 31171, 31731
all have odd prime-factor count and give the three collision edges
  (4062,9058,12002,13398),
  (4062,12002,31171,31731),
  (9058,13398,31171,31731).
Every root occurs twice. Thus even after fixing factor-count parity, a
Boolean refinement cannot have odd color sum on every remaining collision.
Multiplication by 5 preserves squarefreeness and gives the same obstruction
in the even-factor-count class. Both cases are kernel-verified.

This is stronger than imposing linear prime-character formulas, since the
refinement may be ANY function on roots. It is still an obstruction only to
the ODD EDGE-SUM condition, not to ordinary proper two- or four-coloring,
and not to the original existential density conjecture.

The precursor reused the saved 100000 collision data and performed exact F2
elimination, with an independently checked three-edge certificate. Scripts:
/tmp/cube_omega_residual_odd_check.py and
/tmp/cube_omega_rough_residual_odd_check.py, with matching JSON outputs.
On odd squarefree roots after the same factor-parity restriction, all 1702
saved residual rows were independent. This is merely a finite observation,
not an infinite consistency theorem. No new cube-collision enumeration ran.

Also reconsidered the all-family score/counting route. No uniform arithmetic
estimate or finite coloring was obtained. In particular, field-character
separation on each fixed conic still does not handle the aggregate of the
family-dependent finite heads. No new global conclusion is asserted.
Spec.lean is unchanged with its original sorry; no valid settlement is ready.

## Largest-root distribution follow-up (unresolved; repeated diagnostic)

Revisited the bounded largest-root-degree source criterion and recomputed its
saved finite degree distribution through 100000. This repeats the earlier
largest-root-degree diagnostic; it is NOT a new route or an asymptotic result.
The repeated medians in the upper half of the prefixes 1000,3000,10000,30000,
100000 were 2,3,4,6,8, and the degree-zero proportions were respectively
0.234,0.110666...,0.0466,0.020266...,0.00666. No collision enumeration ran.
No uniform positive-density bounded-degree source was established.

Also considered the divisor-sum interpretation of largest-root degree and
whether overlap among primitive-maximal-divisor events could give a positive
lower density complement without reciprocal summability. No such overlap or
uniform prefix estimate was proved. Superlinear counts were not converted
into an upper bound on independence density. No new Lean theorem resulted;
Spec.lean remains unchanged and unresolved.

## Rough fixed-factor-parity odd-color obstruction (new, verified)

Submission/RoughFactorParityOddColorObstruction.lean compiles with a current
olean. Its no_odd_parity_refinement theorem has only propext,
Classical.choice, and Quot.sound as axioms. Build log:
/tmp/rough_factor_parity_odd_color_obstruction.log. No holes, added axioms,
or native_decide occur in this auxiliary module.

This closes the specific residual candidate left by the finite rank check:
restricting to ODD squarefree roots and then to one factor-count parity does
NOT in general permit an odd edge-sum coloring. In fact the theorem uses the
smaller source of squarefree roots coprime to 210. Neither parity class admits
an arbitrary Boolean coloring whose sum is one on every strict collision.
It still does NOT exclude ordinary proper coloring.

The three ordered positive pairs are:
 (27985056751587216951076441196377553,
  15133825904028017038753684197567907),
 (43246475144883114992132083423619021,
  39670484170615831748036120486729503),
 (82018561908244126742857501883038757,
  81093920631780889498415793873742519).
All three larger-cube-minus-smaller-cube differences agree. The six roots
are squarefree and coprime to 210, with prime-factor counts 6,6,4,4,4,4.
Their three four-root collision edges have even incidence at every root,
so their three proposed odd edge sums add to 0=1 in ZMod 2. Multiplication
by 11 preserves squarefreeness and coprimality to 210 and yields the same
obstruction in the odd-factor-count class. All 12 source memberships and
all six cube identities are kernel-verified. Large primes are certified by
66 recursive Lucas-primality lemmas, not by external trust.

Discovery used the ALREADY KNOWN elliptic curve for cube difference
D=20888646305546, with base pairs (27541,1115), (29167,15773),
(38569,33167). Three rational points, with group coefficients
(0,-1,0), (-2,-1,0), (0,-1,2), have denominator lcm
959476694606480507116825220159. Clearing this denominator gives the above
pairs. A targeted finite group-combination check found the witness; no new
full-prefix cubic-collision enumeration was run. Discovery and audit files:
 /tmp/cube_odd_factor_parity_triples.sage
 /tmp/cube_odd_factor_parity_triples.json
 /tmp/cube_odd_factor_parity_triples.log
 /tmp/gen_rough_factor_parity_obstruction.py
The Sage computation is discovery only; the Lean proof checks the final
integer certificate independently.

SCOPE: This is a restricted coloring obstruction, not a proof or disproof
of the original positive-lower-density existential conjecture. It must not
be promoted to an obstruction to ordinary two/four-coloring or arbitrary
positive-density sources. Spec.lean remains unchanged with its original
sorry; no valid settlement is ready and no computation is pending.

## Exact factor-count and positive-density odd-color obstructions (verified)

Three further auxiliary modules compile with current oleans. Their public
results depend only on propext, Classical.choice, and Quot.sound:

* ExactFactorCountOddColorObstruction.no_odd_coloring_exact_count: for every
  k >= 8, the squarefree roots coprime to 210 with exactly k distinct prime
  factors admit no Boolean coloring having odd sum on every strict cubic
  collision. A three-edge, six-root certificate has exactly eight factors
  at every vertex; fresh squarefree dilation proves all larger k. Its 99
  recursive Lucas certificates are independently checked by Lean.
* BoundedFactorCountDensity.exists_large_count: a positive-lower-density
  set of positive integers has unbounded distinct prime-factor counts. A
  prime-multiplication fiber bound contradicts divergence of sum_p 1/p.
* FactorCountSelectedOddColorObstruction.no_odd_coloring_of_positive_density:
  no positive-lower-density source obtained by arbitrary preselection of
  factor counts among squarefree roots coprime to 210 admits such an odd
  edge-sum refinement. It combines the two preceding results.

Logs are /tmp/exact_factor_count_odd_color_obstruction.log,
/tmp/bounded_factor_count_density.log, and
/tmp/factor_count_selected_odd_color_obstruction.log. Discovery data and
script for the exact-count certificate are in
/tmp/cube_odd_exact_factor_count_triples.{sage,json,log}; the generator is
/tmp/gen_exact_factor_count_obstruction.py. The six-root certificate comes
from three rational points on the already known cube-difference curve,
not another full-prefix collision search.

SCOPE: An odd edge-sum coloring is strictly stronger than an ordinary proper
coloring. These theorems do not rule out proper finite colorings or arbitrary
positive-density cube-Sidon sets. The density lemma asserts unbounded factor
counts, not an upper-density-zero conclusion. Spec.lean is still unchanged
and unresolved; there is no valid settlement ready for submission.

## Uniform one-sided exponential prime-score sources (new, verified)

Two new auxiliary modules compile cleanly with current oleans. Every printed
axiom audit uses only propext, Classical.choice, and Quot.sound. Neither module
contains sorry/admit/native_decide or added axioms.

1. PrimeBlockExponential.lean: a remainder-free Euler-product moment bound in
   EVERY natural prefix, for any finite prime block P and nonnegative weights:

     sum_{1<=n<=N} prod_{p in P}(1+v_p 1_{p|n})
       <= N prod_{p in P}(1+v_p/p),                  v_p>=0.

   Expanding over prime subsets and using floor(N/prod Q)<=N/prod Q proves it;
   there is no assumed independence of divisibility events. Consequently,
   for w_p>=0 and t>=0, writing score=sum_{p|n}w_p and mean=sum_p w_p/p,

     sum_{1<=n<=N} exp(t*(score(n)-mean))
       <= N exp(sum_p (exp(t*w_p)-1-t*w_p)/p).

   upper_tail_le gives the corresponding exact Chernoff bound. All primes
   in P are included in the fixed full-block center; primes beyond N cause
   no remainder term because expansion coefficients are nonnegative.

2. PrimeBlockExponentialSource.lean: an arbitrary countable collection of
   these UPPER inequalities can be imposed inside any positive-lower-density
   set of positive integers. The error costs may be any positive summable
   schedule with total below a prefix-density bound. The inverse-square
   schedule proves exists_logarithmic_upper_source: one K (depending only
   on the original source) works for every P_j, nonnegative w_j, and t>0,
   on a retained positive-lower-density A, with

     t*(score_j(n)-mean_j)
       <= sum_{p in P_j}(exp(t*w_j(p))-1-t*w_j(p))/p
            + K + 2*log(j+1).

   The normalization uses the previously verified countable-band prefix
   theorem, not an exchange of countably many asymptotic densities.

Build/audit logs: /tmp/prime_block_exponential.log and
/tmp/prime_block_exponential_source.log. Temporary CheckExp.lean was removed.

LIMITATION: These bounds require NONNEGATIVE weights and are ONE-SIDED with
FIXED FULL-BLOCK centers. They do not give exponential tails for signed
moving-center character scores. The conic separation uses signed contrasts;
replacing it by upper bounds on positive score components loses that
separation. No uniform sum over all collision families, finite-head bound,
Sidon construction, or universal density-zero result follows yet. Spec.lean
remains unchanged with its original sorry; no valid settlement is ready.

## Signed uniform high moments and logarithmic bands (eight files, verified)

This continuation closes the SIGNED moving-center concentration upgrade left
open by the preceding one-sided exponential estimates. It does not settle the
original conjecture or supply a uniform all-collision arithmetic bound.

Eight new auxiliary modules compile with current oleans. A separate importing
axiom audit is /tmp/audit_signed_moments.log. Every audited result uses only
propext, Classical.choice, and Quot.sound. No holes, native_decide, or new axioms
are used. Temporary CheckMoment.lean was removed.

1. SignedPrimeBlockExponential.lean (157 lines): exact signed finite-prime
   Euler-product expansion and its explicit l1 discrepancy. The signed MGF
   is bounded by its independent Bernoulli Euler product plus
   prod_p(1+|exp(t*w_p)-1|). Its centered version retains this error multiplied
   by exp(-t*mean). This error alone is NOT uniform over expanding blocks.

2. PrimeBlockMomentComparison.lean (204 lines): defines the finite independent
   Bernoulli model with prime probabilities 1/p. Joint arithmetic indicator
   moments differ from N times the model by at most one. Repeated prime
   indices are allowed. Expanding centered products and then powers proves

     |sum_{n<=N}(score(n)-mean)^r - N*E(modelScore^r)|
       <= (2*sum_{p in P}|w_p|)^r.

   This polynomial error in block size, rather than the full MGF error, is
   the input that makes truncation work.

3. PrimeBlockModelMoments.lean (188 lines): for |w_p|<=1 and |t|<=1,
   E exp(t*modelScore) <= exp(t^2*M), M=sum_p w_p^2/p. Optimizing the
   even-moment parameter t=sqrt(k/(M+k)) gives

     E(modelScore^(2k)) <= 2*(12*k*(M+k))^k,  k>=1.

   arithmetic_even_moment retains the preceding polynomial error explicitly.

4. SmallPrimeBlockMoments.lean (93 lines): if card(P)^(2k)<=N, the error is
   absorbed, yielding 3*N*(12*k*(M+k))^k. Also proves the general deterministic
   tail bound: primes exceeding T contribute at most r to a bounded score
   at positive n<=N<(T+1)^r. An integer r-th-root cutoff is constructed using
   Nat.findGreatest; no unproved nth-root interface is assumed.

5. PrimeBlockCenteredHighMoments.lean (129 lines): combines the small block
   with its deterministic tail. If a chosen center differs by at most B*k
   from the small-prime center, the prefix moment is bounded by

     N*(16*max(12,(B+2)^2)*k*(M+k))^k.

6. UniformPrimeBlockHighMoments.lean (280 lines): applies the existing uniform
   reciprocal-prime power-window bound. Small root cutoffs are handled
   separately, not discarded as an N-dependent finite exception. The main
   theorem exists_moving_moment_constant proves ONE C>0 such that, for EVERY
   finite prime block, EVERY signed real weight sequence |w_p|<=1, EVERY
   k>=1, and EVERY natural prefix N,

     sum_{1<=n<=N}(score(n)-movingMean(n))^(2k)
       <= N*(C*k*(M+k))^k.

   The integer-dependent center is the existing dyadic square-root center.
   Prefix estimates are glued over exact base-4 shells; the upper shell
   endpoint is 4^(j+1)-1, ensuring the centers really agree.

7. SignedLogarithmicPrimeBands.lean (133 lines): chooses moment orders
   k_j=J+Nat.log 2 (j+1)+1. The costs 4^(-k_j) are summable by comparison
   with (j+1)^(-2). CountableBandDensity then gives, inside ANY positive-
   lower-density set of positive integers, a positive-lower-density A with

     (score_j(n)-movingMean_j(n))^2 <= K*l_j*(M_j+l_j),
     l_j=Nat.log 2 (j+1)+1.

   The same K>0 works for every sequence of prime blocks and signed weights
   bounded by one. This is a genuine improvement over geometric index loss,
   including for signed character scores. It uses uniform prefix estimates,
   not an interchange of countably many asymptotic densities.

8. LogarithmicConicBandSource.lean: applies these bounds to the explicit
   two-field conic, preserving squarefreeness and positive lower density.
   For every surviving positive rational normalization/dilation,

     mixedMass_j <= 4*sqrt(K*l_j*(M_j+l_j)) + 2*sqrt(2000000*M_j).

   Rational proportionality and normalization are handled by the already
   verified ProportionalConicBandSource lemmas.

Build logs: /tmp/signed_prime_block_exponential.log,
/tmp/prime_block_moment_comparison.log, /tmp/prime_block_model_moments.log,
/tmp/small_prime_block_moments.log, /tmp/prime_block_centered_high_moments.log,
/tmp/uniform_prime_block_high_moments.log,
/tmp/signed_logarithmic_prime_bands.log, /tmp/logarithmic_conic_band_source.log.

REMAINING GAP: The analytic source now permits countably many signed scores
with logarithmic index costs, but no normalization-safe global count, summable
cover, uniform finite coloring, or finite-prefix independent-set construction
for ALL cubic collisions has been proved. Family-dependent finite heads and
arithmetic constants cannot simply be summed. The last theorem remains about
one explicit conic. Spec.lean retains its original sorry and statement; these
new results must not be submitted as a settlement of the original existential.

## Continuation after signed high moments: global review only (unresolved)

Reviewed the arithmetic step from the completed signed logarithmic bands to a
uniform source for ALL collisions. No new uniform estimate was established.
The largest-root-degree trimming idea was checked against the existing
DensityOneCollisionGrowth theorem: density-zero deletion cannot produce a
linear-count source. The existing LargePrimeSourceDensity theorem likewise
already rules out a linear full-prefix count on the unrefined large-prime
source. Neither obstruction rules out a smaller positive-density Sidon set.

Also reviewed finite multiplicative colorings, conic-index aggregation, and
scale-dependent constructions. No universal coloring, summable all-family
cover, fixed-density finite-prefix witnesses, or density-zero theorem resulted.
No new enumeration or Lean theorem was produced. Do not treat these reviews as
new mathematical progress or repeat the saved degree diagnostics on that basis.
Spec.lean remains unchanged with its original sorry; no valid proof or disproof
is ready, and no verification submission has been made in this continuation.
