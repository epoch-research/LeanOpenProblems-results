# Development checkpoint — NOT A SETTLEMENT

`Submission/Spec.lean` is unchanged and still contains `sorry`.
No complete proof or disproof of `Erdos3.erdos_3` has been found.
The conjecture is faithfully formalized; no definitional counterexample was found.
All declarations described below were checked with only `propext`, `Classical.choice`, and `Quot.sound`.
The scratch files import `FormalConjecturesUtil` and are independent of the target theorem.

## Verified reduction (`Submission/Reduction.lean`)

The original conjecture is equivalent to each of:

* For every fixed k >= 3, finite k-AP-free subsets of the natural numbers have uniformly bounded reciprocal sums.
* For every fixed k >= 3, the series sum_j r_k(4^j)/4^j converges, where r_k(N) is `Set.IsAPOfLengthFree.maxCard k N`.

Unbounded finite harmonic weights for one fixed k yield a genuine infinite k-AP-free divergent-reciprocal counterexample by safe affine gluing.
The converse extremal-series construction uses separated intervals [2*4^j+1, 3*4^j].

New verified declarations added after the earlier checkpoint:

* `maxCard_add_le`: r_k(m+n) <= r_k(m)+r_k(n), for k >= 2.
* `maxCard_mul_le`: r_k(m*n) <= m*r_k(n).
* `extremal_density_antitone`: j -> r_k(4^j)/4^j is antitone.
* `tendsto_nat_mul_of_summable_antitone`: a nonnegative summable antitone real sequence f satisfies n*f(n) -> 0.
* `conjecture_implies_logarithmic_decay`: the conjecture implies j*r_k(4^j)/4^j -> 0 for each k >= 3.

These are reductions and necessary consequences, not proofs of convergence.

Additional conditional lemmas verified in the latest continuation:

* `extremal_series_of_log_power_bound`: for fixed k, any eventual bound `r_k(N) <= C*N/(Real.log N)^p` with real p > 1 gives convergence of the dyadic extremal series.
* `conjecture_of_log_power_bound`: such a bound for every fixed k >= 3 implies the original conjecture.

The constants and exponent may depend on k, and finitely many exceptional N are harmless. These proofs use the real p-series theorem and comparison. They do **not** prove the required extremal bounds. The new declarations were checked with only `propext`, `Classical.choice`, and `Quot.sound`. `Submission/Spec.lean` remains unchanged.

Additional strengthened gluing results verified in the latest continuation:

* `finite_extension_of_unbounded_with_gap`: given unbounded finite k-AP-free reciprocal weights, an AP-free finite set F can be extended to one with arbitrarily large weight while introducing no new ordered pair at distance at most any prescribed D.
* `gapped_counterexample_of_unbounded`: the resulting infinite AP-free divergent-reciprocal set can satisfy `{x | x in A and x+d in A}.Finite` for every d > 0.
* `conjecture_iff_finite_shift_case`: the original conjecture is equivalent to its restriction to sets with that finite-shift-intersection property.

The extension uses L = max (sup F) D, r = L+1, q = 4r, and an affine image of a sufficiently heavy finite set. Close pairs stabilize in a finite stage of the growing chain. These are conditional construction and equivalence theorems, not the existence of an actual counterexample. All new declarations compile using only the permitted axioms.

Further affine-thin strengthening verified in `Submission/Reduction.lean`:

* `finite_extension_of_unbounded_affine_thin`: the finite extension can introduce no new solution to any nonidentity equation `a*x+b=c*y+d` with positive a,c and all four coefficients at most D.
* `AffineThin A` means `{x | x in A and exists y in A, a*x+b=c*y+d}` is finite for every fixed a,b,c,d with a,c > 0 and `(a != c or b != d)`.
* `affine_thin_counterexample_of_unbounded`: unbounded finite k-AP-free weights produce an affine-thin k-AP-free divergent-reciprocal set.
* `AffineThin.finite_shift_intersection` recovers the earlier fixed-shift property.
* `conjecture_iff_affine_thin_case`: restricting the original conjecture to affine-thin sets is equivalent to the full statement.

For the finite extension use L = max (sup F) D, r = L+1, q = 4*(D+1)*r. A new-new affine relation reduces modulo q to `a*r+b=c*r+d`, then modulo r to b=d, forcing a=c. Cross-block relations are excluded by size. Every fixed relation stabilizes at a finite stage of the chain. All declarations compile with only the permitted axioms. These remain conditional constructions and reductions; they do not exhibit an actual counterexample or prove the conjecture.




## Obstructions already checked

### `Submission/DensityCheck.lean`

Primes have divergent reciprocal sum but natural density zero. Therefore divergence does not imply positive natural density. This is not a counterexample to the original conjecture.

### `Submission/MultiplicativityCheck.lean`

* `rothNumberNat 3 = 2` and `rothNumberNat 9 >= 5`.
* Submultiplicativity fails, even eventually.
* The stronger new theorem `not_eventually_submultiplicative_up_to_constant` proves:
  there are no real C and natural N such that r_3(m*n) <= C*r_3(m)*r_3(n) for all m,n >= N.

The last proof combines qualitative Roth density decay with Behrend's lower bound. Fixing a scale where C*r_3(m) < m and iterating such a recurrence would contradict Behrend. These refute proposed recurrences, not the conjecture.

### `Submission/ColorReductionCheck.lean`

`no_bounded_color_reduction`: for every finite number of colors, there is a finite 4-AP-free set that cannot be partitioned into that many 3-AP-free subsets.
Proof uses base-5 digit cubes with digits {0,1,2} and Hales–Jewett.
The witnesses are finite and are not counterexamples to the target statement.

## New unconditional partial result

### `Submission/ParallelogramCheck.lean`

`HasProperParallelogram A` means there are a < b < c < d in A with a+d=b+c.

* `finite_card_bound`: a finite subset S of [0,N] with no such configuration satisfies |S|*(|S|-1) <= 2*(2*N+1).
* `finite_card_geometric_bound`: at N=4^(j+1), |S| <= 6*2^j.
* `finite_recip_sum_bound`: uniform reciprocal-sum bound by sum_j 6*(1/2)^j for sets with no proper parallelogram.
* `summable_of_no_proper_parallelogram`.
* `divergence_has_proper_parallelogram`: reciprocal divergence forces a proper parallelogram.
* `proper_parallelogram_does_not_force_threeAP`: the set {0,1,3,4} is a proper parallelogram and is 3-AP-free.

Thus the new structural consequence does not imply a three-term or four-term AP.

## Obstruction to iterating through fixed shifts

### `Submission/IntersectionCheck.lean`

Define `spaced n = n * (Nat.log 2 n + 1)` and `spacedRange = Set.range spaced`.

* `spaced_strictMono`.
* `not_summable_spaced`: proved by Cauchy condensation, since the condensed series is the shifted harmonic series.
* `spacedRange_divergent`.
* `fixed_shift_intersection_finite`: for every d > 0, {n | n in spacedRange and n+d in spacedRange} is finite.
* `fixed_shift_intersection_summable`.
* `intersection_divergence_reduction_fails`: disproves the proposed universal implication from reciprocal divergence to divergence of some fixed positive-shift intersection.
* `spacedRange_contains_ap`: this same set has an AP of every finite length; its logarithmic blocks are APs. It is therefore NOT a counterexample to the original conjecture.

For the range summability pullback, specify `(i := f)` explicitly in `Summable.comp_injective` to avoid an elaboration timeout.

## Obstruction to divergence-preserving convex extraction

### `Submission/ConvexExtractionCheck.lean`

Define `blocks = {n | exists j, 4*4^j <= n and n < 5*4^j}`.

* `blocks_divergent`: the reciprocal sum on this set diverges. Each disjoint block contributes at least 1/5.
* `convex_sequence_summable`: every strictly increasing sequence in `blocks` with nondecreasing successive gaps has summable reciprocals. Once its block index increases, it increases at every subsequent step, so a tail is bounded below by a geometric sequence.
* `convex_extraction_fails`: a divergent-reciprocal set need not contain a divergent-reciprocal sequence with nondecreasing gaps.
* `blocks_contains_ap`: the same witness contains an AP of every finite length.

All these declarations compile and use only the three permitted axioms. This only rules out the unconditional extraction step; it does not settle the original conjecture or prove anything about extraction under additional AP-freeness assumptions. `Submission/Spec.lean` is unchanged.

## Unconditional convex-sequence special case

### `Submission/ConvexCase.lean`

For a strictly increasing f : Nat -> Nat, define `gap f n = f (n+1) - f n` and assume these gaps are nondecreasing.

* `summable_of_uniform_gap_increase`: if, for some K > 0, every gap increases strictly after K steps, then the reciprocals of f are summable. The proof obtains `n^2 <= f (2*K*n)` and applies Schlomilch condensation and the p=2 series.
* `divergence_forces_gap_runs`: divergent reciprocals force runs of equal gaps of every finite length.
* `divergent_convex_sequence_contains_ap`: the range contains APs of every finite length.
* `convex_range_case`: the exact original conclusion for the set `Set.range f`, under the additional monotone-gap hypothesis.

These lemmas compile with only the permitted axioms. There is no claimed reduction from general sets to this special case; the preceding convex-extraction counterexample forbids the unconditional divergence-preserving extraction step. `Submission/Spec.lean` remains unchanged.

## Remaining gap

No summable upper bound for r_k(4^j)/4^j has been established for arbitrary fixed k >= 3.
No divergent extremal-density series or unbounded finite harmonic weights have been established for any fixed k >= 3.
Qualitative convergence to zero and antitonicity are insufficient by themselves.
A proof that fixed-shift intersections remain divergent is false, as verified above.
Bounded-color reduction to three-term APs and fixed-constant multiplicative recurrences are also false.

## Environment and verification

Run `lake env lean Submission/<file>.lean` in `/workspace/leanproject`.
The target file's sole import must remain unchanged. Required helpers would have to be copied into that single file if a settlement is found.
A further submission of the unchanged target was made transparently as incomplete; it failed verification as expected. Do not interpret the tool's `Submitted.` acknowledgment as verification success.

Repeated library searches found no theorem closing the gap. Matches connecting summability and arithmetic progressions outside the combinatorics files concerned Dirichlet's theorem on primes in residue classes, not the required long progressions in arbitrary sets.
A fresh search of local PDF/TeX/Markdown material found no relevant paper. External DNS resolution failed; a direct HTTPS DNS query to 1.1.1.1 timed out. No newer external result was obtained.

Further informal ideas involving cubes, weighted Ramsey arguments, convex subsequences, analytic generating functions, Müntz-type reasoning, digit constructions, and nilsequence density increments produced no complete argument. They must not be treated as established lemmas or as settlements.

## Latest continuation status

After the affine-thin reduction, there have been many repeated inability reports and no further verified mathematical progress. `Submission/Spec.lean` still contains its original `sorry`; no successful settlement or new submission has occurred.

Additional informal directions examined without a complete argument: harmonic-weighted infinite-measure recurrence; compactness and affine-invariant dynamics; induction on the minimal omitted AP length via weighted coloring/extraction; multicolor van der Waerden bounds versus weighted extremal bounds; finite digit-statistic constructions; geometric/fractal constructions; recursive residue-class selection; Müntz/Hankel-function approaches; and dimension-theoretic approximate progressions. In particular, approximate APs do not give exact integer APs without a missing error-versus-step estimate. None of these explorations established a new lemma that closes the target.

A later external-access retry also failed: www.erdosproblems.com did not resolve, and an arxiv.org HTTPS connection forced to a known Fastly address timed out. No new external mathematical result was obtained. Resources were not exhausted; the blocker is the absence of a valid mathematical proof or counterexample.

## New verified progress: direct affine-thin subset extraction

`Submission/ThinningCheck.lean` (namespace `Erdos3ThinningCheck`) now compiles independently of the target. All printed axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.

New theorems:

* `affineColor_ne`: for every D, there is a finite coloring of the naturals that separates unequal x,y satisfying a*x+b=c*y+d whenever 0<a,c and all four coefficients are at most D. A greedy coloring uses the finite list of potential neighbors `(a*n+b-d)/c`, indexed by `(Fin (D+1))^4`.
* `large_finite_weight`: a reciprocal-divergent set has finite subsets of arbitrarily large reciprocal weight.
* `nonsummable_color_class`: any finite coloring of a reciprocal-divergent set has a reciprocal-divergent color class.
* `nonsummable_eventually_monochromatic`: given countably many finite colorings and any reciprocal-divergent A, there is a reciprocal-divergent B contained in A that is monochromatic outside a finite set for each coloring. Proof: take nested divergent color classes, choose finite pieces with weights exceeding n from stage n, and take their union.
* `divergent_affine_thin_subset`: **every** reciprocal-divergent A contains a reciprocal-divergent affine-thin B. This is stronger than the older conditional gluing reduction: B is a subset of the original A, and neither AP-freeness nor unbounded AP-free finite weights is assumed.
* `conjecture_iff_affine_thin_case`: a new direct proof of the same exact conjecture equivalence, using subset extraction rather than counterexample gluing.
* `exists_divergent_affine_thin`: applying the extraction to all naturals proves unconditionally that affine-thin reciprocal-divergent sets exist. This is **not** a counterexample to Erdős Problem 3: no AP length is shown to be absent.

For each fixed affine relation, eventual monochromaticity excludes unequal solutions with both endpoints outside a finite exceptional set. Solutions with an exceptional endpoint form a finite set, and nonidentity diagonal solutions satisfy x <= b+d.

This supersedes the older “no further verified mathematical progress” status above. It does not close the principal gap: no uniform finite AP-free harmonic bound has been proved, and no fixed-length AP-free divergent set has been constructed. `Submission/Spec.lean` remains unchanged with its original `sorry`. No proof submission was made in this continuation.

## New unconditional positive case: binary-digit symmetry

`Submission/BinarySymmetryCase.lean`, namespace `Erdos3BinarySymmetryCase`, compiles independently using only the permitted axioms.

Definitions:
* `digitSum n = (Nat.digits 2 n).sum` (binary popcount).
* `digitZeros n = (Nat.digits 2 n).length - digitSum n`.
* `DigitSumInvariant A`: membership depends only on digit sum, allowing zero padding.
* `BinarySymmetric A`: membership depends only on the pair (binary length, digit sum). This is the more general positive case, with no arbitrary zero-padding assumption.

Verified ingredients:
* `weighted_nat_sum`: sum over n < 2^m of r^(digitSum n) equals (1+r)^m.
* `summable_of_bounded_digitSum`: bounded binary popcount implies summable reciprocals. The finite counting estimate is card(S) <= 2^M*(3/2)^L for popcount <= M and n < 2^L; dyadic harmonic contributions are bounded by 2^M*(3/2)*(3/4)^j.
* `summable_of_bounded_digitZeros`: bounded zero count also implies summability. Proof uses an injective binary complement with a new leading 1; it turns zero count into popcount minus 1 and increases positive n by at most a factor of 4.
* `divergent_many_zeros_and_ones`: for every M, any reciprocal-divergent A has an element with more than M zeros and more than M ones in its binary expansion.
* `constant_digitSum_progression`, `prefix_progression`, `balanced_class_ap`: explicit APs with constant digit sum and length. For 0 <= i < 2^m, the low and high m-bit blocks of (i+1)*(2^m-1) are complementary, so their total popcount is m. A fixed high prefix supplies the desired remaining ones and zeros.
* `digitSum_invariant_case` and **`binary_symmetric_case`**: the exact original conclusion under these respective extra hypotheses.
* **`binary_symmetric_fixed_step`**: for every m and N, a divergent binary-symmetric A contains an AP of length 2^m, step 2^m-1, and starting point at least N.
* `binary_symmetric_infinite_adjacent_pairs`: the m=1 case gives infinitely many adjacent pairs.
* **`symmetric_subset_summable_of_finite_adjacent_pairs`**: if A has only finitely many adjacent pairs, every binary-symmetric subset B of A has summable reciprocals. Combined with `ThinningCheck.lean` (or the earlier `IntersectionCheck.lean`), this rules out unconditional divergence-preserving extraction of binary-symmetric subsets from arbitrary divergent sets.

These are actual new positive special cases and a verified extraction obstruction, not a settlement of the original theorem. There is no justified reduction of a general set to the symmetric case. `Submission/Spec.lean` remains unchanged with its original `sorry`, and no proof was submitted in this continuation.

## New unconditional positive case: finite dyadic kernel

`Submission/FiniteKernelCase.lean`, namespace `Erdos3FiniteKernelCase`, now compiles independently with only `propext`, `Classical.choice`, and `Quot.sound`.

Definitions:
```lean
def sectionSet (A : Set ℕ) (q r : ℕ) : Set ℕ := {n | q * n + r ∈ A}
def dyadicKernel (A : Set ℕ) : Set (Set ℕ) :=
  {B | ∃ m r : ℕ, r < 2 ^ m ∧ B = sectionSet A (2 ^ m) r}
def HasAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A
```

Main verified results:
* `finite_vdw`: a finitary van der Waerden bound, derived from Mathlib's finite-dimensional Hales–Jewett theorem by summing word coordinates. It provides a uniformly bounded monochromatic AP for every finite coloring.
* `kernel_closed`: the dyadic kernel is closed under further dyadic residue sections.
* `uniform_holes_of_finite_kernel`: if A has finite dyadic kernel and omits APs of one fixed length, there is L>0 such that every kernel state has an empty residue section modulo Q=2^L. Proof: color residues by their kernel states; a monochromatic AP of residues sharing a nonempty section lifts to an AP in A.
* `count_mul`: exact counting by residue classes.
* `count_pow_le_of_holes`: a section-closed family with one missing residue per state has count(B,Q^j) <= (Q-1)^j.
* `summable_of_count_pow_bound`: that geometric count estimate implies reciprocal summability.
* **`finite_kernel_noAP_summable`**: any fixed AP-length obstruction implies summability for a set with finite dyadic kernel.
* **`finite_kernel_case`**: the exact original conclusion under the additional hypothesis `(dyadicKernel A).Finite`.

This is the finite-kernel condition used to characterize binary automatic sequences, but no equivalence to a DFA definition was needed or formalized here. No reduction from arbitrary sets to finite-kernel sets has been established. Constants in the argument depend on the finite kernel; this does not give the uniform finite harmonic bound required for the unrestricted conjecture.

`Submission/Spec.lean` remains unchanged with its original `sorry`. No completed proof or disproof of the original statement has been obtained, and no proof submission was made.

## New verified obstruction: finite-kernel subset extraction fails

`Submission/FiniteKernelCase.lean` has been extended and still compiles independently with its sole `FormalConjecturesUtil` import and only permitted axioms.

New definitions/results:
* `FiniteShiftIntersections A`: for each d>0, the set of x with x,x+d in A is finite.
* `finite_shift_kernel`: this property passes to dyadic residue sections.
* `uniform_finite_holes`: finite dyadic kernel plus finite fixed-shift intersections gives a fixed L>0 such that each kernel state has a **finite** residue section modulo Q=2^L. The proof colors residue sections and applies the two-term finitary van der Waerden statement; equal sections yield a fixed-shift pair for every point in that section.
* `count_pow_le_of_finite_holes`: if those exceptional sections have counts uniformly bounded by M, then count(B,Q^j) <= (M+1)*(j+1)*(Q-1)^j.
* `summable_of_scaled_count_bound`: a generic summable bound on geometric-scale counts implies reciprocal summability.
* `finite_kernel_finite_shift_summable`: finite kernel and finite fixed-shift intersections together imply summability. The extra linear factor j is absorbed by a polynomial-times-geometric series.
* **`finite_kernel_infinite_shift`**: every reciprocal-divergent finite-kernel set has infinitely many pairs at some fixed positive difference.
* **`finite_kernel_subset_summable`**: every finite-kernel subset of a set having finite fixed-shift intersections is summable.

`Submission/KernelExtractionBarrier.lean` combines the above with `ThinningCheck.lean`. This scratch file imports those two scratch modules (it does not import or depend on the target).

Verified:
* `divergent_subset_without_finite_kernel_subsets`: every reciprocal-divergent A has a reciprocal-divergent B contained in A such that every finite-kernel subset of B is summable.
* **`no_divergent_finite_kernel_extraction`**: negates the proposed universal implication that every divergent set contains a divergent finite-kernel subset.

These declarations have only the allowed axioms. This is NOT a disproof of the original conjecture: the extracted sets may still contain APs with varying differences.

To compile the combined scratch file, first build its two local dependencies if their oleans are absent:
```sh
mkdir -p .lake/build/lib/lean/Submission
lake env lean -o .lake/build/lib/lean/Submission/ThinningCheck.olean Submission/ThinningCheck.lean
lake env lean -o .lake/build/lib/lean/Submission/FiniteKernelCase.olean Submission/FiniteKernelCase.lean
lake env lean Submission/KernelExtractionBarrier.lean
```

The original task remains unsettled. `Submission/Spec.lean` still contains the unchanged original theorem with `sorry`; no proof submission was made in this continuation. No general quantitative AP-free harmonic bound or actual fixed-length AP-free divergent counterexample has been obtained.

## New verified partial result: arbitrary proper additive cubes

`Submission/CubeCase.lean` compiles independently with the sole import `FormalConjecturesUtil`.
All printed main-theorem axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.

Definitions:
* `ReflectedCube d S`: generated from a singleton by repeatedly adjoining `c-S`, with `2*x<c` for every old point x.
* `HasCube A d`: A contains a finite reflected cube of dimension d.
* `vertices a L`: the usual translated subset-sum vertices, recursively adjoining a translate by each list entry.

Verified counting and summability results:
* `reflectedCube_card`: the cardinality is exactly `2^d`.
* `max_fiber`, `split_bound`: a largest sum-and-orientation fiber of ordered distinct pairs gives B contained in S, with every x in B below the reflection center, its reflection in S, and `|S|*(|S|-1) <= 2*(2*N+1)*|B|`.
* `cubeFree_card_bound`: if A omits a dimension-d cube and S is a finite subset of A contained in [0,N], then
  `S.card^(2^d) <= (8*(N+1))^(2^d-1)`.
* `cubeFree_card_geometric_bound`: at the scales Q=2^(2^d), the corresponding count is bounded by `8*(2^(2^d-1))^j`.
* `cubeFree_finite_recip_sum_bound`: the finite reciprocal sum is at most `16*2^(2^d-1)`.
* `summable_of_no_cube` and `divergence_has_cubes`: reciprocal divergence forces reflected cubes of every fixed dimension.
* `reflectedCube_representation`: every reflected cube is a translated subset-sum cube with positive generators.
* **`divergence_has_proper_additive_cubes`**: for every d there are a and a positive-generator list L of length d such that `vertices a L` is contained in A and has cardinality `2^d`. Thus all subset sums are distinct.

Verified obstruction to closing the AP conjecture by this result alone:
* `threeAPFree_reflect`: suitably separated reflected copies preserve 3-AP-freeness.
* `sparseCube d`: a nested cube construction using reflection centers `4^(d+1)`.
* `sparseCube_cube`, `sparseCube_free`, `sparseCube_mono`.
* **`cubes_do_not_force_threeAP`**: a single 3-AP-free set contains reflected cubes of every finite dimension.
* `sparseCube_recip_sum`, `finite_subset_sparseCube`, **`sparseCube_union_summable`**: this explicit cube-rich example has a convergent reciprocal sum, so it is not a counterexample to the original conjecture.

The original conjecture remains unsettled. `Submission/Spec.lean` is unchanged and still contains its original `sorry`. No proof submission was made. The remaining gap is still the uniform finite harmonic bound for sets avoiding a fixed AP length (or unbounded such weights for one fixed length to obtain a disproof).

## New verified obstruction and exact reduction: uniformly bounded shift weights

`Submission/WeightedIntersectionCheck.lean` imports `Submission.ThinningCheck` (whose built olean already exists) and compiles. All printed main theorem axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.

The new unconditional theorem **`divergent_subset_uniform_shift_bound`** states that every reciprocal-divergent A has a reciprocal-divergent subset B such that for every positive d, the reciprocal sum over `{x | x in B and x+d in B}` is summable and at most **3**, uniformly in d. This is stronger than merely making every fixed-shift intersection finite.

Construction and verified helpers:
* `nonsummable_tail`, using cofinite equality of indicators.
* `bounded_weight_piece`: a divergent set has a finite subset with reciprocal weight in (1,2]. A minimal-cardinality subset of weight >1 gives the upper bound.
* `separated_piece`: after finite coloring by residues modulo M+1 and discarding the initial segment through 2M, choose such a finite piece V. Every x in V exceeds 2M, and every positive difference of points of V exceeds M.
* `extend_shift_bound`: if U lies in [0,M], adjoining V preserves the uniform bound 3 on every positive-shift reciprocal intersection. For d<=M no new pairs appear. For d>M old-old pairs are impossible, old-new pairs are unique at most, and new-new pairs have total weight at most 2.
* `finite_subset_chain`, `summable_and_tsum_le_of_finite_bound`.
* The cumulative finite stages have reciprocal mass at least their stage index. Their union diverges; all finite intersection sums are bounded by 3, hence the full intersection sums are summable with the same bound.

Additional verified statements:
* `UniformShiftWeightBound A`: the uniform bound 3, including summability of every intersection.
* **`divergent_affine_thin_subset_uniform_shift_bound`**: both the old affine-thin property and the new uniform shift-weight bound can be imposed simultaneously on a divergent subset of any divergent A.
* **`conjecture_iff_uniform_shift_bound_case`**: the exact original conjecture is equivalent to its restriction to sets satisfying both of these sparsity conditions.
* `exists_divergent_uniform_shift_bound`: such sets exist unconditionally.
* **`unbounded_shift_weight_reduction_fails`**: negates the auxiliary assertion that divergence forces arbitrarily large reciprocal intersection sums as the positive shift varies.

This does NOT settle the original AP conjecture and is not a valid `erdos_3.disproof`. The extracted subsets need not omit any fixed AP length. `Submission/Spec.lean` remains unchanged with its original `sorry`. No proof submission was made in this continuation.

Compile using:
```sh
lake env lean Submission/WeightedIntersectionCheck.lean
```
If the dependency olean needs rebuilding:
```sh
lake env lean -o .lake/build/lib/lean/Submission/ThinningCheck.olean Submission/ThinningCheck.lean
```

Technical note from this development: direct coercions of the local recursively defined `chain n : Finset Nat` into `Set Nat` unexpectedly failed elaboration in this file. Using the equivalent set `{x | exists n, x in chain n}` and expressing finite-subset hypotheses as `forall x in S, exists n, x in chain n` avoided the issue. Explicit `Finset.le_sup (f := id)` and unfolding `shiftPart` before using `Finset.mem_filter` were also needed.

## New verified quantitative route and obstruction: power-scale contraction

`Submission/ScaleContractionCheck.lean` imports `Submission.Reduction` and compiles. The dependency has now been built at `.lake/build/lib/lean/Submission/Reduction.olean`. All printed main theorem axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.

New analytic results:
* `summable_of_scale_contraction`: if f is nonnegative and antitone, C>1 and N>0, q>=0 and C*q<1, and f(C*n)<=q*f(n) for n>=N, then f is summable. The proof uses Mathlib's general Schlömilch condensation theorem at scales N*C^j.
* `summable_of_quadratic_scale_contraction`: f(C*n)<=K*f(n)^2 for n>=N suffices when C*K*f(N)<1 and K>=0.
* `summable_of_eventual_quadratic_scale_contraction`: the quadratic estimate, if eventually true with fixed C>1 and K>=0, suffices alongside f(n)->0.
* `extremalDensity k j := maxCard k (4^j) / 4^j` (real-valued).
* **`conjecture_of_quadratic_scale_contraction`**: an explicit conditional sufficient criterion for the exact original conjecture. It requires, for every k>=3, constants C,N,K satisfying the smallness and quadratic-contraction assumptions. **Those assumptions have NOT been proved.**

New normalization and obstruction results:
* `threeAPFree_iff_free_three`: the Mathlib and conjecture-library 3-AP-free predicates agree over naturals.
* **`maxCard_three_eq_roth`**: `Set.IsAPOfLengthFree.maxCard 3 N = rothNumberNat N`. Translation identifies the intervals [1,N] and [0,N).
* `rothDensity n := rothNumberNat (4^n) / 4^n` and `rothDensity_lower_bound`, using Mathlib's Behrend theorem.
* **`no_quadratic_roth_contraction_below_four`** and **`no_quadratic_extremal_contraction_below_four`**: for 1<C<4 (hence C=2 or 3), there do not exist any fixed K and threshold N such that the quadratic estimate holds thereafter, even just for k=3. Proof: qualitative Roth provides a starting density below 1/K; iteration gives decay with exponent 2^j at scales C^j, whereas Behrend only permits exponent of order sqrt(C^j). Since 4/C>1, these contradict each other.

This is a tested sufficient route plus a rigorously excluded range of its parameters, not a settlement. No quadratic contraction estimate for C>=4 has been proved, and the original extremal-series summability gap remains. `Submission/Spec.lean` is unchanged with its original `sorry`. No proof submission was made in this continuation.

To compile:
```sh
lake env lean Submission/ScaleContractionCheck.lean
```
If its dependency olean needs rebuilding:
```sh
lake env lean -o .lake/build/lib/lean/Submission/Reduction.olean Submission/Reduction.lean
```

Technical note: `A.IsAPOfLengthFree 3` with an ENat numeral did not rewrite directly using the natural-length equivalence in Reduction; stating the scratch lemma as `A.IsAPOfLengthFree (3 : Nat)` gave the required cast explicitly.

## Further verified limitation of the quadratic-contraction route

`Submission/ScaleContractionCheck.lean` has been extended and still compiles with only the permitted axioms.

New results:
* `inverseSquare n := 1 / ((n+1 : Nat) : Real)^2`.
* `inverseSquare_summable`, `inverseSquare_antitone`.
* `inverseSquare_no_quadratic_contraction`: for every natural C, there are no fixed real K and natural N with `f(C*n) <= K*f(n)^2` for all n>=N for this sequence.
* **`summability_does_not_imply_quadratic_contraction`**: a positive, antitone, summable sequence tending to zero can fail every eventual quadratic power-scale contraction with C>1.

This means the recently developed sufficient route requires more than merely proving the extremal series summable. The analytic hypotheses alone cannot establish its contraction estimate. This is a statement about general sequences; it does NOT refute such an estimate for the actual AP extremal densities at C>=4.

No proof or disproof of the original conjecture was obtained. `Submission/Spec.lean` remains unchanged with its original `sorry`; no proof submission was made.

## New verified diagnostic: structural interval-count properties are insufficient

`Submission/StructuralCountCheck.lean` imports only `FormalConjecturesUtil` and compiles. The final theorem's axioms are exactly the permitted `propext`, `Classical.choice`, and `Quot.sound`.

Definitions:
* `weight n = 1 / (Nat.log 4 (n+1) + 1)` (real-valued).
* `mass N = sum_{i<N} weight i`.
* `count N = Nat.ceil (mass N)`.

Verified:
* Positive, decreasing weights at most one, tending to zero.
* The mass function is nonnegative, increasing, subadditive, and at most N.
* The natural-valued count function starts at zero, is increasing and at most N, and is subadditive.
* `count_mul_le`: `count (m*n) <= m*count n` for every m,n.
* `count_succ_le`: each increment is at most one.
* `count_density_tendsto_zero`: `count N / N -> 0`, by Cesaro convergence and the rounding error bound.
* `geometric_density_antitone`: `count (4^j) / 4^j` is decreasing.
* `geometric_density_lower`: this density is at least `1/(j+1)`.
* `geometric_density_not_summable`.
* **`structural_count_properties_do_not_force_summability`** packages all these properties in one existential theorem.

This rules out an implication from the already-proved structural interval-count identities plus qualitative density decay to the required extremal-series summability. It does NOT realize this function as AP-free extremal counts, and is NOT a counterexample to Erdős 3. Additional genuine combinatorial information is still needed.

`Submission/Spec.lean` remains unchanged with the original `sorry`. No complete proof or disproof has been found and no submission was made in this continuation.

Compile with:
```sh
lake env lean Submission/StructuralCountCheck.lean
```

## New verified unconditional result: approximate progressions from interval branching

`Submission/ApproximateAPCase.lean` imports `Submission.FiniteKernelCase` and compiles. Its four printed main theorem axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.

Definitions and counting proof:
* `translated A a = {n | a+n in A}`.
* `FullGrid A Q`: there exist a,j such that all Q consecutive cells of width `Q^j`, starting at a, contain a point of A.
* `count_blocks`: the exact contiguous interval partition identity.
* `no_grid_count_bound`: if no such grid exists, every interval of length `Q^j` contains at most `(Q-1)^j` points of A. At each node one of its Q children must be empty; induction gives the count bound.
* `summable_of_no_grid`: applies the already-verified geometric counting/summability lemma from FiniteKernelCase.
* **`divergence_full_grid`**: reciprocal divergence forces a full grid for every Q>1.

Unconditional approximate-AP consequences:
* **`divergence_approximate_progressions`**: for every k,M there are a,d,L with L>0 and `d=(M+2)*L`, and a strictly increasing `f : Fin k -> Nat` taking values in A, such that
  `a+i*d <= f i < a+i*d+L`.
* **`divergence_real_approximate_progressions`**: for every k and real epsilon>0, there are a,d>0 and a strictly increasing f taking values in A with
  `abs (f i - (a+i*d)) < epsilon*d` for all i.

Verified limitation of this argument:
* `quadratic_perturbation_free`: if `D > 2*k^2`, then `{D*i+i^2 | i : Fin k}` is 3-AP-free. Reducing a prospective AP equation modulo D separates its linear and quadratic parts; strict convexity forces the indices to coincide.
* **`threeAPFree_arbitrarily_accurate_finite_progressions`**: for every k,M, taking `L=(k+1)^2` and `D=(M+2)*L` gives a 3-AP-free approximate progression of length k with the same accuracy inequalities as the positive theorem.

The absolute width L from the interval-branching proof is not bounded. Letting the relative error tend to zero does not make the absolute error tend to zero, since d can grow. The finite 3-AP-free examples show there is no relative accuracy depending only on the requested length that suffices to force an exact 3-AP.

This is NOT a settlement and is not a counterexample to the original conjecture. `Submission/Spec.lean` remains unchanged with its original `sorry`. No complete proof or disproof has been obtained; no proof submission was made in this continuation.

Compile with:
```sh
lake env lean Submission/ApproximateAPCase.lean
```

## New verified test of combining the local-pattern results

`Submission/UniversalPatternCheck.lean` imports `Submission.Reduction`, `Submission.CubeCase`, and `Submission.ApproximateAPCase`. It compiles; the two printed main theorem axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`.

The new general theorem **`summable_universal_free_set`** states that for every fixed k>=3 there exists a k-AP-free set A whose reciprocal sum converges and is at most 2, but which contains an affine copy of every finite k-AP-free set:

```
forall S : Finset Nat, (S : Set Nat).IsAPOfLengthFree k ->
  exists q r : Nat, 0 < q /\ forall x in S, q*x+r in A
```

Construction:
* `finite_extension`: safely adjoin an affine copy of a prescribed finite k-AP-free pattern to an existing finite k-AP-free set, with added reciprocal mass at most `(1/2)^n`.
* Let L be the old maximum, choose `r=2*L+1+2^n*S.card` and `q=2*r+1`, and use the already-proved residue-separated gluing theorem from Reduction.
* Enumerate all finite k-AP-free patterns using countability, then recursively attach each one.
* The increasing union stays k-AP-free by finiteness of every prohibited AP. Its finite reciprocal sums are bounded by the geometric sum 2.

Concrete joint obstruction:
* `threeAPFree_iff_free_three` is copied from the previously verified ScaleContractionCheck normalization lemma.
* `reflectedCube_affine` verifies that positive integral affine images preserve reflected cubes.
* **`cubes_and_approximate_progressions_do_not_force_threeAP`** proves that ONE summable, 3-AP-free set contains reflected cubes of every dimension AND approximate progressions of every finite length and arbitrarily high relative accuracy (with the exact inequalities from ApproximateAPCase).

Thus combining the two strongest local-pattern consequences developed so far still does not force even a 3-AP. This is NOT a counterexample to the original conjecture, because the constructed set has a convergent reciprocal sum.

Built new dependency oleans:
```
.lake/build/lib/lean/Submission/CubeCase.olean
.lake/build/lib/lean/Submission/ApproximateAPCase.olean
```

Compile the new file with:
```sh
lake env lean Submission/UniversalPatternCheck.lean
```

No complete proof or disproof of Erdős 3 was obtained. `Submission/Spec.lean` is unchanged and still contains the original `sorry`. No proof submission was made in this continuation.

## Verified center-pruning certificate (completed)

`Submission/CenterPruningCheck.lean` now compiles, with only the permitted axioms
in both printed main theorem axiom lists.

Definitions: `core S` keeps the points that are centers of nontrivial 3-APs
inside S; `prune S j` iterates this operation.

* `removed_layer_threeAPFree`: each removed layer is 3-AP-free.
* `binary_depth_bound_fails`: there is a 4-AP-free set of 125 naturals below
  4096 for which `prune S 13` is nonempty (it contains 1334). Thus the proposed
  estimate `(prune S j).Nonempty → 2^j ≤ N` is false.
* The explicit nested layers and endpoint witnesses are kernel-checked.
  This is NOT a refutation of every O(log N) pruning bound and is NOT a
  counterexample to Erdős 3.

The original large `decide` and `decide +kernel` checks were killed by memory
usage. They were replaced by a Boolean checker using a natural-number bitmask
for 4-AP-freeness (with a general correctness proof), and explicit pairs of
endpoint witnesses for each pruning step. Every ground certificate uses
`decide +kernel`, not `native_decide`. Compile time is about 15 seconds.

`Submission/Spec.lean` is still unchanged with the original `sorry`.
No target proof or disproof was obtained; no submission was made.

## New verified diagnostic: characteristic-three Freiman modeling can fail

`Submission/FreimanModelCheck.lean` imports only `FormalConjecturesUtil` and
compiles. Its three printed main axiom lists contain only permitted axioms.

The explicit witness is `{0,1,5,6,8,17,18,24}`. `witness_free` verifies that it
is 3-AP-free. The four equalities

```
1+5 = 0+6
1+17 = 0+18
6+18 = 0+24
17+8 = 1+24
```

force any additive 2-Freiman homomorphism f into an abelian group to satisfy

```
f 8 = f 5 + 3 • f 1 - 3 • f 0.
```

Thus any such map into a group of exponent three identifies 8 and 5.
`no_characteristic_three_model` proves this for arbitrary abelian groups of
exponent three. `no_finite_field_model` specializes to `(ZMod 3)^d` for every
dimension d. `finite_threeAPFree_without_model` packages the finite obstruction.

This rules out a lossless finite-field modeling step even before requiring a
Freiman isomorphism or a small model. It does NOT rule out modeling selected
subsets with quantitative losses, nor characteristic-dependent models, and is
NOT a counterexample to Erdős 3.

The witness was simplified from an exact rational/modular linear-algebra check
of finite 3-AP-free patterns; the final proof is the displayed four-relation
algebraic calculation and a kernel-checked finite freeness test. The exploratory
Python scripts are not trusted by or used in the Lean proof.

No complete target proof or disproof was obtained. `Submission/Spec.lean` still
contains its original `sorry`; no proof submission was made.

### Additional verified fact about characteristic-three models

`FreimanModelCheck.lean` now also proves
`source_threeAPFree_of_characteristic_three_iso`: a 2-Freiman isomorphism from
an integer set into ANY abelian group of exponent three forces the source
itself to be 3-AP-free. The cyclic characteristic-three AP identities pull
back to two incompatible nontrivial integer AP equations. Its axiom list is
permitted and it compiles.

### New forward development under investigation (not yet proved)

Attempt a positive summability result for integer sets admitting characteristic-
three Freiman models. Planned ingredients: a polynomial-method cap-set bound,
small-doubling projection to a small finite vector space, and Plünnecke.
This remains a restricted class, not an established reduction of the original
conjecture. No new main-case theorem has yet resulted.

## Verified polynomial-method cap-set bound

Two new scratch files compile with only permitted axioms:

* `Submission/CapsetSlice.lean` (only `FormalConjecturesUtil` imported):
  `exists_large_support_annihilator` constructs a vector annihilating a given
  family of linear forms, with support size at least the ambient number of
  coordinates minus the number of forms. The proof chooses independent pivot
  columns and sets all other coefficients to one.
  `diagonal_slice_lower_bound` proves the three-tensor diagonal slice-rank lower
  bound by contracting with this vector and factoring the resulting diagonal
  matrix through the other two families of slices.

* `Submission/CapsetPolynomial.lean` imports `Submission.CapsetSlice`:
  expands the characteristic-three zero-sum tensor in seven coordinate
  monomials; each monomial has degree at most 2 per coordinate. Every product
  monomial has one of its three variable-group degrees at most `2*n/3`.
  Grouping by the low-degree monomial and applying the diagonal lower bound
  proves `capset_card_le_monomials`.
  The elementary weight identity
  `sum_e 2^(2*n-degree e) = 7^n`
  bounds the number of low-degree monomials. The exact integer inequality
  `343^5 <= 16^5 * 3^14` then gives the main quantitative result:

  `threeAPFree_card_power_bound`:
  for `S : Finset (Fin n -> ZMod 3)`, if S is 3-AP-free, then
  `S.card^15 <= 27^5 * (3^n)^14`.

All four printed main theorems in the polynomial file and both printed main
lemmas in the slice file use only permitted axioms. This is a genuine finite-
field quantitative result. It is not yet a proof for arbitrary integer sets.

Built dependency oleans:
`.lake/build/lib/lean/Submission/CapsetSlice.olean`
`.lake/build/lib/lean/Submission/CapsetPolynomial.olean`

Next planned step: use a small-doubling projection and Plünnecke to obtain a
bound independent of the original finite-field model dimension. No such
projection theorem is proved yet. `Submission/Spec.lean` remains unchanged.

## Verified dimension-free cap-set doubling bound and reciprocal summability case

Two further new scratch files compile, with permitted axiom lists only.

### `Submission/CapsetDoubling.lean`
Imports `Submission.CapsetPolynomial`.

* `exists_linear_separating`: for a finite set S of nonzero vectors in F3^n
  with `S.card < 3^m`, some linear map to F3^m kills no point of S. The proof
  counts kernels of the evaluation maps on the finite space of all linear
  maps. Each evaluation at a nonzero vector is surjective (use a dual vector),
  so kernel cardinality times `3^m` equals the number of maps. A union bound
  proves the assertion without any probabilistic axiom.
* `capset_card_le_tripling`: apply this separation to `(S+S+S).erase 0`, choosing
  m so that `3^m <= 3*(S+S+S).card`, and apply the polynomial cap-set bound to
  the projected indexed set. Result:
  `S.card^15 <= 27^5 * (3*(S+S+S).card)^14`.
* `tripling_times_card_sq_le`: Plünnecke gives
  `(S+S+S).card * S.card^2 <= (S+S).card^3`.
* **`capset_card_le_doubling`**:
  `S.card^43 <= 3^29 * (S+S).card^42` for every finite cap set in F3^n,
  independently of n.

### `Submission/FreimanModelCase.lean`
Imports `Submission.CapsetDoubling`, `Submission.FreimanModelCheck`, and
`Submission.FiniteKernelCase`.

* `HasThreeModel S`: S has an additive 2-Freiman isomorphism to its image in
  F3^n, for some n and some map. Dimension and map may depend on S.
* `sumset_card_image_le`: a Freiman homomorphism does not increase the
  cardinality of a finite sumset, proved by choosing representatives of sums.
* `modeled_card_le_doubling`: transfers the dimension-free cap-set bound to
  finite integer sets with such a model:
  `S.card^43 <= 3^29 * (S+S).card^42`.
* `modeled_card_in_range`: if S lies below N, then
  `S.card^43 <= (3^29 * 2^42) * N^42`.
* `summable_of_polynomial_count_bound`: a general integral counting estimate
  `count A N^(r+1) <= C*N^r` (with the intended parentheses
  `(count A N)^(r+1)`) and `C>=1` implies reciprocal summability. It chooses
  `Q=(C+1)^(r+1)` and `R=C*(C+1)^r < Q`, shows
  `count A (Q^j) <= (Q-1)^j`, then uses the previously verified geometric
  counting/summability lemma.
* `FinitelyThreeModelable A`: every finite subset of A has a three-model.
* **`summable_of_finitely_three_modelable`** proves reciprocal summability
  under that hypothesis. It does NOT assume one finite-dimensional model for
  the whole infinite set.
* **`divergence_finite_model_obstruction`**: every set with divergent
  reciprocal sum has a finite subset with no such model in any dimension.

All printed theorems in both files have only the permitted axioms. Compile:
```
lake env lean Submission/CapsetDoubling.lean
lake env lean Submission/FreimanModelCase.lean
```
The new CapsetDoubling and FreimanModelCheck oleans were built for dependencies.

This is a positive, quantitative restricted result. It is NOT the original
conjecture: the already-verified eight-element 3-AP-free witness shows that
progression-freeness alone does not imply finite three-modelability. No
reduction overcoming this obstruction has been established. `Spec.lean` still
contains its original `sorry`; no target proof/disproof or submission exists.

## Verified bounded-model-cover obstruction

`Submission/ModelCoverCheck.lean` now compiles with only permitted axioms.
The only remaining elaboration error was resolved by explicitly typing the
alphabet argument of `Sum.elim` as the witness subtype.

* `cube_threeAPFree`: the base-49 coding of any finite Cartesian power of
  `{0,1,5,6,8,17,18,24}` is 3-AP-free. Digit sums are at most 48, so pair-sum
  equalities reflect coordinatewise without carries.
* `no_bounded_model_cover`: for every finite number r, there is a finite
  3-AP-free integer set which cannot be colored with r colors such that every
  color class has an injective additive 2-Freiman homomorphism into any F3^d.
  Hales--Jewett supplies a monochromatic combinatorial line carrying the
  verified eight-point obstruction.

This rules out a bounded-piece reduction to characteristic-three models,
even for the weaker homomorphism notion. It is NOT a target disproof.
`Spec.lean` remains unchanged, with its original `sorry`.

## Verified quantitative model-cover obstruction

`Submission/ModelCoverQuantitative.lean` imports `Submission.FreimanModelCase`
and compiles with permitted axioms only.

* `model_cover_card_bound`: for S below N colored in r colors with every
  fiber admitting a characteristic-three Freiman isomorphism,
  `S.card^43 <= r^43 * (3^29 * 2^42) * N^42`.
* `eventually_roth_power_lower`: Behrend's lower bound implies, for every
  fixed natural q, eventually `N^q <= (rothNumberNat N)^(q+1)`.
* `eventually_polynomial_model_cover_obstruction`: for every sufficiently
  large N, there exists a finite 3-AP-free S below N such that every coloring
  into r modelable fibers satisfies
  `N <= (3^29 * 2^42)^2 * r^86`.

The last theorem follows by taking a maximum 3-AP-free set, using the second
lemma with q=85, squaring the first bound, and cancelling N^84. This rules
out even slowly growing (e.g. polylogarithmic) numbers of model pieces.
The statement concerns Freiman isomorphisms; the earlier bounded-cover
obstruction was stronger in allowing only injective Freiman homomorphisms.

There are now 26 verified scratch files, totaling about 6700 lines, but no
proof or disproof of the target. No unrestricted extremal-series estimate
has been obtained. `Submission/Spec.lean` still contains its original `sorry`.

## Verification status and direct residue-weight investigation

A submission of the unchanged target was rejected. `Spec.lean` still has its
original `sorry`; it is not a valid proof and should not be resubmitted without
an actual settlement. The scratch results remain separate from the target.

`Submission/ResidueHarmonicCheck.lean` is a new verified scratch file importing
`Submission.Reduction`, with permitted axiom lists for its main theorems:

* `residueQuotient S q r` is the quotient by q of the r-th residue fiber.
* `quotient_weight_eq` identifies its reciprocal sum with the sum over the
  original fiber; division by q is injective on a fixed residue class.
* `weight_le_max_residue`: if q>0, every x in S is at least q, and every
  residue quotient has reciprocal weight at most M, then S has weight at
  most M. This needs no progression-free assumption.
* `no_strict_residue_contraction`: for every real c<1, a three-point 3-AP-free
  set S above the initial segment has all three residue quotients of weight
  at most M>0, but S has weight greater than c*M.
  The witness is `{3*n,3*n+1,3*n+5}` with n sufficiently large. Its quotient
  fibers are `{n}`, `{n}`, and `{n+1}`. The proof uses the explicit lower
  bound `3/(3*n+5)` on its reciprocal sum and an Archimedean choice of n.

This rules out uniform strict contraction based only on AP-freeness and
residue subdivision. It does NOT rule out a threshold-dependent descent
applicable only to sets with large total reciprocal weight. No such descent
has been proved. There are now 27 verified scratch files; the target remains
unproved and undisproved.

## Verified obstruction to finite greedy-prefix compression

`Submission/GreedyCompressionCheck.lean` is verified with permitted axioms.

* `FinThreeFree` is a decidable, finite-quantifier form of `ThreeAPFree`.
* `greedy n` scans 1 through n, adding each integer if 3-AP-freeness is kept.
* `greedy_free` proves this algorithm always produces a 3-AP-free set.
* `greedy_nine` is checked by kernel reduction: the result is `{1,2,4,5}`.
* `{1,2,4,8,9}` is checked 3-AP-free and lies in `[1,9]`.
* Its reciprocal weight is `143/72`, greater than the greedy weight `39/20`.
* `no_greedy_prefix_domination` therefore disproves universal harmonic-weight
  domination by the greedy prefix at the same endpoint.

This does NOT disprove a bound by the weight of the entire infinite greedy
set. That stronger global comparison has not been proved or disproved here.
The finite example is verified without trusting any external optimization
result. Exploratory finite MILP computations were used only for investigation,
not as Lean proof steps. There are now 28 verified scratch files.

The actual target remains unchanged with `sorry`. No valid resubmission has
been made after the rejected attempt, and no target proof/disproof exists.

## Verified finite sampling and L² almost-periodicity

Mathlib's integer Roth theorem was inspected directly. It is proved via
corners and triangle removal, with `cornersTheoremBound` depending on a
tower-type regularity bound, not via a quantitatively strong density
increment. No hidden reciprocal-summability estimate was found.

Two new positive analytic scratch files compile with permitted axioms only.

### `Submission/FiniteSampling.lean`
Imports only `FormalConjecturesUtil`.
* `expect_pi_prod`, `expect_pi_apply`, `expect_pi_apply_mul`: exact expectation
  identities on finite Cartesian products, including independence of distinct
  coordinate evaluations.
* `expect_center_sq`, `sample_mean_center_sq`: the exact variance identity
  for a uniformly sampled finite empirical mean.
* `sample_mean_sq_bound`: for f:A→X→ℝ and a sample indexed by nonempty finite I,
  the expected squared error, summed over X, is at most
  `(sum_x E_a f(a,x)^2) / card I`.
* `card_le_two_card_sublevel`: a finite Markov inequality, treating B=0
  separately, showing at least half the inputs have error at most twice the
  mean bound.
* `many_good_samples`: packages the resulting large finite set of good samples.

### `Submission/CrootSisaskL2.lean`
Imports `Submission.FiniteSampling`.
* `common_translate_fiber`: packing/pigeonhole for good tuples L⊆A^I.
  Produces T⊆S and one common translated tuple, with
  `L.card*S.card <= (A+S).card^(card I)*T.card`.
  No analytic or characteristic-three modeling assumption is used here.
* `smooth A f x = E_{a∈A} f(x+a)`; `sqNorm f = sum_x f(x)^2`.
* `exists_many_L2_almost_periods`: in any finite abelian group, for nonempty
  A,S and n>0, there is T⊆S satisfying
  `A.card^n*S.card <= 2*(A+S).card^n*T.card`
  and, for s,t∈T,
  `sqNorm (smooth A f (·+s) - smooth A f (·+t)) <= (8/n)*sqNorm f`.

This is the L² Croot--Sisask argument from exact finite sampling and counting.
It is a real quantitative ingredient, not enough to settle even the required
integer three-term summability result. A higher-moment sampling estimate is
now being investigated, with the aim of obtaining the L^p version.
No higher-moment theorem has yet been proved. No strong integer density
increment, summability estimate, or original-target proof/disproof exists.
There are now 30 verified scratch files. Both new dependency oleans were built.

## Verified higher-moment sampling and L^p almost-periodicity

Two more new positive files compile with permitted axioms; their dependency
oleans were built.

### `Submission/FiniteSamplingMoments.lean`
Imports `Submission.FiniteSampling`.
* Finite-product expectations factor by sample-index fibers. A term in the
  centered moment expansion vanishes if an index occurs exactly once.
* If no index occurs exactly once in a map from `Fin (2*m)`, its image has
  at most m elements. Encoding its image in m slots bounds the number of
  such maps by `(card I)^m * m^(2*m)`.
* Each remaining product expectation is bounded using a maximum factor and
  the sum of even powers. No analytic probability axiom is used.
* Jensen for even powers and the centering inequality give
  `E (f-E f)^(2*m) <= 2^(2*m) * E f^(2*m)`.
* **`sample_mean_even_moment`**: for m>0 and nonempty finite I,A,
  `E_v (E_i f(v i) - E_a f a)^(2*m)` is at most
  `[2*m*(2*m)^(2*m)/(card I)^m] * E_a (f a)^(2*m)`.
* `sample_mean_even_moment_sum` sums this over arbitrary finite coordinates.
* **`many_good_moment_samples`**: at least half the tuples have total
  even-moment error at most twice that bound.

### `Submission/CrootSisaskLp.lean`
Imports `Submission.CrootSisaskL2` and `Submission.FiniteSamplingMoments`.
* `evenMoment f m = sum_x (f x)^(2*m)` is nonnegative.
* The same common-tuple packing argument as in L², now with the even-power
  triangle inequality, proves `exists_many_even_moment_periods`.
* The elementary integer estimate
  `2^(2*m+1)*(2*m)*(2*m)^(2*m) <= (256*m^4)^m`
  produces the main quantitative theorem:
* **`exists_many_Lp_almost_periods`**: for nonempty A,S in any finite abelian
  group, f:G→ℝ and n,m>0, some T⊆S satisfies
  `A.card^n*S.card <= 2*(A+S).card^n*T.card`, and for s,t∈T,
  `evenMoment (smooth A f (·+s)-smooth A f (·+t)) m`
  `<= (256*m^4/n)^m * evenMoment f m`.

The m^4 sample dependence is deliberately non-optimal but polynomial, which
is useful for a possible polylogarithmic density-increment argument.
This does NOT yet yield an integer Roth summability bound, much less all AP
lengths. Next possible step: smooth once more by a set B of density at least
`2^(-2*m)` to convert the L^(2m) estimate into a uniform estimate.
There are now 32 verified scratch files. The target still has its original
`sorry`, and no valid target submission exists.

## Verified uniform almost-periodicity after a second smoothing

`Submission/CrootSisaskSup.lean` imports `Submission.CrootSisaskLp` and now
compiles with permitted axioms only. Its olean was built.

* `smooth_sub`, `smooth_translate`: elementary identities for finite averages.
* `smooth_abs_le_of_evenMoment_le`: if `evenMoment g m <= e^(2*m)*B.card`,
  with m>0, B nonempty, and e>=0, then `|smooth B g x| <= e` for every x.
  Proof: Jensen, sum over the translated B bounded by the ambient even moment,
  then take the positive even-power comparison.
* `evenMoment_le_card_of_abs_le_one`: bounded f has moment at most |G|.
* **`exists_uniform_almost_periods`**: given nonempty A,B,S in a finite abelian
  group, |f|<=1, m,r>0, and `|G| <= 2^(2*m)*|B|`, there is T⊆S such that,
  writing `n=256*m^4*r^2`,
  `|A|^n*|S| <= 2*|A+S|^n*|T|`, and for all s,t∈T and x∈G,
  `|smooth B (smooth A f) (x+s) - smooth B (smooth A f) (x+t)| <= 2/r`.

This is a uniform Croot--Sisask-type estimate with polynomial moment cost.
There are now 33 verified scratch files. It remains only an ingredient: no
strong integer Roth density increment or reciprocal summability result has
been obtained, and the unrestricted target still has its original `sorry`.

Possible next analytical step (no code yet): prove autocorrelation moment
positivity and convolution/autocorrelation moment comparison by a finite
Gram identity, avoiding the need to first formalize Fourier theory. For
`C_g(x)=E_y g(y)g(y+x)` and `F(v)=E_x prod_i g(x+v_i)`, one expects
`E_x C_g(x)^p = E_v F(v)^2 >= 0`.
Similarly the convolution moment is `E_v F(v)F(-v)`, hence at most the
correlation moment by Cauchy--Schwarz and invariance under v↦-v. These would
support an unbalancing lemma; a dependent-random-choice sifting step and
structured/localized density increments are still missing. None of these
possible next steps is presently asserted as proved.

## Verified Gram identities, unbalancing, and 3AP sifting

Four further scratch files compile with permitted axioms only. Their oleans
were built in `.lake/build/lib/lean/Submission/`. The target `Spec.lean` remains
unchanged with its original `sorry`; these are NOT a target settlement.
There are now 37 verified scratch files.

### `Submission/CorrelationMoments.lean`
Imports `Submission.FiniteSampling`.
Namespace `Erdos3CorrelationMoments`.
* `expect_pow_eq`: converts a power of a finite average into an average of
  products over `Fin p`-indexed samples.
* `gram_moment`: generic finite identity for kernels
  `E_z f(x,z)g(y,z)`, with arbitrary finite index types X,Y,Z.
* `corr g x = E_y g(y)g(y+x)`;
  `conv g x = E_y g(y)g(x-y)`;
  `tensorMean g v = E_x prod_i g(x+v_i)`.
* `corr_moment_gram`: `E_x corr(g)(x)^p = E_v tensorMean(g,v)^2`.
* `conv_moment_gram`: the corresponding convolution moment is
  `E_v tensorMean(g,v)*tensorMean(g,-v)`.
* `corr_moment_nonneg`, `abs_conv_moment_le_corr`: all integer moments
  of autocorrelation are nonnegative, and dominate the absolute convolution
  moment. Proof uses finite Cauchy--Schwarz and v↦-v, not Fourier theory.
* `corr_center`, `conv_center`, specialized `*_center_one` when E g=1.
* `corr_center_moment_nonneg` and `abs_conv_center_moment_le_corr`:
  the same conclusions for centered correlations/convolutions of a mean-one g.

### `Submission/Unbalancing.lean`
Imports `Submission.CorrelationMoments`.
Namespace `Erdos3Unbalancing`.
* `pow_le_choose_mul (r p)`: `r^p <= (r*p).choose p`. Induction uses one
  nonnegative term in Vandermonde's identity.
* `unbalance`: if e>=0, r>0, e^p <= E g^p, and all moments through rp
  are nonnegative, then `(r*e)^p <= E(1+g)^(r*p)`.
* `unbalance_half`: with e=1/2 and r=8, the right side is at least
  `(9/8)^(8*p)`.
* `corr_moment_of_conv_center`: for E g=1, if
  `(1/2)^p <= |E(conv g-1)^p|`, then
  `(9/8)^(8*p) <= E(corr g)^(8*p)`.

### `Submission/CorrelationSifting.lean`
Imports `Submission.CorrelationMoments`.
Namespace `Erdos3CorrelationSifting`.
* `select_weight_cost`: if M,B>0, b>=0, E w>=M and E b<=B,
  some sample v satisfies `M<=2*w(v)` and `M*b(v)<=2*B*w(v)`.
  Select a maximum of `2*B*w-M*b`.
* `indicator A x` is the 0/1 indicator;
  `density A = |A|/|G|`;
  `common A v = {x | forall i, x+v_i in A}`;
  `pairDensity B q = E_x E_y 1_B(x)1_B(y)q(y-x)`.
* Exact identity `expect_pairDensity_common`:
  `E_v pairDensity(common A v,q) = E_t corr(1_A)(t)^p*q(t)`.
* `expect_density_common_sq`, `expect_bad_pairs_le`.
* `exists_sifted_intersection`: if E corr(1_A)^p >= M>0 and L>0,
  some nonempty common intersection B satisfies
  `M<=2*density(B)^2` and
  `M*pairDensity(B,1_{corr(1_A)<=L}) <= 2*L^p*density(B)^2`.
* `normalized A x = indicator A x / density A`, and normalization identities.
* `exists_normalized_sifted_intersection`: for A nonempty and L,H>0,
  if E corr(normalized A)^p >= H^p, some nonempty B=common A v satisfies
  `density(A)^(2*p)*H^p <= 2*density(B)^2` and
  `pairDensity(B,1_{corr(normalized A)<=L}) <=
    2*(L/H)^p*density(B)^2`.

### `Submission/ThreeAPSifting.lean`
Imports `Submission.CorrelationSifting` and `Submission.Unbalancing`.
Namespace `Erdos3ThreeAPSifting`.
* `conv_indicator_double`: if A is 3AP-free and a∈A,
  `conv(1_A)(a+a)=1/|G|`. Only the trivial pair contributes.
* `double_injOn`: doubling is injective on a 3AP-free set, even when the
  ambient finite abelian group has 2-torsion.
* `density_mul_le_expect`: transfers a lower bound on doubles of A into
  an ambient mean lower bound for a nonnegative function.
* `centered_moment_lower`: writing α=density(A), if `4<=|G|*α^2`
  and p is even, then `α*(3/4)^p <= E(conv(normalized A)-1)^p`.
* `large_corr_moment`: if additionally A is nonempty and `(2/3)^p<=α`,
  then `(9/8)^(8*p) <= E(corr(normalized A))^(8*p)`.
* **`sift_threeAPFree`**: under those hypotheses, there is
  `v : Fin (8*p) -> G` such that B=common A v is nonempty,
  `α^(8*p) <= 2*density(B)`, and
  `pairDensity(B,1_{corr(normalized A)<=17/16}) <=
     2*(17/18)^(8*p)*density(B)^2`.
  Equivalently, the fraction of bad ordered pairs in B is at most
  `2*(17/18)^(8*p)`.

### Remaining gap / possible next work
The finite correlation/unbalancing/DRC steps from the previous plan are now
verified. To proceed toward a strong integer *three-term* result, one could
combine `sift_threeAPFree` with uniform almost-periodicity of the high-correlation
set, then construct Bohr-set almost periods and a structured/localized density
increment. No such structured increment has been proved yet. An arbitrary
subset density increment is insufficient for iteration.

Even a completed strong 3AP theorem would not settle `erdos_3`, which requires
every fixed progression length. No unrestricted all-length estimate and no
fixed-length divergent counterexample exists in this work. No new submission
attempt was made on the incomplete target.

Technical notes:
* `single_le_sum` in the Vandermonde proof needed explicit `f`, `s`, and `a`
  parameters; otherwise the membership proof had an unresolved finset metavariable.
* Rewriting an inequality inside `ite` with `rw` produced an ill-typed motive
  because its Decidable instance depended on that inequality. `simp only` with
  the same rewriting lemmas handled the dependency correctly.

## Verified global Bohr-set density increment (11 further files)

Eleven further scratch files compile. All printed main-theorem axiom lists
are exactly subsets of `propext`, `Classical.choice`, `Quot.sound`. Their
oleans are built. There are now **48 verified scratch files**. The target
`Spec.lean` is still unchanged with `sorry`; no valid target submission exists.

### 38. `Submission/PopularAlmostPeriods.lean`
Imports `CorrelationSifting` and `CrootSisaskSup`.
Namespace `Erdos3PopularAlmostPeriods`.
* `diffSmooth B f x = E_{b,c∈B} f(x+c-b)`.
* `expect_indicator_mul`: `E_x 1_B(x) f(x) = density(B)*E_{b∈B} f(b)`.
* `pairDensity_eq_diffSmooth`: `pairDensity B f = density(B)^2*diffSmooth B f 0`.
* `smooth_neg_smooth`: `smooth (-B) (smooth B f) = diffSmooth B f`.
* Basic linearity, positivity and unit upper bounds for diffSmooth.
* `diffSmooth_zero_lower`: bad-pair fraction ≤δ implies `diffSmooth B f 0≥1-δ`.
* **`exists_popular_almost_periods`**: for nonempty B,S, 0≤f≤1,
  bad-pair fraction ≤δ, m,r>0 and `|G|≤2^(2m)|B|`, a nonempty T⊆S satisfies
  `|B|^n|S|≤2|B+S|^n|T|`, n=256*m^4*r^2; every pair s,t∈T is a uniform
  2/r-almost period of diffSmooth B f, and
  `diffSmooth B f(s-t)≥1-δ-2/r`.
* `sum_almost_periods`: finite sums of uniform almost-periods have the sum of
  their individual errors.

### 39. `Submission/DissociatedRiesz.lean`
Imports only `FormalConjecturesUtil`.
Namespace `Erdos3DissociatedRiesz`.
* `expect_char_mul_conj`: finite character orthogonality.
* `expect_energy_sum_chars`, `expect_norm_sq_sum_chars`: exact L² identity
  for a finite sum of distinct characters with arbitrary complex coefficients.
* **`riesz_l2`**: if D is `MulDissociated`, then
  `E_x ||prod_{χ∈D}(1+aχ*χ(x))||^2 = prod_{χ∈D}(1+||aχ||^2)`.
  Expand by subsets; dissociation makes distinct subset-product characters
  orthogonal. Uses Mathlib's dissociation definition, not a new axiom.

### 40. `Submission/ChangAnalytic.lean`
Imports `DissociatedRiesz`. Namespace `Erdos3ChangAnalytic`.
* `expect_re`: real part commutes with finite expectation.
* `expect_log_le_log_expect`: finite Jensen for positive f, proved from
  `log(f/M)≤f/M-1`, M=E f.
* `norm_one_add_pos` if ||z||<1.
* `log_norm_one_add_lower`, `log_norm_sq_one_add_lower`: for ||z||≤1/2,
  `log||1+z||≥Re z-||z||²`; uses Mathlib's complex logarithm error bound.
* `exists_unit_phase`: for z≠0, a unit complex u has Re(uz)=||z||.

### 41. `Submission/ChangSpectrum.lean`
Imports `ChangAnalytic` and `PopularAlmostPeriods`.
Namespace `Erdos3ChangSpectrum`.
* `spectrum A η = {χ | η≤||E_{a∈A}χ(a)||}` (normalized on A).
* **`dissociated_spectrum_bound`**: if A nonempty, 0<η≤1 and a dissociated
  D consists of η-large characters, then
  `|D|≤4*log(1/density(A))/η²`.
  Choose unit phases, c=η/4, use the Riesz L² identity for `aχ=c*uχ`,
  Jensen on A, and the logarithm lower bound.
* **`exists_spectrum_generators`**: spectrum A η lies in D.mulSpan for
  some D⊆spectrum A η with cardinality at most the natural floor of that
  bound. Uses Mathlib's maximal dissociated subset lemma.

### 42. `Submission/FiniteBohr.lean`
Imports `ChangSpectrum`. Namespace `Erdos3FiniteBohr`.
* `bohr D ρ = {x | forall χ∈D, ||χ(x)-1||≤ρ}`.
* Unit-product norm bound; Bohr zero, addition, and negation lemmas.
* `span_control`: if χ∈D.mulSpan and x∈bohr D ρ, ρ≥0, then
  `||χ(x)-1||≤|D|*ρ`.
* **`card_bohr_lower`**: for q>0,
  `|G|≤(2q+1)^(2|D|)*|bohr D (2/q)|`.
  Label real/imaginary parts of each χ(x) by a grid with 2q+1 cells.
  A largest common fiber is large; subtracting one of its points injects
  it into the indicated Bohr set.

### 43. `Submission/FiniteFourier.lean`
Imports `DissociatedRiesz`. Namespace `Erdos3FiniteFourier`.
* `hat f χ = E_x f(x)*conj(χ(x))`.
* `meanChar T χ = E_{t∈T}χ(t)`.
* Complex `cdiffSmooth T f x = E_{b,c∈T}f(x+c-b)`.
* `walkSmooth T n f`: n iterated symmetric smoothings (zero = f).
* `inversion`, `parseval`, `hat_shift`.
* `hat_cdiffSmooth`, `hat_walkSmooth`: multiplier is respectively
  `||meanChar T χ||²` and `||meanChar T χ||^(2n)`.
* `norm_hat_le`, `norm_meanChar_le_one`, `norm_char_sub_one_le_two`.

### 44. `Submission/SpectralAlmostPeriods.lean`
Imports `FiniteFourier` and `FiniteBohr`.
Namespace `Erdos3SpectralAlmostPeriods`.
* `walk_close`: if each difference of T is a uniform e-almost period of f,
  then `||walkSmooth T n f(x)-f(x)||≤n*e`.
* `shift_eq_sum`: exact Fourier expression for a translated difference.
* **`walk_shift_bound`**: if sum_χ||hat f χ||≤L and t satisfies
  `||χ(t)-1||≤η` on the 1/2-spectrum of T, then
  `||walkSmooth T n f(x+t)-walkSmooth T n f(x)||`
  `≤ L*(η+2*(1/2)^(2n))`.
* **`exists_bohr_almost_periods`**: for nonempty T and η≥0, such an f has
  D⊆spectrum T(1/2), `|D|≤floor(16 log(1/density(T)))`, and every
  `t∈bohr D (η/(|D|+1))` is a uniform almost period with error
  `2*n*e+L*(η+2*(1/2)^(2n))`.

### 45. `Submission/FourierSmoothing.lean`
Imports `FiniteFourier` and `PopularAlmostPeriods`.
Namespace `Erdos3FourierSmoothing`.
* Complex expectation with a mask, and real-to-complex expectation adapter.
* `uniform B`: normalized complex indicator; its Fourier transform is the
  conjugate of meanChar B.
* `uniform_energy`, `sum_meanChar_sq`: both relevant L² quantities are 1/density(B).
* **`cdiffSmooth_hat_l1`**: if ||f||≤1 and B nonempty, then
  `sum_χ||hat(cdiffSmooth B f)χ||≤1/density(B)`.
* `cdiffSmooth_ofReal`: compatibility with the prior real diffSmooth.

### 46. `Submission/PopularBohr.lean`
Imports `FourierSmoothing` and `SpectralAlmostPeriods`.
Namespace `Erdos3PopularBohr`.
* **`exists_popular_bohr`** combines the Croot--Sisask, sifting,
  Chang and spectral bounds. For B,S nonempty, 0≤f≤1, bad fraction≤δ,
  m,r>0, `|G|≤2^(2m)|B|`, and n≥0, η≥0, there exist T and D with
  the same packing bound and `|D|≤floor(16 log(1/density(T)))`.
* Every t∈bohr D(η/(|D|+1)) is a uniform almost period of diffSmooth B f
  with error `E=4*n/r+(1/density(B))*(η+2*(1/2)^(2n))`.
* Also `diffSmooth B f(t)≥1-δ-E` for all such t.

### 47. `Submission/CorrelationIncrement.lean`
Imports `PopularBohr`. Namespace `Erdos3CorrelationIncrement`.
* `smooth_comm`, `mean_smooth`, `smooth_nonneg`.
* `corr_smooth`: `corr(smooth B g)(x)=diffSmooth B(corr g)(x)`.
* `corr_zero`: correlation at zero = mean square.
* **`exists_translate_increment`**: for nonempty B,V, g≥0 with E g=1,
  if diffSmooth B(corr g)(s-t)≥C for all s,t∈V, then some x has
  `smooth V g x≥C`. Proof: average square≥C, mean=1, and compare with
  the maximum of smooth V g.
* **`bohr_translate_increment`**: if H≥0, H*f≤corr g pointwise and
  diffSmooth B f≥c on bohr D ρ, then some translate of bohr D(ρ/2)
  has mean g at least H*c.
* `popular_indicator_bound` supplies H*f≤corr g for
  f=1_{corr g>H}, g≥0.

### 48. `Submission/ThreeAPBohrIncrement.lean`
Imports `CorrelationIncrement` and `ThreeAPSifting`.
Namespace `Erdos3ThreeAPBohrIncrement`.
* `half_pow_le_density_iff`: converts the ambient cardinal condition into
  `2^(-2m)≤density(B)`.
* `smoothing_error_le`: with n=m+4, r=512(m+4), η=density(B)/128,
  the total spectral/averaging error E above is at most 3/128.
* `bad_fraction_le`: for p≥16, `2*(17/18)^(8p)≤1/256` (kernel rational arithmetic).
* `sampleMoment p = 8*p²+1`;
  `sampleLength p = 256*(sampleMoment p)^4*(512*(sampleMoment p+4))²`.
* `sifted_density_large_enough`: the sifted B automatically satisfies the
  required cardinal condition for m=sampleMoment p.
* **`exists_threeAPFree_bohr_increment`**: let α=density(A). If A is nonempty
  and 3AP-free, `4≤|G|*α²`, p is even, p≥16, and `(2/3)^p≤α`, then
  there exist nonempty B,T with
  `α^(8p)≤2*density(B)` and
  `|B|^(sampleLength p)*|G|≤2*|G|^(sampleLength p)*|T|`,
  plus a character set D with `|D|≤floor(16 log(1/density(T)))`, and x such that
  `smooth (bohr D (density(B)/(256*(|D|+1)))) (indicator A) x ≥ (33/32)*α`.

### What is and is not now proved
There is now a genuine **global structured Bohr-set density increment**,
not merely an unstructured-subset increment. This replaces the previously
missing global extraction step. It does NOT yet support iteration with
relative density inside a Bohr set. No localized counterpart, regular-Bohr
iteration, strong integer reciprocal-summability theorem, or result for
all progression lengths has been established.

Possible next work: regularity and approximate translation invariance of
finite Bohr sets, then localized versions of the moment/sifting/density-
increment steps. A global increment alone cannot be iterated as if a Bohr
set were a subgroup. Passing instead to a long AP inside each Bohr set
loses too much quantitatively for the desired harmonic summability.
The higher-progression-length gap remains independent and major.

Technical notes:
* Mathlib already has dissociation and maximal {−1,0,1}-span generators in
  `Combinatorics/Additive/Dissociation.lean`.
* `RCLike.norm_expect_le (K := ℂ)` needs the explicit scalar field.
* For `map_expect` with real part/conjugation, restrict the linear map to
  ℚ≥0. Sometimes first state the explicit pointwise expectation equality;
  `rw [map_expect ...]` does not see through the bundled map projection.
* Parenthesize subtractions inside `𝔼 x, (...)`; otherwise notation can
  parse the subtraction outside the expectation.
* Use a `funext` equality to replace `cdiffSmooth B (ofReal ∘ f)` as a
  whole function argument of `hat`; pointwise `simp_rw` alone did not do it.
* In a cardinal-power comparison, explicit Nat.mul_le_mul_* and
  Nat.pow_le_pow_left avoided `gcongr` choosing exponent monotonicity.

## Verified fixed-tolerance localization and weighted local moment gain (9 further files)

Nine further scratch files compile and have built oleans. All audited main
axiom lists use only `propext`, `Classical.choice`, and `Quot.sound`.
There are now **57 verified scratch files**. `Spec.lean` is unchanged with
its original `sorry`. No original-target proof/disproof or valid submission
has been obtained.

### 49. `Submission/BohrCovering.lean`
Imports `FiniteBohr`. Namespace `Erdos3BohrCovering`.
* `bohr_mono` in the radius.
* `card_le_grid_mul_bohr`: for nonempty A, if each χ∈D has its values on A
  within distance R>0 of a chosen complex center, then for q>0,
  `|A| <= (2q+1)^(2|D|) * |bohr D (2R/q)|`.
  Largest-fiber pigeonholing is performed on A, rather than all of G.
* `card_scale_le` is the centered-Bohr specialization.
* **`card_double_le`**: `|bohr D (2R)| <= 81^|D| * |bohr D R|`, R>0.

### 50. `Submission/BohrStableScale.lean`
Imports `BohrCovering`. Namespace `Erdos3BohrStableScale`.
* `exists_slow_step`: a positive initial value and an endpoint growth bound
  force a step growing by at most the chosen ratio.
* `stability_growth`: `(1+1/q)^(q(7d+1)) > 81^d`, q>0, from Bernoulli.
* `stabilitySteps D q = q*(7*|D|+1)`;
  `stabilityWidth D q R = R/(2*stabilitySteps D q)`.
* **`exists_stable_radius`**: for R>0,q>0 there is s with
  `R <= s-width`, `s+width <= 2R`, and
  `|bohr D(s+width)| <= (1+1/q)*|bohr D(s-width)|`.
  This is a **fixed-tolerance** stability result. It does NOT assert the
  usual simultaneous regularity at every sufficiently small tolerance.

### 51. `Submission/BohrTranslation.lean`
Imports `BohrStableScale` and `PopularAlmostPeriods`.
Namespace `Erdos3BohrTranslation`.
* `indicator_shift_shell`: if y∈bohr D h, h>=0, then
  `|1_{B_r}(x+y)-1_{B_r}(x)| <= 1_{B_{r+h}\B_{r-h}}(x)`.
* `shell_card_le`: a (1+δ) inner/outer size ratio bounds the shell by δ|B_r|.
* **`normalized_bohr_translation_le`**: under that size ratio, r,h,δ>=0,
  `E_x |normalized(B_r)(x+y)-normalized(B_r)(x)| <= δ` for y∈B_h.
* `abs_expect_le_expect_abs` for finite real expectations.
* `weighted_translation_bound`: an L¹ translation bound δ controls
  pairings with |f|<=M by δM.
* `expect_normalized_mul`, `smooth_weighted` identify conditional averages
  with normalized ambient weighted means.
* **`smooth_bohr_translation_le`**: `|smooth B_r f(z+y)-smooth B_r f(z)|<=δM`
  for |f|<=M and y∈B_h.
* `exists_translation_stable_bohr` combines this with the stable radius.

### 52. `Submission/BohrLocalAverages.lean`
Imports `BohrTranslation`. Namespace `Erdos3BohrLocalAverages`.
* `abs_pairing_le`: general L¹ pairing bound for two weights.
* `mean_abs_smooth_sub_le`: averaging small L¹ translations preserves the
  same error bound.
* **`normalized_bohr_absorption`**: normalized stable B_r is an approximate
  identity under smoothing by any nonempty W⊆B_h, with L¹ error <=δ.
* `mean_smooth_exchange`.
* **`mean_bohr_smooth_close`**: for |f|<=M, smoothing by W changes its
  conditional B_r mean by at most δM.
* `relativeDensity A B = |A∩B|/|B|`, plus conditional indicator identity.
* **`exists_dense_window`**: some b∈B_r has
  `smooth W (indicator A) b >= relativeDensity A B_r - δ`;
  the translated W lies in B_{r+h}.

### 53. `Submission/WeightedCorrelation.lean`
Imports `CorrelationMoments` and `Unbalancing`.
Namespace `Erdos3WeightedCorrelation`.
* General finite `gram_product` and `familyTensor` identities.
* `corr_product_gram`: the mean of a product of correlations is an
  average square. The convolution counterpart is a mixed tensor average.
* `corr_product_nonneg`, `abs_conv_product_le_corr`.
* **`weighted_corr_moment_nonneg`**:
  `E_t corr h(t)*(corr g(t))^p >= 0` for all real g,h and all natural p.
* `abs_weighted_conv_moment_le`, `weighted_comparison_of_even`:
  when h is even, the same correlation weight compares the absolute
  convolution moment with the correlation moment.
* `mean_corr h = (E h)^2`.
* `weighted_unbalance`, **`weighted_unbalance_half`**: the earlier
  unbalancing argument works with arbitrary weights whose weighted moments
  are nonnegative, and with a nonnegative mass factor M.

### 54. `Submission/LocalCorrelationCentering.lean`
Imports `BohrLocalAverages` and `WeightedCorrelation`.
Namespace `Erdos3LocalCorrelationCentering`.
* `crossCorr`, `crossConv`, symmetry/commutativity and exact subtraction expansions.
* `indicator_translation_bound`, `cross_indicator_close`.
* **`corr_center_local`**, **`conv_center_local`**: if f is supported on B,
  E f=β=density(B), |f|<=L, and normalized B has L¹ translation error δ at
  ±t, then centering f by 1_B differs from subtracting β at the correlation
  level by at most `δ*β*(2L+1)`. The convolution version also requires B even.
* Bohr indicators are even.
* `localNormalized A B = indicator(A)/relativeDensity(A,B)`;
  its global mean is density(B) when nonempty A⊆B.
* **`bohr_local_centering`**: applies both estimates on every small shift
  of a stable Bohr set, with error `δ*β*(2/α+1)`, α=relativeDensity(A,B).

### 55. `Submission/RobustWeightedUnbalancing.lean`
Imports `WeightedCorrelation`.
Namespace `Erdos3RobustWeightedUnbalancing`.
* `robust_even_power_bound`: for v>=0, |u-v|<=1/256 and q even,
  `u^q <= (65/64)^q*v^q + (65/256)^q`.
* `robust_power_gap`: for q>=2,
  `(65/64)^q*(17/16)^q + (65/256)^q <= (9/8)^q`.
* **`weighted_moment_transfer`**: a 9/8 even-moment gain under a probability
  weight survives a pointwise error 1/256 on its support as a 17/16 gain.
* Weighted comparison and nonnegativity after dividing correlations by β>0.
* **`local_weighted_unbalance`**: for f>=0 and an even nonnegative mean-one h,
  a weighted convolution deficit for g/β forces a 17/16 moment gain for
  corr(f)/β, provided
  `|corr g(t) - (corr f(t)-β)| <= β/256` on the support of corr h.

### 56. `Submission/StableBohrIncrement.lean`
Imports `CorrelationIncrement` and `BohrLocalAverages`.
Namespace `Erdos3StableBohrIncrement`.
* **`exists_stable_bohr_increment`**: if the global correlation criterion
  holds throughout bohr D ρ, it can realize the same gain Hc on a translate
  of bohr D r which is stable at any preselected tolerance 1/q.
  Choose the stable r in [ρ/4,ρ/2] so its difference set remains inside
  the original popular Bohr set. There is no loss in the gain factor.
* This avoids an unjustified assumption that an arbitrary Bohr set obtained
  from the global increment is already regular.

### 57. `Submission/LocalThreeAPMoment.lean`
Imports `LocalCorrelationCentering`, `RobustWeightedUnbalancing`, `ThreeAPSifting`.
Namespace `Erdos3LocalThreeAPMoment`.
* `doubledMass Z w = (sum_{a∈Z} w(a+a))/|G|`.
* `weighted_double_lower`, `weighted_deficit`: doubling injectivity on a
  3AP-free set transfers a pointwise deficit at doubled centers to an even
  weighted moment. If mass >=(2/3)^p and the pointwise deficit is at least
  3/4, the moment is at least (1/2)^p.
* `conv_localNormalized`, `local_convolution_at_double`: for A⊆B 3AP-free,
  alpha=relativeDensity(A,B), and a∈A,
  `conv(localNormalized A B)(2a)/density(B) = 1/(alpha²*|B|)`.
* **`local_threeAP_weighted_gain`**: let B=bohr D r be stable at window h
  and error δ, A⊆B nonempty and 3AP-free, Z⊆A, and u>=0 be even with mean 1.
  Assume:
  - `8 <= alpha²*|B|`;
  - `δ*(2/alpha+1) <= 1/256`;
  - corr u is supported on bohr D h;
  - all doubled centers 2a for a∈Z belong to bohr D h;
  - p>0 is even;
  - **`(2/3)^p <= doubledMass Z (corr u)`**.
  Then
  `E_t corr u(t)*(corr(localNormalized A B)(t)/density(B))^(8p)`
  `>= (17/16)^(8p)`.
  The bold mass condition is an explicit, not yet universally discharged,
  hypothesis. This theorem is NOT an unconditional localized increment.

### Remaining mathematical gaps and next possible route
Fixed-tolerance regularization, translation stability, local centering,
weighted positivity, and a conditional local weighted moment gain are now
verified. The original conjecture is still not proved or disproved.

1. Need to arrange enough weighted mass on admissible centers while retaining
   local relative density and bounds suitable for iteration.
2. Need a genuinely relative/local sifting, Croot--Sisask and Chang extraction.
   Existing global theorems depend on ambient densities, including the very
   small density of the current Bohr set. Applying them unchanged would not
   give an iteration with the required harmonic-summability bound.
3. Need the quantitative localized iteration and integer summability even
   for 3-term APs.
4. Longer AP lengths remain a separate major gap.

A possible next idea (reasoned only; NOT formalized): in a finite group where
x↦2x is bijective, let C be a small symmetric Bohr set and take
u = normalized(2·C). Then `corr u(2a) = corr(normalized C)(a)`, and the doubled
mass of centers from A is a symmetric C-average of 1_A. Thus one could try to
choose a common translation with both base-set density and weighted center
mass near alpha, using stable averages and a no-density-increment hypothesis.
This may avoid estimating the center mass by a crude |inner C|/|C| ratio,
which would introduce a dimension-dependent loss into the moment parameter.
No such simultaneous-density selection or doubled-weight identity is coded yet.

Similarly, weighted DRC can be viewed through a Gram identity with an extra
factor u: intersections may be confined to a small localization set, and
sample shifts restricted to a slightly enlarged base Bohr set. Boundary
stability might then cancel ambient base-density factors. This is a plan,
not a proved local sifting theorem. Relative Chang/period extraction remains
an additional substantial task.

Technical notes:
* In `Finset.image`, explicitly annotate `(fun (x : A) => (x:G)-x0)` when
  the domain is a subtype. Without this, Lean coerced the entire finset to G,
  invalidating the intended fiber-injectivity proof.
* `|expression|*M` lexes `|*` as a token; insert whitespace or parentheses.
* To rewrite two different quotients' powers, specify `div_pow a c` and
  `div_pow b c`; a second bare `rw [div_pow]` can unfold the denominator's
  own quotient instead of the other summand.

## Continuation: doubled weights and simultaneous windows verified

### 58. `Submission/DoubledWeights.lean`
Imports `LocalThreeAPMoment`. Namespace `Erdos3DoubledWeights`.
Compiled successfully; olean built; main theorem axiom checks contain only
`propext`, `Classical.choice`, `Quot.sound`.

* `density_image`, `normalized_image`, `corr_normalized_image`: transport
  of normalized correlations under additive equivalences.
* `doublingEquiv` for a group with bijective doubling.
* `corr_pairing`, `normalized_corr_pairing`: correlation-weighted pairings
  equal symmetric averages.
* **`doubled_mass_eq_diffSmooth`**:
  `doubledMass Z (corr(normalized(2*C))) = diffSmooth C (indicator Z) 0`.
* `window A U x := U.filter (fun a => x+a ∈ A)`; subset, monotonicity,
  relative-density and 3AP-freeness transport.
* `diffSmooth_window`: if C-C⊆U, the local window's symmetric average
  equals the original set's shifted symmetric average.
* Support, nonnegativity and evenness lemmas for normalized correlations.
* `doubled_weight_support`: if C⊆bohr D rho, the correlation of the doubled
  normalized image is supported in bohr D (4*rho).
* **`doubled_mass_window`** combines the exact identities:
  `doubledMass (window A U x) (corr(normalized(2*C)))
    = diffSmooth C (indicator A) x`, provided C-C⊆U.

### 59. `Submission/SimultaneousWindows.lean`
Imports `DoubledWeights`. Namespace `Erdos3SimultaneousWindows`.
Compiled successfully; olean built; main theorem axiom checks contain only
`propext`, `Classical.choice`, `Quot.sound`.

* `exists_two_large`: if E f≥a, E g≥b, f≤U and g≤V on a finite nonempty
  type, some i satisfies f(i)≥a+b-V and g(i)≥a+b-U. Proof maximizes f+g.
* `mean_diffSmooth_exchange`: exchange the outer conditional average with
  the two symmetric averages.
* **`mean_bohr_diffSmooth_close`**: if C-C lies in the stability window,
  symmetric smoothing changes the conditional stable-Bohr mean by at most
  delta*M for |f|≤M.
* **`exists_simultaneous_averages`**: write alpha for A's density in a stable
  outer Bohr set. If both local averages have pointwise upper bound
  (1+epsilon)*alpha, some common center in the outer Bohr set has
  `smooth W (indicator A)` and `diffSmooth C (indicator A)` both at least
  `(1-epsilon)*alpha - 2*delta`.
* **`exists_simultaneous_windows`**: translated-window and doubled-mass
  formulation, including the subset relation between center and base
  windows. The two no-increment bounds remain explicit hypotheses.

### Status after this continuation
`Submission/Spec.lean` remains unchanged, with the original `sorry`.
There is no complete proof or disproof. The two new files resolve the exact
weight identity and simultaneous selection identified previously, but do not
supply a relative sifting/period-extraction iteration. More importantly,
this entire localized analytic route concerns three-term progressions;
the full conjecture requires every progression length. No reduction closing
that separate gap has been established. These auxiliary results must not be
represented as a settlement or submitted as a complete target proof.

Minor elaboration lessons from this continuation:
* Give the homomorphism in `AddEquiv.ofBijective` an explicit `G →+ G` type.
* `change` can expose coercions from additive equivalences and `Equiv.addRight`
  when simp does not unfold them. `Equiv.addRight_apply` is not a lemma here.
* Use fresh witness names when destructing image memberships.
* Parenthesize the complete integrand of finite expectations, e.g.
  `(𝔼 j : I, (f j+g j))`; otherwise the notation may leave `g j` outside
  the binder.

## Continuation: an all-length finite binary-jet invariant case

### 60. `Submission/DigitPolynomialCase.lean`
Imports `BinarySymmetryCase` and `FiniteKernelCase`.
Namespace `Erdos3DigitPolynomialCase`. Compiles; olean built. All three
printed main axiom lists contain only `propext`, `Classical.choice`,
`Quot.sound`. Source contains no proof holes.

Definitions and construction:
* `wordPoly` associates to a least-significant-first binary word w the
  integer polynomial whose coefficients are its digits.
* `doubleWord w := complement(w) ++ w`.
  If L=length(w), its integer value is
  `(2^L-1)*(Nat.ofDigits 2 w+1)`.
  Its digit polynomial is
  `onesPoly(L) + (X^L-1)*wordPoly(w)`.
* `encode r w` repeats this operation r times; its length is `2^r*length(w)`.
* **`encode_jet`**: for same-length binary words u,v,
  `(X-1)^r` divides `wordPoly(encode r u)-wordPoly(encode r v)`.
  Thus their first r Taylor coefficients at X=1 agree.
* `encode_value_affine`: encoding all m-bit inputs is affine with positive
  step (for m>0); the step is the product of the factors `2^(2^j*m)-1`.
* **`binary_jet_progression`**: for every r,k there are common-length
  binary words forming a positive-step k-AP as integers, all with the same
  jet modulo `(X-1)^r`. Length `2^r*(k+1)` suffices.

All-length special case:
* `JetInvariant A r`: membership in A is preserved under replacing binary
  words of the same length when their digit polynomials agree modulo
  `(X-1)^r`. This is an explicit additional hypothesis.
* `wordPoly_sandwich`: the jet congruence is preserved on insertion into
  any common low and high binary blocks.
* `template_hole`: if a JetInvariant set avoids a k-AP, it cannot contain
  the first word of the above template at any binary block position.
  Otherwise replacing that block by the other template words yields a k-AP.
* **`jet_invariant_uniform_holes`**: every dyadic section of such a set has
  a missing residue at the same fixed binary depth L. The dyadic kernel
  need NOT be finite for this statement.
* **`jet_invariant_noAP_summable`**: use the earlier uniform-hole counting
  argument to get `count A ((2^L)^j) <= (2^L-1)^j`, hence reciprocal
  summability.
* **`jet_invariant_contains_ap`**, **`jet_invariant_case`**: reciprocal
  divergence plus finite-jet invariance implies an AP of every finite
  length, and therefore the exact conclusion of the target theorem.

This is an all-length positive special case, not a proof of the original
conjecture. An arbitrary subset of naturals need not have finite-jet
invariance. No divergence-preserving extraction, approximation, or other
reduction to this class has been proved. The earlier uniform extremal
harmonic-bound gap remains unchanged.

`Submission/Spec.lean` still contains the unchanged original `sorry`.
No complete proof or disproof has been obtained or submitted.

## Continuation: finite binary-jet extraction is impossible in general

### 61. `Submission/JetExtractionBarrier.lean`
Imports `DigitPolynomialCase` and `WeightedIntersectionCheck` (the latter's
olean was rebuilt). Namespace `Erdos3JetExtractionBarrier`. Compiles and
olean built. All four printed axiom lists contain only `propext`,
`Classical.choice`, `Quot.sound`.

* `count_digits_ofDigits`: the count of a nonzero digit is unchanged when
  a padded base-q word is converted to its canonical expansion.
* `blockColor q a n`: parity of the count of base-q digit a in n.
* **`blockColor_ne`**: replacing a nonzero digit a by a different digit b
  in any aligned base-q position changes this binary color.
* **`monochromatic_replacement_summable`**: a set closed under the digit
  replacement a->b and monochromatic for this coloring has summable
  reciprocals. Every q-adic section must omit the digit a; the existing
  uniform-hole count bound yields geometric decay.
* `jet_block_replacement`: finite-jet invariance supplies exactly the
  required replacement closure for congruent binary blocks of length L,
  viewed as digits in base q=2^L.
* **`exists_jet_separator`**: for each r, a binary coloring has the
  property that every eventually monochromatic r-jet-invariant set is
  reciprocal-summable. Choose the second and third words of the 3-AP
  template, so 0<a<b<q. Replacing a by b increases n, hence preserves
  any tail beyond the finite exceptional set.
* **`divergent_subset_without_jet_invariant_subsets`**: applying the
  verified countable-coloring diagonal thinning, every divergent A has
  a divergent B⊆A such that, for all C⊆B and all natural r,
  `JetInvariant C r` implies reciprocal summability of C.
* **`no_divergent_jet_invariant_extraction`**: negates the universal
  auxiliary principle asserting that every divergent set contains a
  divergent invariant subset for some finite jet order.

This conclusively rules out that direct extraction route from arbitrary
sets to file 60's positive special case. It does NOT exhibit an AP-free
divergent set: the thinned sets may contain APs with varying differences.
It is NOT a negation of the original conjecture.

Status: the missing unrestricted finite extremal harmonic bound has not
been proved, and no genuine counterexample has been constructed.
`Submission/Spec.lean` remains unchanged, including its original `sorry`.
No complete proof or disproof has been submitted.

Technical detail: `List.count_replicate` needed to be included explicitly
in simp; it was not automatically used to discard trailing zero padding.

## Continuation: rechecked the unrestricted extremal route; no new completion

The exact reduction remains:
  for every fixed k>=3, sum_j maxCard(k,4^j)/4^j must converge.
No estimate deciding this series was obtained in this continuation.

Rechecked the available library bounds and earlier obstructions:
* The library's Behrend lower bound, evaluated at geometric scales, has
  profile exp(-C*sqrt(j)). This is a summable lower-bound profile and does
  not yield divergence of the extremal series or a counterexample.
* Qualitative extremal-density decay is insufficient, as already formally
  demonstrated in StructuralCountCheck.lean.
* No available higher-length quantitative theorem was found that supplies
  the required summable upper bound.

An additional informal route considered was a quantitative coloring of a
k-AP-free finite set into 3-AP-free pieces, with a sufficiently small loss
that a strong 3-term bound could be transferred. Bounded-color extraction
was already excluded in ColorReductionCheck.lean. No valid bound for the
unbounded number of colors was proved here, so this is not a lemma or a
completion route currently available for use.

No new proof file was added in this continuation. Spec.lean is unchanged
and still contains sorry. No complete proof or disproof has been obtained.

## Continuation: genuinely relative DRC sifting verified

### 62. `Submission/LocalCorrelationSifting.lean`
Imports `LocalCorrelationCentering` and `DoubledWeights`.
Namespace `Erdos3LocalCorrelationSifting`. Compiles, olean built, and all
five printed main axiom lists contain only the three permitted axioms.

* `localCommon A C v := C ∩ common A v`.
* `expect_restrict`, `restricted_corr_gram`: if A-C⊆V, correlations
  sampled over V are exactly global correlations divided by density(V),
  when the two test points belong to C.
* **`expect_pairDensity_localCommon`**: for v sampled in `(Fin p → V)`,
  the mean pair cost of `localCommon A C v` is
  `E_t corr(1_C)(t) * (corr(1_A)(t)/density(V))^p * q(t)`.
  The q=1 specialization gives the mean squared size.
* `local_bad_pairs_le` bounds the corresponding low-correlation cost.
* **`exists_local_sifted_intersection`**: given a weighted moment
  `H^p <= E_t corr(normalized C)(t)*(corr(1_A)(t)/sigma)^p`, finds a
  nonempty local intersection with squared density at least
  `density(C)^2*(sigma*H/density(V))^p / 2`, and bad-pair fraction at most
  `2*(L/H)^p` for the threshold L.
* `corr_localNormalized` gives the exact local normalization identity.
* **`exists_relative_sifted_intersection`**: if A⊆B has relative density
  alpha, and `density(V) <= H*density(B)`, the above estimate cancels the
  ambient B-density completely. The selected S⊆C satisfies
  `alpha^p <= 2*relativeDensity S C`, with the same bad-pair fraction.
* **`exists_bohr_sifted_set`**: specialize V to bohr(D,r+rho), with
  A⊆bohr(D,r), C⊆bohr(D,rho), and cardinal enlargement factor at most H.
* **`sift_local_threeAPFree`**: combine file 57's conditional moment gain
  with relative sifting. Under the same center-mass hypothesis, and
  C symmetric in bohr(D,rho), 2rho<=h, obtain nonempty S⊆C with
  `alpha^(8p) <= 2*relativeDensity S C` and bad-pair fraction at most
  `2*(33/34)^(8p)` for the correlation threshold 33/32.
  The necessary enlargement bound 17/16 follows from the existing
  centering-error bound and Bohr stability.

This resolves the previously missing *symmetric relative DRC* step. It
is not an iterated density increment and not a proof of the target.
The center-mass hypothesis is explicit, though files 58-59 provide a
conditional way to arrange it.

### Important next-step analysis (NOT formalized)
Simply applying the global Croot--Sisask and Fourier extraction lemmas
still incurs ambient-density losses. Even localizing symmetric smoothing
can introduce the doubling ratio |C-C|/|C|, exponential in the old rank.
A polynomial dependence on the old rank in each rank increment would be
too costly over O(log(1/alpha)) iterations. This must not be silently
ignored in the quantitative bookkeeping.

A possible asymmetric route:
1. Smooth the outer weight C by a much smaller U. If C is stable with
   L1 error delta, its weighted moment changes by at most
   delta*alpha^(-p), since corr(localNormalized A B)/density(B)<=1/alpha.
   Choose delta quasipolynomially small in alpha.
2. Average over centers x∈C, then select one such that the moment under
   the *cross*-correlation of normalized C and normalized(x+U) remains
   large. Positivity/unbalancing was already done before this selection;
   it need not hold for the resulting cross-weight.
3. Prove asymmetric DRC: obtain S1⊆C and S2⊆x+U with relative density
   product >=alpha^(2p)/2 and few bad cross-differences. Each individual
   relative density is then >=alpha^(2p)/2.
4. Truncate the popular-difference indicator to C-(x+U) (and a small
   enlargement), whose size is O(|C|) by stability, rather than |2C|.
   The Fourier l1 bound for smoothing by S1 and S2 can use Cauchy--Schwarz
   and |hat(normalized S2)|<=1:
     ||hat f * hat(mu_S1) * hat(mu_S2)||_1
       <= ||f||_2 / sqrt(density S1)
       = O(1/sqrt(relativeDensity S1 C)).
   This avoids both the ambient density and the inner-set size ratio.
5. For localized Croot--Sisask, sample the small S2 and smooth by the large
   S1. Restrict the error norm to an O(|C|)-size region containing all
   relevant evaluations. The norm-to-sup factor then involves relative
   density of S1 in C, while |S2+T|/|S2| is controlled inside the stable
   small set U. A theorem with these restricted-domain hypotheses still
   needs to be proved.
6. Relative Chang extraction may be approached using approximately
   dissociated characters under normalized C: small Fourier coefficients
   of all nonempty signed products bound the local Riesz-product integral.
   Maximality leaves products with a large C Fourier coefficient; stability
   of C controls their phases on a small old-Bohr window. This too remains
   unproved.

Even successful completion of this route gives a three-term bound only.
There is still no justified all-length extension.

Technical note: the generic `expect_pi_prod` lemma chooses a classical
DecidableEq on its index type. Instantiating it at Fin p did not rewrite
against the canonical Fin-indexed function Fintype. Using the already
Fin-indexed `expect_pow_eq` avoided the nondefinitional Fintype mismatch.

`Submission/Spec.lean` remains unchanged with its original `sorry`.
No complete proof or disproof has been obtained or submitted.

## Continuation: asymmetric sifting, localization, and Fourier control verified

### 63. `Submission/AsymmetricSifting.lean`
Imports `LocalCorrelationSifting`. Namespace `Erdos3AsymmetricSifting`.
Compiles; olean built; all printed main theorem axiom lists are permitted.

* `crossPairDensity C D q = E_{x,y} 1_C(x)1_D(y)q(y-x)`.
* `crossAverage C D f = E_{c∈C,d∈D} f(d-c)`.
* Identities relate crossPairDensity, crossAverage, and pairings with
  `crossCorr (normalized C) (normalized D)`.
* **`expect_crossPairDensity_localCommon`**: the asymmetric DRC identity
  when shifts are sampled from V. **Only A-C⊆V is required**; the first
  factor alone forces the integrand to vanish off the sampling domain.
* **`exists_asymmetric_sifted_intersections`**: a cross-weighted p-moment
  at scale sigma with gain H selects S⊆C and T⊆D with density product
  at least `density(C)*density(D)*(sigma*H/density(V))^p/2` and bad
  cross-pair fraction at most `2*(L/H)^p`.
* **`exists_relative_asymmetric_sets`**: with A⊆B of relative density
  alpha and density(V)<=H*density(B), both selected relative densities
  satisfy `alpha^(2p) <= 2*relativeDensity(S,C)` and the analogous bound
  for T in D. The proof first bounds their product, then uses each
  relative density's upper bound of one.

### 64. `Submission/AsymmetricLocalization.lean`
Imports `AsymmetricSifting`. Namespace `Erdos3AsymmetricLocalization`.
Compiles; olean built; main theorem axiom lists are permitted.

* `shiftSet U x = U.image (fun u => x+u)`, with size, density and averaging
  identities.
* **`exists_localized_crossAverage`**: if C is a stable Bohr set and U
  lies in its stability window, for |f|<=M some x∈C satisfies
  `crossAverage C (shiftSet U x) f >= crossAverage C C f - delta*M`.
  Proof applies the earlier stable-mean theorem to
  `g(y)=E_{c∈C} f(y-c)`, then maximizes its U-average.
* `local_correlation_bound`: for nonempty A⊆B,
  `0 <= corr(localNormalized A B)(t)/density(B) <= 1/alpha`.
* **`exists_asymmetric_moment`**: a symmetric H^p moment localizes to a
  cross-weighted K^p moment, provided
  `delta*(1/alpha)^p <= H^p-K^p`. There is no |C|/|U| loss.
* **`localize_and_sift`** combines that selection with file 63. It gives
  S⊆C and T⊆x+U with both relative-density bounds and few bad cross-pairs.
* `cross_differences_in_enlargement`: T-S lies in x+bohr(D,r+h), not in
  bohr(D,2r), when S⊆bohr(D,r) and U⊆bohr(D,h).
* `crossPairDensity_truncate`: restricting the test function to a set
  containing all these cross-differences leaves the pairing unchanged.

### 65. `Submission/AsymmetricFourierSmoothing.lean`
Imports `AsymmetricLocalization` and `FourierSmoothing`.
Namespace `Erdos3AsymmetricFourierSmoothing`. Compiles; olean built;
main axiom lists are permitted.

* Real `crossSmooth` and complex `ccrossSmooth` average f(x+t-s) over
  s∈S and t∈T, plus real/complex and ordinary-smoothing compatibility.
* `hat_ccrossSmooth`: multiplier is
  `meanChar(T,chi)*conj(meanChar(S,chi))`.
* **`ccrossSmooth_hat_l1_sq`**:
  `(sum_chi |hat(ccrossSmooth S T f)(chi)|)^2 <= E|f|^2/density(S)`.
  No inverse density of T is paid; use |meanChar(T)|<=1, Cauchy--Schwarz,
  and Parseval for f and normalized S.
* **`ccrossSmooth_hat_l1_sq_support`**: for |f|<=1 supported on W, the
  same squared norm is at most density(W)/density(S).
* **`ccrossSmooth_hat_l1_sq_relative`**: if S⊆C has relative density eta
  and density(W)<=K*density(C), this bound is K/eta, independently of
  both ambient density(C) and the inner-set density(T).
* `crossSmooth_truncate` gives exact truncation on an evaluation window
  when all needed cross-differences stay inside W.

### Remaining work after files 63-65
The asymmetric plan's DRC, moment localization, and Fourier-l1 control
are now verified, not merely proposed. Restricted-domain Croot--Sisask
and relative Chang extraction remain substantial missing steps. The
popular-difference truncation must be valid on the full evaluation window
used by those later steps, not just at zero.

For eventual density increment realization, the asymmetric analogue of
the existing symmetric argument should use the identity
  E_{y∈V} crossSmooth S T (corr(1_A)) y
    = E_x smooth S (1_A)(x) * smooth T (smooth V (1_A))(x).
Since the second factor is bounded by max_z smooth V(1_A)(z), and the
first has mean density(A), a high left side gives a translate of V with
increased relative density. This identity/selection has not yet been
formalized in the asymmetric development.

No localized iteration or integer summability theorem has been completed.
All higher AP lengths are still an independent gap. Spec.lean is unchanged
with its original sorry; no complete proof or disproof has been submitted.

## Continuation: asymmetric increment and supported almost-periods verified

### 66. `Submission/AsymmetricIncrement.lean`
Imports `AsymmetricFourierSmoothing` and `CorrelationIncrement`.
Namespace `Erdos3AsymmetricIncrement`. Compiles; olean built; printed
main theorem axiom lists contain only permitted axioms.

* `crossCorr_smooth`: cross-correlation of the S- and T-smoothed g is
  `crossSmooth S T (corr g)`.
* `mean_crossSmooth_corr`: the V-average of this cross smoothing equals
  `E_x smooth S g x * smooth T (smooth V g) x`.
* `exists_translate_from_crossAverage`: for nonnegative g of positive
  mean mu, a cross-smoothed correlation V-average at least c*mu gives
  some translate x with `c <= smooth V g x`.
* `local_asymmetric_increment`: for nonempty A subset B of relative
  density alpha, if `H*f <= corr(localNormalized A B)/density B` and
  `c <= crossSmooth S T f` throughout V, there is a translate with
  `H*c*alpha <= smooth V (indicator A) x`. No ambient-density loss.
* `popular_local_asymmetric_increment`: specializes f to the indicator
  of popular differences with correlation threshold H.

Only the increment window V, not V-V, needs the lower bound.

### 67. `Submission/SupportedAlmostPeriods.lean`
Imports `AsymmetricIncrement` and `CrootSisaskSup`.
Namespace `Erdos3SupportedAlmostPeriods`. Compiles; olean built; main
axiom lists contain only permitted axioms.

* `evenMoment_le_card_of_support`: if m>0, |f|<=1 and f vanishes outside
  W, then `evenMoment f m <= W.card`.
* `exists_supported_uniform_almost_periods`: replaces the previous
  ambient-cardinality condition by `W.card <= 2^(2*m)*B.card`, for f
  supported on W. The original global Lp sampling theorem suffices.
  Sample count n=256*m^4*r^2; cardinal bound
  `|A|^n |Q| <= 2 |A+Q|^n |P|`; global uniform error 2/r.
* `exists_crossSmooth_almost_periods`: samples the small inner T and
  smooths with the large outer -S. Requires `|W| <= 2^(2*m)|S|`, and
  the cardinal cost involves only `|T+Q|/|T|`.
* `truncate W f = indicator W * f`, with positivity/support bounds.
* `crossAverage_lower`: few bad cross-pairs implies average at least
  1-delta.
* `crossSmooth_truncate_zero`: truncation exact at zero if W contains
  T-S.
* `exists_supported_popular_periods`: combines all these facts to give
  nonempty P subset Q with the cardinal bound, global uniform almost-
  periods for the truncated smoothing, value >=1-delta at zero, and
  value >=1-delta-2/r on P-P.

Important correction to the previous plan: a restricted-domain
Croot--Sisask theorem is NOT needed. Truncating f first makes the
existing global Lp error support-sensitive. Truncation only needs to be
exact at zero: its lower bounds anywhere transfer to f by positivity.

### Remaining obstacles
Relative Chang/spectrum extraction, quantitative local iteration, and
an integer three-term summability theorem remain uncompleted. The
all-length extension is an independent unresolved issue. The target
in Spec.lean remains unchanged with its original sorry.

Possible relative spectrum route (not proved): use approximate
orthogonality of distinct subset-products under normalized C, with
error epsilon. A d-frequency Riesz product has local L2 integral at
most `(1+c^2)^d + epsilon*(1+c)^(2*d)`. Fix a rank cutoff R and take
epsilon <= 4^(-(R+1)); Jensen then bounds d in terms of relative
log-density log(2/tau), not ambient density. A maximal approximately
dissociated family leaves each large-spectrum character a signed
product of new generators and a character with C-mean >epsilon.
Stability of C controls the latter character's phase by delta/epsilon.
This should feed the existing `walk_shift_bound`, which accepts phase
control directly rather than requiring global Chang.

## Continuation: relative spectrum extraction verified

### 68. `Submission/RelativeRiesz.lean`
Imports `ChangSpectrum`. Namespace `Erdos3RelativeRiesz`.
* `ApproxDissociated C epsilon D`: distinct subset-products of D have
  cross means over C of norm at most epsilon.
* Monotonicity under restricting D.
* `expect_norm_sq_sum_chars_le`: approximate orthogonality bounds the
  local mean squared norm by `sum |a_i|^2 + epsilon*(sum |a_i|)^2`.
* `relative_riesz_l2`: local Riesz-product L2 mean is at most
  `prod(1+|a_chi|^2) + epsilon*prod(1+|a_chi|)^2`.

### 69. `Submission/RelativeChang.lean`
Imports `RelativeRiesz` and `BohrTranslation`.
Namespace `Erdos3RelativeChang`.
* `mean_subset_le`: for A subset C and f nonnegative,
  `(|A|/|C|)*E_A f <= E_C f`.
* `relative_spectrum_bound`: if D is approximately dissociated on C,
  all its characters have A-mean at least eta, and
  `epsilon*4^|D| <= 1`, then
  `|D| <= 4 log(2/(|A|/|C|))/eta^2`.
  The proof uses local Riesz, log Jensen, and aligned phases.

### 70. `Submission/RelativeSpectrum.lean`
Imports `RelativeChang` and `FourierSmoothing`.
Namespace `Erdos3RelativeSpectrum`.
* `extension_obstruction`: if D is approximately dissociated but
  inserting chi fails, then some s,t subset D satisfy
  `epsilon < |meanChar C ((prod s)*chi/(prod t))|`.
* `exists_relative_spectrum_generators`: if the above real rank bound
  is <R+1 and `epsilon*4^(R+1)<=1`, a maximal family D in the A-spectrum
  has |D|<=R and the obstruction representation holds for every
  large-spectrum character outside D. No circular epsilon choice.

### 71. `Submission/RelativeSpectrumPhase.lean`
Imports `RelativeSpectrum`. Namespace `Erdos3RelativeSpectrumPhase`.
* `meanChar_mul_phase_le`:
  `|meanChar C chi|*|chi(y)-1| <= E_x |normalized C(x+y)-normalized C(x)|`.
* `phase_le_of_large_mean`, `subset_prod_phase`, and `obstruction_phase`.
* `exists_relative_spectrum_phase`: the relative spectrum is controlled
  by new-generator Bohr phases and any reference-set stability window:
  `|chi(y)-1| <= delta/epsilon+2*|D|*rho`.

### 72. `Submission/RelativeBohrPeriods.lean`
Imports `RelativeSpectrumPhase` and `SpectralAlmostPeriods`.
Namespace `Erdos3RelativeBohrPeriods`.
* `shift_bound_from_walk`: packages the existing walk approximation
  and Fourier-tail argument for any supplied large-spectrum phase bound.
* `exists_relative_almost_periods`: a set P subset C of global uniform
  almost-periods gives D of rank controlled by `16 log(2/(|P|/|C|))`.
  For y in bohr(D,rho) satisfying C-translation error <=delta, the new
  uniform error is
  `2*n*e + L*(delta/epsilon+2*|D|*rho+2*(1/2)^(2*n))`,
  where L bounds the Fourier l1 norm.
* `exists_relative_bohr_almost_periods`: if C=bohr(E,r) has stable
  growth at width h, this applies on `bohr(E union D,min h rho)`.

All five files compile, their oleans were built, and printed main
axiom lists contain only propext, Classical.choice, Quot.sound.
The previously missing relative Chang/phase extraction is now proved.
Integration with supported sampling, local parameter choices and
iteration remains. None of this supplies an all-length extension.
Spec.lean is unchanged and still contains the original sorry.

### 73. `Submission/SupportedBohrIncrement.lean`
Imports `SupportedAlmostPeriods` and `RelativeBohrPeriods`.
Namespace `Erdos3SupportedBohrIncrement`. Compiles with permitted axioms.
* `sampling_log_bound`: from `a^n*q <= 2*b^n*p` obtains
  `log(2/(p/q)) <= log(4*(b/a)^n)`.
* `supported_l1_le`: `|W| <= 2^(2*m)|S|` bounds the Fourier l1 norm of
  the truncated asymmetric smoothing by `2^m`.
* `exists_supported_relative_popular_periods`: combines support-sensitive
  sampling, relative Chang and Fourier extraction. Given bad-pair
  fraction b and W containing T-S, obtains D of rank at most R whenever
  `16 log(4*(|T+Q|/|T|)^(256*m^4*r^2)) < R+1` and
  `epsilon*4^(R+1)<=1`. For y in bohr(D,rho) with Q-translation error
  <=delta, the ORIGINAL (untruncated) smoothing is at least
  `1-b-[4*n/r+2^m*(delta/epsilon+2*|D|*rho+2*(1/2)^(2*n))]`.
* `supported_bohr_increment`: for Q=bohr(E,q) stable at width h, and
  `H*f <= corr(localNormalized A B)/density B`, the preceding popular
  lower bound yields an actual translate of
  `bohr(E union D,min h rho)` with relative density at least H times
  that lower bound times relativeDensity(A,B).

This completes the integration of asymmetric supported sampling with
relative spectral extraction and increment realization. Parameters and
popular-pair hypotheses remain explicit, not silently assumed.

### Next priorities after file 73 (not yet proved)
1. Convenient explicit parameters for the loss bound:
   n=m+10, r=1024*n, epsilon=4^(-(R+1)),
   delta=epsilon/(1024*2^m), rho=1/(2048*(R+1)*2^m).
   The sampling contribution is 1/256; the phase contribution <=1/512;
   the Fourier tail <=1/512. Thus total loss <=1/128, and a bad-pair
   fraction <=1/128 gives popular smoothing >=63/64. At H=33/32 this
   gives a relative density gain exceeding 129/128.
2. Choose nested stable Bohr radii, connect files 57-59 and 63-64 to
   file 73, including center mass, two simultaneous averages, asymmetric
   localization, enlargement sizes, and the inner sampling ratio.
3. Prove quantitative local iteration and transfer to integers, giving
   reciprocal summability for three-term-progression-free sets.
4. There remains NO proved all-length extension. Ordinary Fourier
   control is not sufficient for arbitrary-length progression counts;
   an unsupported induction from the three-term case must not be used.

Spec.lean still has its original single sorry. No complete proof or
disproof has been obtained or submitted in this continuation.

## Continuation: explicit parameters, geometry and stable local 3AP increment

### 74. `Submission/BohrIncrementParameters.lean`
Explicit definitions `walkSteps m=m+10`, `sampleAccuracy m=1024*walkSteps m`,
`sampleCount m=256*m^4*sampleAccuracy(m)^2`,
`stabilityDenominator m R=1024*2^m*4^(R+1)`,
`spectralTolerance R=1/4^(R+1)`,
`translationTolerance m R=1/stabilityDenominator(m,R)`,
`generatorRadius m R=1/(2048*(R+1)*2^m)`.
`total_loss` proves the total smoothing loss is <=1/128.
`fixed_supported_increment` proves the relative gain 129/128 under
bad-pair fraction <=1/128 and popularity threshold 33/32.

### 75. `Submission/StableSupportedIncrement.lean`
`rankBudget m=32*(1+m*sampleCount m)` is polynomial in m.
`rankBudget_bound` verifies the rank budget whenever the inner sumset
ratio is <=2^(2m). `increment_all_windows` gives the 129/128 gain on
ANY nonempty subset of the output Bohr window. `stable_increment`
therefore regularizes the next Bohr radius at an arbitrary prescribed
fixed tolerance without losing the density gain.

### 76. `Submission/BohrTransport.lean`
`transportChars e D` precomposes characters by e^{-1}.
Cardinality of the frequency set is unchanged, and
`image e (bohr D r)=bohr (transportChars e D) r`.
Growth is preserved. `doubled_bohr_subset` puts the doubled image in
bohr(D,2r); `doubled_bohr_mass` identifies the corresponding center
mass with a symmetric average. IMPORTANT: transporting the old
frequencies through doubling does NOT double the old rank.

### 77. `Submission/LocalSiftedIncrement.lean`
`bad_fraction_small`: p>=536 implies 2*(66/67)^p<=1/128.
`size_of_relative_lower` converts sigma<=2*relativeDensity(S,C),
|W|<=2|C| and 4<=2^(2m)*sigma into |W|<=2^(2m)|S|.
`shift_sumset_subset`, `enlargement_le_twice` supply the geometric bounds.
`moment_to_stable_increment`: a (17/16)^p weighted local moment,
localized to (67/64)^p with threshold 33/32, produces the stable
129/128 increment. All nesting, support, enlargement, and budget
hypotheses are explicit, with rankBudget m independent of ambient
density and old rank.

### 78. `Submission/RelativeStableBohr.lean`
`windowDenominator d z=4*z*(7*d+1)` and
`relativeWidth D z r=r/windowDenominator(D.card,z)`.
`RelativeStable D z r` is growth <=1+1/z at this relative width.
`exists_relative_stable`: one exists between R and 2R.
Transport through an additive equivalence preserves this condition.
`initial_window_card_bound`: if w>=relativeWidth(D,z,r)/4, then
|bohr(D,r)| <= (16*windowDenominator(D.card,z)+1)^(2*D.card)*|bohr(D,w)|.

### 79. `Submission/LocalThreeAPIncrement.lean`
`localShrinkDenominator d z m = 16*windowDenominator(d,z)*
  windowDenominator(d,1)*windowDenominator(d,stabilityDenominator(m,rankBudget m))`.
`local_threeAP_increment` combines the local 3AP moment with all later
steps, and selects the auxiliary U and Q radii automatically.
Inputs: stable base radius r and stable outer radius c with
4c<=relativeWidth(E,z,r), nonempty three-AP-free A subset bohr(E,r),
admissible centers Z subset A of doubled mass >=(2/3)^p, p>=67 even,
base size >=8/alpha^2, explicit centering/localization errors and
4<=2^(2m)*alpha^(16p).
Output: F of rank <=E.card+rankBudget(m), a RelativeStable F z s with
  min(c/localShrinkDenominator, generatorRadius)/2 <= s <= c,
s>0, and a translate of bohr(F,s) with density >=129/128*alpha.
The old frequencies are transported through doubling, not unioned
with a second copy; hence no multiplicative old-rank loss.

All files 74-79 compile, oleans built, printed main axiom lists are
only the permitted axioms. Center mass still needs elimination via
the simultaneous-window dichotomy, followed by quantitative iteration.

Next simplification for iteration: use the SAME fixed stability
parameter z for the original base, the localized base W and outer C.
Choose z fine enough for localization, not merely centering. Then the
direct-increment branches W and C already satisfy the same invariant;
there is no need to infer a larger-window stability statement from
stability at a finer tolerance (which would be invalid).

Spec.lean remains unchanged with its original sorry. The all-length
extension is still an independent unproved gap.

### 80. `Submission/LocalDensityStep.lean`
**The explicit center-mass hypothesis is now eliminated.**
Defines `coverFactor d z=(16*windowDenominator(d,z)+1)^(2d)` and
`stepShrinkDenominator d z m=64*windowDenominator(d,z)^2*localShrinkDenominator(d,z,m)`.
`local_density_step`: given a stable Bohr base, a nonempty 3AP-free A
of relative density >=a>0, and numerical parameters fixed from a,
if `32*coverFactor <= a^2*|base|`, there is a stable new base with:
* rank <= old rank+rankBudget(m),
* radius >= min(old radius/stepShrinkDenominator,generatorRadius)/2,
* radius positive and <=old radius,
* some translate of relative density >=1025/1024 times the old density.
Proof: select stable W and C at nested radii. If either direct average
or symmetric C-average already increases density, use that branch.
Otherwise simultaneous windows retain >=511/512 of the density and
center mass. File 79 then gives the stronger 129/128 gain, enough to
absorb the retention loss. Uses one fixed z throughout.

### 81. `Submission/FiniteThreeAPBound.lean`
**The quantitative local step is now iterated.**
`generatorDenominator m=2048*(rankBudget(m)+1)*2^m`,
`iterationScale b z m=2*stepShrinkDenominator(b,z,m)*generatorDenominator(m)`,
`iterationVolume b z m t=(4*iterationScale(b,z,m)^t+1)^(2b)`.
Monotonicity and radius/volume lemmas give an i-step state of rank
<=i*rankBudget, radius >=iterationScale^(-i), and density
>= (1025/1024)^i*a. If the ambient group is too large, each state is
large enough to take another step. At t steps density >1 contradicts
the universal upper bound.
`finite_threeAP_bound` proves, for b=t*rankBudget(m),
  a^2*|G| < 32*coverFactor(b,z)*iterationVolume(b,z,m,t),
under the explicit numerical parameter conditions and odd-group
hypothesis (doubling bijective).

### 82. `Submission/DyadicThreeAPBound.lean`
**All numerical parameter hypotheses are instantiated.**
For l in Nat, set:
* dyadicDensity(l)=2^(-l),
* momentParameter(l)=2*(l+40),
* supportParameter(l)=8*momentParameter(l)*(l+1)+1,
* stableParameter(l)=2^(supportParameter(l)+20),
* iterationSteps(l)=1024*(l+1),
* finalRank(l)=iterationSteps(l)*rankBudget(supportParameter(l)).
Every mean/mass/centering/localization/support/growth condition is
proved. The localization error is exactly 1/2097152; the support
budget is exactly 4.
`threeAPFree_card_lt_dyadic_bound`: a 3AP-free subset of an odd finite
abelian group of density >=2^(-l) forces
  |G| < dyadicGroupBound(l),
where the latter is an explicit natural expression from file 81.

Files 80-82 compile, oleans built, printed axiom lists permitted.

Next: bound dyadicGroupBound(l) by 2^(P(l)) for an explicit polynomial
P. A crude polynomial exponent suffices; no need to optimize degree
or coefficients. One can bound each polynomial factor n by 2^n,
while keeping stableParameter and the spectrum stability denominator
as exact powers of two. This gives an explicit polynomial exponent
of degree about 31 without difficult constant normalization. Then
transfer to integers and prove three-term reciprocal summability by
counting scales at each dyadic density level. Still no all-length
extension: Spec.lean remains unchanged with its original sorry.

## Milestone: the three-term reciprocal-summability case is complete

### 83. `Submission/PolynomialThreeAPThreshold.lean`
A crude, explicit polynomial exponent is sufficient; no optimization
of degree/constants is needed.
* `scaleExponent b k m=3k+2m+3*rankBudget(m)+35b+50` bounds the logarithm
  to base two of iterationScale when z=2^k.
* `thresholdExponent l`, using m=supportParameter(l), b=finalRank(l),
  k=m+20, t=iterationSteps(l), is
  `5+2l+2b*(k+7b+8)+2b*(3+scaleExponent(b,k,m)*t)`.
* `dyadicGroupBound_le_pow_threshold`: dyadicGroupBound(l)<=2^thresholdExponent(l).
* `thresholdPolynomial : Polynomial Real` explicitly represents the
  exponent; `eval_thresholdPolynomial` is proved.
* `polynomial_geometric_summable` and `summable_threshold_weight` prove
  summability of thresholdExponent(l)*2^(-l).
* `threeAPFree_card_lt_pow_threshold`: the finite odd-group bound with
  the polynomial-exponent threshold.

### 84. `Submission/IntegerThreeAPBound.lean`
Embed S subset range N into ZMod(2N+1). Doubling is bijective, the
embedding preserves cardinality and 3AP-freeness, and the density
loss is at most a factor of four.
* `integer_threeAP_density_bound`: if density(S,[0,N))>=2^(-l), then
  `N<2^thresholdExponent(l+2)`.
* `integer_threeAP_density_lt`: contrapositive density estimate above
  that threshold.

### 85. `Submission/GeometricThresholdSummability.lean`
* `exists_dyadic_band`: for 0<x<=1, some l has 2^-l<x<=2*2^-l.
* `summable_of_dyadic_thresholds`: if 0<=f(j)<=1 and
  j>=P(l) implies f(j)<=2^-l, and sum_l P(l)*2^-l converges, then f
  is summable. Proof uses the nonnegative family
  g(l,j)=2^-l when j<P(l), zero otherwise, and Tonelli.
* `initialCount A N = range(N).filter membership(A)`.
* `scaleDensity A j = |A intersect [0,2^j)|/2^j`.
* `threeAPFree_scaleDensity_summable`: this sequence is summable for
  every three-term-free set of naturals.

### 86. `Submission/ThreeAPReciprocalSummability.lean`
* `harmonicScale A j=|A intersect [0,2^(j+1))|/2^j` is summable for
  three-term-free A.
* `finite_harmonic_le`: every finite S subset A has reciprocal sum
  bounded by tsum harmonicScale(A), using fibers of Nat.log 2.
* **`threeAPFree_reciprocal_summable`**:
  `ThreeAPFree A -> Summable (fun a : A => 1/(a : Real))`.
* **`nonsummable_contains_three_term_AP`**:
  `not Summable (fun a : A => 1/(a : Real)) ->
     exists S subset A, S.IsAPOfLength 3`.
  The final step explicitly constructs a nondegenerate Nat progression;
  it does not rely on a degenerate interpretation of AP length.

All files 83-86 compile, their oleans are built, and printed theorem
axiom lists use only propext, Classical.choice, Quot.sound.

### Updated mathematical status
The entire previously missing THREE-TERM chain is now complete:
local weighted moments -> asymmetric localization/sifting -> supported
sampling -> relative spectrum extraction -> stable local increment ->
center elimination -> quantitative iteration -> polynomial-exponent
finite bound -> integer transfer -> reciprocal summability.
Do not continue treating relative Chang, center mass, local iteration,
or integer three-term summability as unproved gaps.

**The original conjecture remains unproved.** Its conclusion asks for
arbitrarily long APs. The three-term theorem alone does not imply this,
and no genuine all-length reduction or counterexample has been found.
The next mathematical work must address this independent higher-length
obstacle, rather than silently substituting a length-three conclusion.
The earlier barrier files remain relevant: fixed-shift divergence,
bounded-color reductions, and unconditional structured extraction are
not available as shortcuts.

`Submission/Spec.lean` has not been changed; it still contains its
original sorry. No completed submission has been made in this turn.

## Higher-order development (files 87–90)

### 87. `Submission/QuadraticFourAPBarrier.lean`
Proves the finite-field quadratic-phase obstruction to controlling four-term
counts by ordinary linear Fourier coefficients. A primitive quadratic phase
has every Fourier coefficient squared equal to 1/|F|; the four phases with
coefficients 1,-3,3,-1 have mixed four-term progression average exactly one.
`arbitrarily_flat_fourAP` makes every linear Fourier coefficient arbitrarily
small while preserving that average. This is a complex-function obstruction,
not a divergent AP-free set or a disproof of the original conjecture.

### 88. `Submission/FiniteUniformity.lean`
Defines complex multiplicative derivatives and recursive `uniformityPower`.
Index n means the 2^(n+1)-th power of U^(n+1), so index 1 is U2^4 and index 2
is U3^8. Proves nonnegativity, boundedness, scalar invariance, the U2 Fourier
fourth-moment identity, quadratic U2^4=1/|F|, and quadratic higher uniformity=1.

### 89. `Submission/LinearFormsUniformity.lean`
Proves arbitrary-length generalized von Neumann bounds over finite fields.
For n+2 distinct slopes and pointwise one-bounded functions, the 2^(n+1)-th
power of the mixed average norm is bounded by `uniformityPower n` of any
chosen function. Uses iterative Cauchy–Schwarz elimination and even-power
Jensen. This is a counting theorem, not a higher-order inverse theorem.

### 90. `Submission/UniformityCounting.lean`
Proves a telescoping counting lemma with error (n+2)*eta when centered higher
uniformity is at most eta^(2^(n+1)). For a nonempty set A, n+2 distinct slopes,
and density(A)^(n+1)*|F| >= 4, sufficiently small centered uniformity forces a
nontrivial configuration. `pattern_free_uniformity_lower` gives the explicit
contrapositive lower bound. All files 87–90 compile; oleans were built and
printed theorem axiom lists use only the three permitted axioms.

The original conjecture is still not settled. The independent missing step
is a higher-order structural/increment mechanism with sufficiently efficient
quantitative dependence to imply reciprocal summability for every fixed
length. Ordinary Fourier information is insufficient in general; qualitative
Szemeredi or qualitative inverse theorems alone also do not supply the needed
summability bound. `Spec.lean` remains unchanged with its original sorry.

## Quantitative pre-inverse steps (files 91–92)

### 91. `Submission/DerivativeSpectrum.lean`
Defines `iterDerivative f h` for h : Fin n -> G and proves
`uniformityPower (n+m) f = E_h uniformityPower m (iterDerivative f h)`.
The elementary U2 inverse estimate selects a Fourier coefficient whose squared
norm is at least U2^4. `many_large_derivative_coefficients`: for one-bounded f
with uniformityPower(n+1,f) >= delta >= 0, at least (delta/2)*|G|^n derivative
tuples have a Fourier coefficient of squared norm >= delta/2. This does not
assert coherence of those selected frequencies.

### 92. `Submission/SpectralGraphEnergy.lean`
Defines normalized `graphEnergy H xi` by counting (h,k,t) with all four of
h,k,h-t,k-t in H and xi(h)*xi(k-t)=xi(k)*xi(h-t).
* `kernel_fourth_bound`: two Cauchy–Schwarz steps for a finite complex kernel.
* `correlation_fourth_le_graphEnergy`: for |f|,|b| <= 1, b supported in H,
  |E_h b(h)*hat(derivative f h)(xi h)|^4 <= graphEnergy H xi.
  The proof expands the kernel Gram energy, changes variables, and uses exact
  character orthogonality. It imposes no unjustified linearity on xi.
* `large_U3_spectral_graph`: if uniformityPower 2 f >= delta >= 0, selects H,xi
  with |H| >= (delta/2)*|G|, every selected derivative coefficient squared >=
  delta/2, and graphEnergy >= (delta/2)^4.
* `many_derivative_spectral_graphs`: if uniformityPower (n+2) f >= delta,
  at least (delta/2)*|G|^n n-fold derivative slices have such graphs, each
  with domain size >= (delta/4)*|G|, coefficient squared >= delta/4, and
  graphEnergy >= (delta/4)^4.

Files 91–92 compile, oleans built, and printed axiom lists contain only
propext, Classical.choice, Quot.sound. These establish quantitative derivative
extraction and a first coherence estimate, not a complete inverse theorem.
The next structural steps would need to linearize/integrate the frequency
graphs and make the different derivative slices compatible. Even a resulting
inverse theorem must still have sufficiently efficient relative increment
bounds to yield all-length reciprocal summability. No such complete mechanism
has been proved here. The original Spec.lean remains unchanged with its sorry.

## Quantitative BSG and Freiman-frequency extraction (files 93–100)

### 93. `Submission/FiniteGraphPaths.lean`
An explicit dense bipartite graph path lemma. `dense_graph_many_paths`:
for a relation of density >= epsilon > 0 between finite nonempty vertex
sets I,J, selects S subset I of relative size >= epsilon/4 such that every
pair i,k in S has normalized alternating length-four path count at least
epsilon^5/4096. The codegree is E_j 1_R(i,j)*1_R(k,j).
`path_density_eq` identifies the average product of codegrees with the
cardinality of the explicit path finset divided by |I|*|J|^2.
Proof: a neighborhood with small bad-pair mass, pruning high-bad-degree
vertices, then many intermediate vertices with two large codegrees.

### 94. `Submission/SmallDifferenceExtraction.lean`
For a finite A in any abelian group and a dense relation a+b in D,
`restricted_sumset_small_difference` yields B subset A with
  |B| >= (epsilon/4)*|A|,
  (epsilon^5/4096)*|A|^3*|B-B| <= |D|^4.
Alternating length-four paths inject into four-tuples of sum labels, and
different endpoint differences occupy disjoint label-value fibers.
The ambient group need not be finite. The DecidableEq argument is explicit.

### 95. `Submission/BalogSzemerediGowers.lean`
No BSG theorem was found in Mathlib, so this supplies one.
`popular_sums_of_energy` uses the exact sum-representation second moment.
`balog_szemeredi_gowers`: for nonempty finite A, delta>0, and
  E[A] >= delta*|A|^3,
there is B subset A with
  |B| >= (delta/8)*|A|,
  delta^9*|B-B| <= 2097152*|A| = 2^21*|A|.
Again the ambient abelian group can be infinite.

### 96. `Submission/FrequencyGraph.lean`
`frequencyGraph H xi = {(h,xi h) : h in H}`, using AddChar's additive group
structure (which corresponds to multiplication of character values).
An explicit bijection between parallelogram parameters and additive-energy
quadruples proves
  graphEnergy H xi = E[frequencyGraph H xi]/|G|^3.
`large_U3_small_difference_graph`: for |f|<=1 and U3^8>=delta>0, selects H,xi
with
  |H| >= (delta^5/256)*|G|,
  |hat(derivative f h)(xi h)|^2 >= delta/2 for h in H,
  delta^36*|Gamma-Gamma| <= 2^57*|G|.
This bridges the analytic energy bound to genuine small-difference extraction.

### 97. `Submission/CharacterSeparation.lean`
For a nontrivial character chi, the fraction of points with |chi(x)-1|<=1
is at most 2/3. Independent finite sampling gives
`exists_small_separating_set`: any finite family C of nontrivial characters
is separated from 1 by at most 2*(Nat.log 2 |C|+1) evaluation points, with
fixed separation |chi(x)-1|>1. `separation_grid_cost` proves that for this
number m of points,
  17^(2*m) <= (2*(|C|+1))^20.
Thus the constant-radius grid loss is polynomial, not exponential in |C|.

### 98. `Submission/FreimanFrequencyGraph.lean`
`verticalDifferences H xi` is the set of chi for which (0,chi) lies in
(Gamma+Gamma)-(Gamma+Gamma).
`FreimanOn H xi` says a+b=c+d in H implies xi(a)+xi(b)=xi(c)+xi(d).
`FreimanOn.isAddFreimanHom` connects it to Mathlib's exact order-two predicate.
`exists_freiman_restriction`: there is H' subset H, FreimanOn H' xi, with
  |H| <= (2*(|verticalDifferences H xi|+1))^20*|H'|.
Proof: logarithmically many evaluations separate the nonzero vertical
obstructions; select a large translate fiber of a dual Bohr set of radius
1/4. Every four-term frequency difference in that fiber lies in the radius-1
Bohr set and therefore must vanish if it is vertical.

### 99. `Submission/VerticalDifferenceBound.lean`
A vertical translate of a graph is disjoint from every distinct vertical
translate, because the first coordinate determines the second. Hence
  |verticalDifferences|*|Gamma| <= |3*Gamma-2*Gamma|.
Mathlib's Pluennecke–Ruzsa theorem gives
  |verticalDifferences| <= (|Gamma-Gamma|/|H|)^5.
`small_difference_freiman_restriction`: if |Gamma-Gamma|<=K*|H| and H is
nonempty, then the Freiman restriction satisfies
  |H| <= (2*(K^5+1))^20*|H'|.
This is polynomial loss in the difference ratio.

### 100. `Submission/U3FreimanExtraction.lean`
The combined theorem `large_U3_freiman_graph`: for |f|<=1, delta>0, and
uniformityPower 2 f>=delta, there are nonempty H and xi such that
* FreimanOn H xi (exact order-two Freiman homomorphism),
* every selected derivative Fourier coefficient squared is >=delta/2,
* with K=2^65/delta^41,
    (delta^5/256)*|G| <= (2*(K^5+1))^20*|H|.
All quantitative losses in this pre-inverse extraction are polynomial in
delta^{-1}; there is no implicit ambient-size dependence.

Files 93–100 compile, their oleans have been built, and printed axiom lists
contain only propext, Classical.choice, Quot.sound.

### Current remaining gap
The quantitative graph-energy -> BSG -> exact Freiman restriction chain is
now proved. Do not treat BSG or this restriction step as an assumption.
The extracted map is only order-two Freiman on its domain; it has NOT been
extended to a locally additive map or integrated into a quadratic phase.
For extending a difference map to multi-sumsets one may need higher-order
Freiman preservation (six/eight-term relations), which is not automatic
from the order-two statement. The vertical-obstruction method can plausibly
be adapted to those higher fixed orders, but that adaptation is not proved.
Even a complete U3 inverse theorem would not by itself settle the original
conjecture: an efficient relative density increment and arbitrary-order
extension sufficient for reciprocal summability are still missing.
`Submission/Spec.lean` remains unchanged with the original sorry. No complete
proof or disproof, and no new proof submission, has been made.

### Technical notes
Several new helper files take an explicit DecidableEq G argument. Omitting it
and then applying a theorem to G x AddChar G C can trigger a multi-million-
heartbeat definitional-equality timeout between classical and product
DecidableEq instances. The issue was fixed by parameterizing files 94–95
explicitly. For membership in frequencyGraph, use mem_frequencyGraph rather
than unpacking its closed image definition with an incompatible DecidableEq.
Finite Pi types also depend on the index DecidableEq: instDecidableEqFin and
a classical Fin decision can produce different (propositionally equal)
Fintype structures. For the sampling moment in file 97, a direct proof via
Fintype.prod_sum avoids that definitional-equality issue. Indicator predicates
under Fin quantifiers may similarly carry different decidable-forall
instances; pointwise case splits normalize them safely.

## Higher Freiman preservation and local additive extension (files 101–106)

### 101. `Submission/HigherFreimanRestriction.lean`
Generalizes the vertical-separation argument to every positive Freiman order n.
`verticalN n H xi` consists of characters chi with (0,chi) in n*Gamma-n*Gamma.
`restrictionExponent n = 4*(8*n+1)`.
`exists_higher_freiman_restriction` gives H' subset H with
  |H| <= (2*(|verticalN n H xi|+1))^(restrictionExponent n)*|H'|,
and the actual Mathlib predicate `IsAddFreimanHom n (H' : Set G) Set.univ xi`.
Uses dual Bohr radius 1/(2n), grid parameter 4n, logarithmically many tests,
and multiset sum control. Helper lemmas handle sums in nH, centered sums,
graph sums, and sums of Bohr-set elements.

### 102. `Submission/HigherFreimanExtraction.lean`
* `higher_vertical_card_le_ratio`: |verticalN| <= (|Gamma-Gamma|/|H|)^(2n+1).
* `small_difference_higher_restriction`: from difference ratio <=K, the
  n-Freiman restriction has loss (2*(K^(2n+1)+1))^(restrictionExponent n).
* `large_U3_higher_freiman_graph`: for U3^8>=delta>0, extracts nonempty H,xi
  with all derivative Fourier coefficients squared >=delta/2, exact n-Freiman
  preservation, and
    (delta^5/256)*|G| <= (2*(K^(2n+1)+1))^(restrictionExponent n)*|H|,
    K=2^65/delta^41.
All losses are polynomial in delta^{-1} for each fixed n. Here n is the
number of summands preserved by the Freiman map; this is still a U3 theorem,
NOT a general U^n inverse theorem.

### 103. `Submission/LocalFreimanExtension.lean`
A fully algebraic extension theorem for maps between arbitrary abelian groups.
`DifferenceRep H m x` records positive/negative multisets of cardinal m,
all entries in H, with difference of sums x.
* Representations exist exactly on mH-mH.
* A 2m-Freiman map makes the represented value independent of the representation.
* A 3m-Freiman map makes these values locally additive.
`differenceExtension H m f` is a choice-defined global function, zero off
its representation domain. Its properties are proved, not postulated.
`exists_local_additive_extension`: for m>0 and a 3m-Freiman f, there is F with
  F(0)=0,
  F(a-b)=f(a)-f(b) for a,b in H,
  F(x+y)=F(x)+F(y) whenever x,y,x+y all lie in mH-mH.
This closes the previous representation-consistency and extension gap.

### 104. `Submission/FiniteBogolyubov.lean`
An explicit finite Bogolyubov lemma. For nonempty H of density alpha, there
is a character set D with |D|<=8/alpha^2 and
  bohr D (1/2) subset 2H-2H.
The proof takes the spectrum where squared Fourier coefficients of 1_H are
at least alpha^3/8, bounds its cardinality by Parseval, and proves the real
part of the fourfold correlation is >=alpha^4/4 throughout the Bohr set.
Nonzero correlation implies membership in the fourfold difference set.
This result uses ordinary Fourier analysis on H, after Freiman extraction;
it does not assert that ordinary Fourier analysis directly counts four-APs.

### 105. `Submission/LocalBilinearExtraction.lean`
* `freiman_local_bilinear`: a six-Freiman map on H extends to a character-valued
  map F, locally additive on a rank <=8/density(H)^2, radius-1/2 Bohr set.
  It also agrees with all xi(a)-xi(b) on differences a-b from H.
* `extractionLoss delta = (2*((2^65/delta^41)^13+1))^196`.
* `rankBound delta = 8*(256*extractionLoss(delta)/delta^5)^2`.
* `large_U3_local_bilinear`: produces H,xi,D,F, with H nonempty,
  (delta^5/256)*|G| <= extractionLoss(delta)*|H|,
  every selected derivative Fourier coefficient squared >=delta/2,
  |D|<=rankBound(delta), F(0)=0, the difference agreement above, and
  F(x+y)=F(x)+F(y) for x,y,x+y in bohr D (1/2).
For every x, F(x) is a global character in its evaluation argument.
No symmetry between the two arguments is asserted.

### 106. `Submission/LocalizedBilinearExtraction.lean`
Localizes H to a translate of bohr D (1/4), chooses a base point a0 there,
and translates the selected domain to a set T containing zero, with
T subset bohr D (1/2). The map F retains its local additivity and rank bound.
`large_U3_localized_bilinear` gives
  (delta^5/256)*|G| <= extractionLoss(delta)*17^(2*|D|)*|T|,
  |hat(derivative f (t+a0))(F(t)+chi0)|^2 >= delta/2 for all t in T.
The fixed shift a0 and fixed character chi0 are retained explicitly. They
have NOT been silently replaced by zero. The localization loss is exponential
in the polynomial rank, as expected at this stage of a classical inverse proof.

All files 101–106 compile, their oleans were built, and all printed axiom
lists contain only propext, Classical.choice, Quot.sound.

### Current mathematical gap after file 106
The graph extraction -> arbitrary fixed-order Freiman restriction -> consistent
local additive extension -> Bohr-domain localization chain is now proved.
The next missing U3 step is a valid symmetry/approximate-symmetry argument and
local quadratic integration with correlation estimates. Local additivity of
F by itself does not establish symmetry of F(x)(y) and F(y)(x). Nor may one
substitute a global quadratic phase for the local structures without proof.
The actual all-length conjecture still additionally requires higher-Gowers-
order structure and sufficiently efficient relative density increments to
obtain reciprocal summability. A classical U3 inverse theorem, even if
completed, would not alone close that all-length quantitative gap.

`Submission/Spec.lean` remains unchanged with its original sorry. There is no
complete proof or disproof, and no proof submission was made in this continuation.

## Phase-preserving energy and conditional integration (files 107–109)

### 107. `Submission/TwistedCorrelationEnergy.lean`
Defines mixedCoefficient(u,v,F,h)=E_x u(x+h)*conj(v(x))*conj(F(h)(x)),
and the complex twisted energy
  E_{h,k,t} b(h)*conj(b(k))*conj(b(h-t))*b(k-t)*F(h-k)(t).
* `kernel_gram_eq_twistedEnergy` retains this twisting phase exactly, assuming
  b is supported on T and F(h-k)=F(h)-F(k) for h,k in T.
* `twistedEnergy_eq_derivative_fourier` is an exact identity, valid for any F:
    twistedEnergy(b,F) = E_a |hat(derivative b a)(-F(a))|^2
  (the right side is coerced from Real to Complex).
* `mixed_correlation_fourth_le` gives
    |E_h b(h)*mixedCoefficient(u,v,F,h)|^4
      <= E_a |hat(derivative b a)(-F(a))|^2
  for one-bounded u,v and the support/compatibility hypotheses above.
No absolute value of the twisting phase is discarded in this step. The
opposite frequency -F(a) is essential; it is not replaced by F(a).

### 108. `Submission/LocalPhaseDuality.lean`
* `large_U3_compatible_bilinear` strengthens file 106 by additionally retaining
    F(h-k)=F(h)-F(k) for every h,k in T.
  This is deduced from the global difference agreement on the original
  extracted H; it does NOT assume T-T lies in the radius-1/2 Bohr domain.
* `shifted_mixed_coefficient` explicitly incorporates the fixed shift and
  character offset:
    u(x)=f(x+a0), v(x)=f(x)*chi0(x)
  gives mixedCoefficient(u,v,F,t)=hat(derivative f (t+a0))(F(t)+chi0).
* `aligned_phase_duality`: if these mixed coefficients have squared norm
  >=kappa>=0 on T, there is a one-bounded b supported on T with
    (kappa*|T|/|G|)^4 <= E_a |hat(derivative b a)(-F(a))|^2.
  Phases are aligned explicitly using `exists_phase_alignment`; the required
  norm and support assertions are all proved.
This is a phase-preserving duality estimate, NOT a proof that F is symmetric.

### 109. `Submission/LocalQuadraticIntegration.lean`
Defines local additivity on a set P with all domain conditions explicit.
An additive halving map is constructed whenever doubling on G is bijective.
For any additive map half and locally additive F, define
  q(x)=F(x)(half(x)),
  cross(h,x)=F(h)(half(x))*F(x)(half(h)).
The cross pairing is symmetric by construction; no symmetry of F is assumed.
* `quadraticPhase_add` and `quadraticPhase_derivative`:
    derivative q h x = q(h)*cross(h,x)
  when x,h,x+h lie in P.
* `quadraticPhase_second_derivative`: the second derivative is cross(h,k),
  with each required point explicitly assumed in P.
* `quadraticPhase_third_derivative`: the third derivative is one on the
  specified eight-vertex local cube, again with all domain hypotheses.
* `quadraticPhase_derivative_approx`: suppose half(u+u)=u, F is locally
  additive, u,v,2u,2v,2u+2v lie in P, and |F(u)(v)-F(v)(u)|<=epsilon. Then
    |derivative q (2v) (2u)-q(2v)*F(2v)(2u)| <= 2*epsilon.
  Working on doubled points avoids an invalid square-root branch inference.
  This is a CONDITIONAL integration estimate. The needed approximate symmetry
  hypothesis is not established for the extracted map from large U3.

All files 107–109 compile, oleans built, and printed axiom lists contain
only propext, Classical.choice, Quot.sound.

### Updated remaining gap
The phase-retaining Cauchy–Schwarz identity and the algebraic/conditional
local integration step are now proved. The analytic step that would force
sufficient approximate symmetry on a quantitatively useful restricted domain
is still missing. An estimate on a phase's square cannot justify choosing a
near-one square root without further work; file 109 deliberately uses doubled
points instead. One must also localize the base variable of the mixed
correlation to the integration domain and retain both fixed offsets.
Even completing that U3 inverse chain would not by itself prove the required
all-length reciprocal summability: higher-uniformity structure and adequately
efficient relative density increments remain independent missing work.
`Submission/Spec.lean` remains unchanged with its original sorry. No complete
proof/disproof or proof submission has been made in this continuation.

### 110. `Submission/AntidiagonalTwistedEnergy.lean`
Defines the antisymmetric phase A(x,y)=F(x)(y)*conj(F(y)(x)), the fiber
weight w_s(x)=b(x)*b(s-x)*F(x)(x-s), and the skew form
Q(w)=E_x E_u w(x)*conj(w(u))*A(x,u).
* `skewPhase_sub_right`: A(x,u)*conj(A(x,v))=A(x,u-v), provided
  u,v belong to T and F(u-v)=F(u)-F(v).
* The fiber weights inherit support in T and the one-boundedness of b.
* `twistedEnergy_eq_skew_forms`: twistedEnergy(b,F)=E_s Q(w_s).
  This exact antidiagonal reindexing uses t=x+u-s and only difference
  compatibility on T, not global additivity of F or additivity on T+T.
The file compiles, its olean was built, and its axiom list is permitted.

Next concrete goal: with sigma=|T|/|G| and
  bias_T(d)=E_x 1_T(x)*A(x,d),
prove |twistedEnergy(b,F)|^2 <= sigma *
  E_u E_v 1_T(u)*1_T(v)*|bias_T(u-v)|.
Cauchy--Schwarz for Q(w) and expansion of the masked squared row norm
should give the bound for each fiber; Jensen then averages over s.
Keeping the mask on T is essential: F outside its local domain is arbitrary.
This remains partial higher-order work, not a settlement of Spec.lean.

### 111. `Submission/AveragedAntisymmetry.lean`
Defines the masked complex bias
  localSkewBias(T,F,d)=E_x 1_T(x)*skewPhase(F,x,d)
and averageSkewBias(T,F)=E_u E_v 1_T(u)1_T(v)*|localSkewBias(T,F,u-v)|.
* Proves general complex-expectation Cauchy--Schwarz and a support-mass bound.
* `masked_row_energy`: the squared L2 norm of the masked skew-kernel row
  is exactly the real part of the weighted bias average; no absolute values
  are taken before this identity.
* `skewForm_sq_le_average_bias`: |Q(w)|^2<=sigma*averageSkewBias.
* `twistedEnergy_sq_le_average_bias`: |twistedEnergy(b,F)|^2 has the same
  bound, by Jensen over the antidiagonal fibers.
* `mixed_correlation_eighth_le`: |E b*mixedCoefficient|^8<=sigma*averageSkewBias.
* `large_coefficients_average_bias_lower`: coefficients squared>=kappa on
  nonempty T imply kappa^8*sigma^7<=averageSkewBias(T,F).
* `large_U3_average_antisymmetry` combines this with the existing extraction:
  all rank/cardinality/domain properties and both offsets are retained, and
  the extracted map satisfies (delta/2)^8*sigma^7<=averageSkewBias(T,F).
The file compiles, its olean is built, and all printed axioms are permitted.
This is averaged antisymmetry bias, NOT pointwise approximate symmetry.

Potential next route: graph(T,F) has small sumset by difference compatibility.
Croot--Sisask sampling in G x dual(G), using graph(T,F) as the sampling domain,
can potentially provide large sets of almost periods independent of ambient
|G x dual(G)|. Large Fourier coefficients of the graph are precisely the
biased skew phases evaluated as characters on G x dual(G). L1 almost periods
of graph self-convolution would therefore approximately annihilate all such
characters simultaneously. This route is not yet formalized.

### 112. `Submission/SmallDoublingAnnihilation.lean`
Proves a new ambient-density-free spectral annihilation lemma using the existing
L2 Croot--Sisask theorem. For nonempty A and positive integer n, produces X⊆A,
X nonempty, with |A|^(n+1)<=2|A+A|^n|X| and, for all s,t in X and characters chi,
  n*|A|*|chi(s-t)-1|^2*|E_A chi|^4 <= 16|A-A|.
The key is that smooth(A,1_A) is supported on A-A. Two shifted supports have
size <=2|A-A|, so Cauchy--Schwarz converts the L2 sampling error into a Fourier
error with a small-doubling cost instead of an ambient-group-size cost.

### 113. `Submission/GraphSkewAnnihilation.lean`
Defines an actual character on G x dual(G):
  graphSkewCharacter(F,d)(x,chi)=chi(d)*conj(F(d)(x)).
On the graph (x,F(x)), this is exactly skewPhase(F,x,d).
Difference compatibility on T makes BOTH graph sumset and graph difference
set project injectively to G, so each has cardinality <=|G|.
`exists_skew_almost_annihilators` applies file 112 to the graph and gives X⊆T,
nonempty, |T|^(n+1)<=2|G|^n|X|, with
  n*|T|*|skewPhase(F,s-t,d)-1|^2*|E_{x∈T} skewPhase(F,x,d)|^4 <=16|G|
for all s,t in X and arbitrary d. A parameterized version controls every
normalized-bias>=eta phase by epsilon when n|T|eta^4 epsilon^2>=16|G|.

### 114. `Submission/BiasedSkewDifferences.lean`
Defines normalizedSkewBias and its average over differences of T.
Proves averageSkewBias=sigma^3*pairSkewBias. A bounded difference average >=Lambda
produces D⊆T-T with |D|>=Lambda|T|/2 and every d in D having bias>=Lambda/2.
For large mixed coefficients one can use Lambda=kappa^8*sigma^4.
`exists_cross_skew_control` combines this with graph sampling: a quantitatively
large X⊆T and D⊆T-T satisfy |skewPhase(F,s-t,d)-1|<=epsilon for all s,t∈X,d∈D.
All files 112–114 compile, oleans built, axiom lists permitted.

Next route (derived, not yet formalized): localize the original T more deeply,
to bohr(B,1/16). Then D⊆T-T lies in bohr(B,1/8), and 2D-2D lies in the local
additivity domain bohr(B,1/2). The cross control extends by local additivity to
  |skewPhase(F,z,w)-1|<=8*epsilon
for z∈2X-2X and w∈2D-2D. Bogolyubov on X and D, then intersection, gives a common
Bohr domain with uniform approximate symmetry. NO second sampling step is needed:
extension in the second argument uses the already valid local additivity of F.
This appears to close the analytic symmetry gap once domain extension and
parameterized deeper localization are formalized. Local correlation/integration
and the all-length quantitative problems still remain afterward.

### 115. `Submission/LocalSkewSymmetry.lean`
Proves local sub/add identities for the skew phase with every domain membership
explicit. Cross control |skew(s-t,d)-1|<=epsilon on X,X,D extends to
  |skew(z,w)-1|<=8epsilon for z∈2X-2X, w∈2D-2D.
`cross_control_bohr_symmetry` assumes T⊆bohr(B,1/16), X⊆T, D⊆T-T and local
additivity on bohr(B,1/2). Bogolyubov on X and D gives E of rank
  <=8/density(X)^2+8/density(D)^2,
with bohr(E,1/2)⊆bohr(B,1/4) and |F(x)(y)-F(y)(x)|<=8epsilon throughout
bohr(E,1/2)^2. The 1/16 localization verifies all fourfold domain conditions.

### 116. `Submission/QuantitativeSkewSymmetry.lean`
Defines
  symmetrySamples(sigma,Lambda,epsilon)
    =ceil(16/(sigma*(Lambda/2)^4*(epsilon/8)^2))+1,
  symmetryRank(sigma,Lambda,epsilon)
    =32/sigma^(2*(symmetrySamples+1))+32/(Lambda*sigma)^2.
`exists_quantitative_bohr_symmetry` proves rank<=symmetryRank and error<=epsilon
on a common radius-1/2 Bohr domain from pairSkewBias>=Lambda>0. The quantitative
rank depends on sigma and Lambda, not on ambient group size. Sampling gives
  density(X)>=sigma^(n+1)/2, density(D)>=Lambda*sigma/2.

### 117. `Submission/U3ApproximateSymmetry.lean`
* `large_U3_deep_bilinear` repeats the valid translate localization using
  radius 1/32 (grid parameter 64), producing T⊆bohr(B,1/16) with
  delta^5|G|/256<=extractionLoss(delta)*129^(2|B|)*|T|.
  Both offsets, difference compatibility, local additivity, and the previous
  polynomial bound on |B| are retained.
* `large_U3_approximate_symmetry` now unconditionally applies files 111–116:
  for every epsilon>0, the extracted F has a common Bohr domain E with
  |E|<=symmetryRank(sigma,(delta/2)^8*sigma^4,epsilon) and
  |F(x)(y)-F(y)(x)|<=epsilon for every x,y∈bohr(E,1/2).
* `integrated_derivative_on_refined_bohr`: if half is an additive halving map,
  on u,v∈bohr(B union E,1/8), the phase q(x)=F(x)(half(x)) satisfies
    |derivative q (2v) (2u)-q(2v)*F(2v)(2u)|<=2epsilon.
  Domain memberships of u,v,2u,2v,2u+2v in the original local-additivity domain
  are all proved. This avoids invalid square-root branching.
All files 115–117 compile, oleans built, axiom lists permitted.

### Milestone after file 117
The previously missing analytic APPROXIMATE SYMMETRY step is now proved with
quantitative bounds, and it feeds the conditional quadratic integration lemma.
What is still NOT proved: correlation of f with the integrated local quadratic
phase. Need to localize derivative directions into doubles of the refined Bohr
set and the base variable into a translate of a comparable small doubled Bohr
set, then detwist and use a mixed-correlation Fourier estimate. The offsets
must still be retained. Beyond U3, higher orders and sufficiently efficient
all-length density increments remain missing. Spec.lean still has its original
sorry, and no settlement/submission has been made.

### 118. `Submission/MixedCorrelationFourier.lean`
Proves the exact Fourier formula for mixedCorr(a,b)(h)=E_x a(x+h)conj(b(x)),
and the energy identity sum_chi |hat(a)|^2 |hat(b)|^2.
`localized_mixed_inverse`: if normalized correlations over Q have averaged
squared norm >=kappa on H, and b is one-bounded, a has a Fourier coefficient
of squared norm >=kappa*density(H)*density(Q).

### 119. `Submission/LocalizedQuadraticCorrelation.lean`
* `exists_localized_mixed_mean` localizes the base variable to a translate z+Q
  while preserving the averaged squared mixed coefficient. The center phase
  conj(F(h)(z)) is explicitly retained in the mean identity.
* `localized_detwist_error` removes a unit-norm phase q assuming its derivative
  approximates q(h)F(h)(x) on h∈H,x∈Q. No global integration assumption.
* `localized_phase_correlation`: if 4e^2<=kappa and the approximation error is
  <=e, obtains z and chi such that actual correlation of u(z+y) with q(y)chi(y)
  on any specified R containing Q+H has squared norm at least
    (kappa/4)*density(H)*density(Q).
  R can be a full doubled Bohr set, not just an arbitrary subset Q+H.

### 120. `Submission/DoubledBohrLocalization.lean`
Defines doubledBohr(C,r) as the image of bohr(C,r) under doubling, proves
halving/membership/cardinality/sum/difference lemmas when doubling is bijective.
`exists_doubled_bohr_restriction` recenters a subset of T to H containing zero,
H⊆doubledBohr(C,1/16), |T|<=129^(2|C|)|H|. The fixed center t0∈T and
h+t0∈T for every h∈H are retained. Also |G|<=65^(2|C|)|doubledBohr(C,1/16)|.
All files 118–120 compile, oleans built, axioms permitted.

Immediate next assembly: apply file 117 with epsilon=delta/16, put C=B union E,
localize directions via file 120, Q=doubledBohr(C,1/16), R=doubledBohr(C,1/8).
The earlier integration lemma gives error e=delta/8 on H x Q. Use kappa=delta/2,
so 4e^2<=kappa since delta<=1. File 119 should then yield actual local quadratic
correlation of squared norm >=delta*density(T)/(8*8385^(2|C|)). Both recentered
fixed offsets must be absorbed exactly into u and v before applying it.

### 121. `Submission/U3LocalQuadraticCorrelation.lean`
`large_U3_local_quadratic_correlation` now assembles the full local inverse
correlation step, for finite abelian groups with bijective doubling:
* Apply approximate symmetry with error delta/16.
* Refine to C=B union E, recenter directions into doubledBohr(C,1/16), and
  explicitly replace offsets by a0+t0 and F(t0)+chi0. Difference compatibility
  proves exact preservation of each large derivative Fourier coefficient.
* Use Q=doubledBohr(C,1/16), R=doubledBohr(C,1/8). The derivative error is delta/8.
  Since delta<=1, 4*(delta/8)^2<=delta/2.
* Base localization, detwisting, and the mixed Fourier inverse produce a shift
  a and character chi with ACTUAL squared local correlation
    |E_y 1_R(y) f(a+y) conj(q(y)) conj(chi(y))|^2
      >= delta*density(T)/(8*8385^(2*|C|)),
  where q(y)=F(y)(half(y)). The explicit size bound on T, rank bound on B,
  symmetryRank bound on E, and local additivity of F are retained.
This is no longer merely conditional integration or a graph extraction.
The theorem compiles, its olean is built, and axioms are permitted.

Still missing for the ORIGINAL target: higher uniformity orders and density
increments efficient enough for reciprocal summability for every fixed length.
This classical quantitative local U3 inverse theorem is not an all-length
solution. Spec.lean remains unchanged with its original sorry.

### 122. `Submission/LocalQuadraticInverse.lean`
Defines `IsLocallyQuadratic R q` using vanishing third derivative on EVERY
8-vertex cube lying in R, with no extra assumption on its directions.
Proves the integrated phase is locally quadratic on any R⊆bohr(B,1/4):
directions h,k lie in bohr(B,1/2) by subtracting cube vertices. Character
modulation preserves this property exactly.
`local_quadratic_inverse` packages file 121 with a unit-norm phase q that
is genuinely locally quadratic on the entire doubledBohr(B union E,1/8)
correlation domain. All rank/cardinality/correlation bounds are retained.
The file compiles, its olean is built, and its axiom list is permitted.
This completes the classical local U3 inverse chain at the level of actual
correlation and an explicit local-cube polynomial identity.

### 123. `Submission/UniformLocalQuadraticInverse.lean`
Eliminates the intermediate support density from the inverse parameters.
Defines explicit functions depending only on delta:
  baseRank(delta)=ceil(rankBound(delta));
  baseDensity(delta)=delta^5/(256*extractionLoss(delta)*129^(2*baseRank(delta)));
  inverseRank(delta)=baseRank(delta)+ceil(symmetryRank(baseDensity(delta),
    (delta/2)^8*baseDensity(delta)^4,delta/16));
  inverseCorrelation(delta)=delta*baseDensity(delta)/(8*8385^(2*inverseRank(delta))).
Proves positivity of inverseCorrelation for delta>0, antitonicity of the
sampling/rank functions, and the needed support-density lower bound.
`uniform_local_quadratic_inverse` gives a domain with rank<=inverseRank(delta)
and squared correlation>=inverseCorrelation(delta), uniformly in |G|.
Finally, doubling a Bohr set is itself a Bohr set after pulling its characters
back by halving. `bohr_local_quadratic_inverse` gives the conventional form:
  exists C,q,a, |C|<=inverseRank(delta), |q|=1,
  q is locally quadratic on bohr(C,1/8), and
  |E_y 1_bohr(C,1/8)(y) f(a+y) conj(q(y))|^2>=inverseCorrelation(delta).
The file compiles, its olean is built, and both final theorem axiom lists are
exactly [propext, Classical.choice, Quot.sound].

### Current status after file 123
A uniform quantitative classical U3 local inverse theorem is now fully proved,
including symmetry, base/direction localization, actual correlation, the local
cube identity, and ambient-size-independent parameters. This is substantial
but still NOT a proof of the original all-length conjecture.
The central unresolved target gaps are now:
1. Higher Gowers orders (U4 and beyond), not supplied by higher *Freiman* order.
2. Relative density increments efficient enough to imply reciprocal summability
   for each fixed AP length. Even the new U3 inverse has very poor classical
   rank/correlation costs and by itself does not prove the four-term analogue
   of the completed three-term reciprocal-summability theorem.
No divergent fixed-length AP-free counterexample is known from this work.
Spec.lean is unchanged with the original sorry. No completed proof/disproof
has been submitted. New development files 111–123 are all verified.

### 124. `Submission/UnlocalizedBilinearExtraction.lean`
Defines diffBall(T,n)=n*(T-T)=nT-nT, with monotonicity, addition, subtraction,
and recentering lemmas. Extracts Freiman order 12 and extends on 4H-4H before
recentering H to T. `large_U3_unlocalized_bilinear` retains zero in T,
  delta^5|G|/256 <= unlocalizedLoss(delta)*|T|,
where unlocalizedLoss(delta)=(2*(((2^65/delta^41)^25)+1))^388 is polynomial
in delta^-1. F is locally additive on diffBall(T,4), difference-compatible on
T, and all shifted derivative coefficients are large. No early Bohr thinning.

### 125. `Submission/UnlocalizedSkewSymmetry.lean`
Shows all sets needed in cross_control_fourfold lie in diffBall(T,4):
X-X⊆T-T, 2X-2X⊆2T-2T, D⊆T-T, D-D⊆2T-2T, 2D-2D⊆4T-4T.
The same sampling/Bogolyubov symmetry argument therefore works before any Bohr
localization. `large_U3_unlocalized_symmetry` retains polynomial density T and
gives one Bohr set E with local additivity and approximate symmetry on it.

### 126. `Submission/CompatibleQuadraticCorrelation.lean`
Extracts the correlation assembly into a reusable theorem: any compatible
correlated map with local additivity and error<=kappa/8 symmetry on bohr(E,1/2)
yields actual unit-norm local quadratic correlation on doubledBohr(E,1/8),
with squared correlation >=kappa*density(T)/(4*8385^(2|E|)). The original T need
not lie in a Bohr set. Both offsets are preserved through recentering.

### 127. `Submission/ReducedLossQuadraticInverse.lean`
Uniform inverse parameters now use retainedDensity(delta)=delta^5/(256*unlocalizedLoss(delta))
in place of the exponentially small earlier baseDensity. Defines reducedRank
and reducedCorrelation by the same symmetry/correlation formulas, proves
positivity, and proves `reduced_loss_quadratic_inverse` on an ordinary Bohr set.
This removes one avoidable exponential loss from the previous inverse bound.
All files 124–127 compile, oleans are built, and axioms are permitted.

Potential further improvement (not yet proved): use the *same* graph L2 samples
both for biased-character annihilation and uniform almost-periodicity of graph
triple convolution. Its vertical Fourier projections are normalized cubic
self-convolutions of phase-weighted 1_T, with Fourier l1 norm <=1. Their common
almost-periods can feed one Chang spectrum, giving polynomial-rank simultaneous
Bohr periods. At a center with scalar triple-convolution >=density(T), these
periods force skew(t,d) near 1 for all biased d. Intersecting with Bogolyubov(D)
would yield polynomial-rank symmetry, avoiding Bogolyubov on the exponentially
small sample set X. All these projection/period arguments still need proof.

### 128. `Submission/PhaseCubicSmoothing.lean`
Defines normalized cubic self-convolution of a phase-weighted indicator.
Proves its Fourier coefficient is sigma^-2*hat(w)*|hat(w)|^2, hence Fourier
l1 norm <=1 for a one-bounded phase supported on T. This bound is independent
of sigma and of the ambient group size. Also proves the exact local double-
average formula for cubicSmooth(T,theta).

### 129. `Submission/GraphTripleProjection.lean`
Defines triple(T,x)=E_{a,b∈T}1_T(x+a-b). Under 0∈T and local additivity of F on
4T-4T, proves exact factorization
  cubicSmooth(T,skew(-,d),x)=skew(x,d)*triple(T,x).
Proves graph triple convolution at (x,psi) equals triple(T,x) if psi=F(x),
and zero otherwise: at most one nonzero vertical coordinate per row.
Proves exact shifted graph/scalar identities even outside the local domain,
where the scalar triple convolution vanishes. No dual-cardinality factor is lost.

### 130. `Submission/JointGraphAlmostPeriods.lean`
One L2 Croot--Sisask sample set simultaneously supplies spectral annihilation
and uniform almost-periodicity of triple convolution (via one further smoothing).
`exists_skew_cubic_almost_periods` transfers this to the graph projection:
for 8<=n*epsilon^2 and 16|G|<=n|T|eta^4 epsilon^2, produces X⊆T nonempty,
  |T|^(n+1)<=2|G|^n|X|,
with scalar triple periods of error epsilon and, simultaneously for every d
with normalized skew bias>=eta, cubicSmooth skew-phase periods of error 2epsilon.
The same sample set is used for both properties, not an unjustified intersection.
All files 128–130 compile, oleans built, axioms permitted.

Next: apply a SINGLE Chang spectrum to these common periods. Its rank is
O(log(1/density(X))) and its Bohr-period error is 2*ell*e+eta+2*2^(-2ell),
using the Fourier-l1 bound 1. Find a center where triple(T)>=density(T), then
use positivity of the translated scalar triple and local additivity to deduce
uniform skew(t,d)≈1 on this Bohr set for all biased d. Intersect with Bogolyubov(D).
This should avoid Bogolyubov(X) and its exponential rank loss, but this last
common-Bohr/center/symmetry assembly is not yet formalized.

### 131. `Submission/CommonCubicBohrPeriods.lean`
`exists_common_bohr_generators` extracts one Chang spectrum from X; it works
for every function having the stated Fourier-l1 and common-period bounds.
`exists_common_cubic_bohr_periods` applies it simultaneously to scalar triple
and all biased phase-cubic functions, with common error
  periodError(ell,epsilon,tau)=4*ell*epsilon+tau+2*(1/2)^(2ell),
rank <=floor(16 log(1/density(X))), and radius tau/(rank+1).
There is no factor counting the number of phases.

### 132. `Submission/TripleCenterSymmetry.lean`
Proves E_{a∈T}triple(T,a)>=density(T) by the exact squared-smoothing identity
and Jensen. Therefore T contains a center with triple value >=density(T).
`common_periods_force_skew`: if the common period error rho is <density(T),
all those periods lie in 4T-4T (by positivity at the large center), and
  density(T)*|skew(t,d)-1|<=2rho
for every biased d. This uses local additivity only after domain membership
has been proved; it does not assume a global extension of F.

### 133. `Submission/SpectralSkewSymmetry.lean`
Combines the common spectral periods with Bogolyubov ONLY on the large biased
difference set D. Defines sampleRank(sigma,n)=floor(16(log2+(n+1)log(1/sigma)))
and spectralSymmetryRank(sigma,Lambda,n)=sampleRank+ceil(32/(Lambda*sigma)^2).
`exists_spectral_bohr_symmetry` gives C of at most that rank, radius
  min(tau/(|C|+1),1/2),
local additivity on the Bohr set, and symmetry error <=8*periodError/sigma.
This removes the exponential rank loss from applying Bogolyubov to the sparse
sample set X. All files 131–133 compile, oleans built, axioms permitted.
Next: choose explicit polynomial sample/error parameters, normalize the small
Bohr radius by adding finitely many powers of its characters, and feed the
result into CompatibleQuadraticCorrelation. This will give a substantially
sharper polynomial-rank U3 inverse, but still not the target's higher-order and
reciprocal-summability density increments.

### 134. `Submission/BohrPowerNormalization.lean`
Defines powerFamily(C,m) from powers j<=m of the characters in C. Its rank is
at most (m+1)|C|. The geometric-sum argument proves that |z^j-1|<=1/2 for all
j<=m implies |z-1|<=1/m. Therefore any positive-radius Bohr set contains a
fixed-radius (1/2) Bohr set with rank cost (ceil(1/r)+2)|C|.

### 135. `Submission/PolynomialRankSkewSymmetry.lean`
Chooses explicit algebraic sampling/walk parameters in alpha,Lambda,omega,
with tolerance alpha*omega/64 and period error at most three times tolerance.
Combines spectral symmetry with radius normalization to obtain E of rank
<=fixedRadiusRank(alpha,Lambda,omega), locally additive on bohr(E,1/2),
with symmetry error <=omega. This rank formula contains algebraic functions,
logarithms and roundings, but no exponential in inverse parameters.
Files 134--135 compile, oleans built, axioms permitted.
Next: combine this with unlocalized bilinear extraction and the existing
compatible correlation theorem to obtain the sharper uniform U3 inverse.
This does NOT yet supply higher-order inverses or summable density increments.

### 136. `Submission/PolynomialRankQuadraticInverse.lean`
Assembles unlocalized twelve-Freiman extraction, the common spectral symmetry
lemma, and compatible quadratic correlation. Defines sharpRank(delta) using
fixedRadiusRank at alpha=retainedDensity(delta), Lambda=(delta/2)^8 alpha^4,
omega=delta/16. Defines positive sharpCorrelation(delta)=delta*alpha/
(8*8385^(2*sharpRank(delta))). The main theorem gives a unit-norm phase locally
quadratic on an ordinary radius-1/8 Bohr set, actual squared masked correlation
>=sharpCorrelation(delta), and rank<=sharpRank(delta). The rank formula has no
exponentials of inverse parameters. Compiles, olean built, permitted axioms.
This is a U3 inverse only, not the original conjecture or four-term summability.

### 137. `Submission/QuadraticRankPowerBound.lean`
Proves the explicit monomial estimate
 fixedRadiusRank(alpha,Lambda,omega) <= 30000000000000*t^21
whenever alpha<=1 and t>=1 dominates 1/alpha, 1/Lambda, and 1/tolerance.
Intermediate bounds: samplingCount<=200000*t^9, rawRank<=4000000*t^10,
and reciprocal rawRadius<=5000000*t^11. Compiles, olean built, permitted axioms.

### 138. `Submission/SingleExponentialQuadraticInverse.lean`
Proves retainedDensity(delta)^-1 <= extractionConstant*delta^-397705 for
0<delta<=1. Dominates all symmetry parameters by
parameterConstant*delta^-1590828. Consequently:
 sharpRank(delta) <= rankConstant*delta^-33407388,
 sharpCorrelation(delta) >= exp(-correlationConstant*delta^-33407388).
All three constants are explicitly defined positive real numbers independent
of delta and the group. `single_exponential_local_quadratic_inverse` packages
the local quadratic inverse with these conventional quantitative bounds.
Compiles, olean built, only permitted axioms. This remains a U3 inverse, NOT
a proof of arbitrary-length APs or four-term reciprocal summability.

### 139. `Submission/FourPatternQuadraticStructure.lean`
Combines pattern_free_uniformity_lower at n=2 with the completed local inverse.
For four distinct slopes over a finite field with bijective doubling, a
nonempty set A with only diagonal patterns and 4<=density(A)^3*|F| has a local
quadratic-correlation witness on a radius-1/8 Bohr set. The rank is bounded by
fourRankConstant*density(A)^-1069036416; squared masked correlation of the
balanced indicator is at least exp(-fourCorrelationConstant*density(A)^-1069036416).
Compiles, olean built, only permitted axioms.

Checkpoint after 139: Spec.lean is UNCHANGED and still has its original sorry.
No completed proof or disproof has been submitted. The definitions were
rechecked: IsAPOfLengthWith includes ENat.card s = length, so constant or
repeated progressions do not satisfy the target at arbitrary lengths.
The missing steps remain (1) higher Gowers orders, and (2) efficient enough
density increments to obtain fixed-length reciprocal summability. The new
four-pattern result supplies structure, not such an increment.

### 140. `Submission/FinitePartitionIncrement.lean`
A centered signed distribution with large L1 mass has a cell with both controlled
mass and positive relative increment. Applies this to a bounded complex test
approximated on a finite partition: squared correlation>=r and approximation
error<=r/2 imply a cell of mass>=r/(16*numberOfCells) and centered mean>=r/16.
Centering is used explicitly; a negative correlation alone cannot yield a positive
increment. Compiles, olean built, permitted axioms.

### 141. `Submission/MaskedPhaseIncrement.lean`
Explicit real/imaginary phase-grid labels with mesh n, masked outside a given B.
Equal labels have test oscillation<=2/n. For n=ceil(4/r), r<=1, the number of
cells is <=128/r^2. Thus squared masked correlation>=r yields a cell of mass
>=r^3/2048 and positive centered mean>=r/16. The definition IsMaskedPhaseCell
records that the cell is a q-grid fiber inside B OR the whole complement of B;
it is not an arbitrary subset selected from f. Compiles, olean built, permitted
axioms. The complement alternative remains a genuine obstacle to iteration.
Next route: retain averages over translation centers throughout the inverse,
then use mean-zero across centers to select a positive phase cell INSIDE B.

### 142. `Submission/AveragedLocalizedQuadraticCorrelation.lean`
Retains the average over all base translations throughout localization and
Fourier extraction. Produces a character correction chi(z) at every center,
with average squared masked correlation >=(kappa/4)*density(H)*density(Q).
No favorable-center selection is made prematurely.

### 143. `Submission/AveragedCompatibleQuadraticCorrelation.lean`
Repeats the compatible local integration assembly with the averaged lemma.
Produces q(a,y), unit-norm and locally quadratic on the same doubled Bohr set
for every a, with averaged squared correlation >=kappa*density(T)/
(4*8385^(2|E|)). Handles both offsets by an explicit translation reindexing.

### 144. `Submission/AveragedPolynomialRankInverse.lean`
The complete sharper U3 inverse now retains averages over a: produces C and
q(a,y), rank<=sharpRank(delta), locally quadratic q(a,-) on bohr(C,1/8), and
average squared masked correlation >=sharpCorrelation(delta). Same quantitative
parameters as file 136, but a stronger averaged conclusion.

### 145. `Submission/AveragedMaskedPhaseIncrement.lean`
Eliminates the complement-cell alternative. Inside-phase charges sum to the
masked mean, whose average over all translations is zero. Averaged squared
correlation>=r implies a center with large (L1 mass + signed mean) on the
INTERIOR cells. Proves a positive interior cell of mass>=r/(16*(2n+1)^2)
and centered mean>=r/16 whenever 2/n<=r/2. This is not a signed deficit.

### 146. `Submission/InteriorQuadraticDensityIncrement.lean`
Assembles the averaged inverse with the positive interior-cell selection.
`interior_quadratic_density_increment`: a centered indicator with U3-power>=delta
has an interior quadratic phase cell S (mesh ceil(4/r)), rank<=sharpRank(delta),
|S|>=r^3*|G|/2048, and density of A on a+S >=density(A)+r/16, for every
0<r<=sharpCorrelation(delta). The phase is locally quadratic on the entire
Bohr domain containing S, not just on S.
`four_pattern_free_interior_density_increment` applies this to four distinct
slopes and uses the explicit r=exp(-fourCorrelationConstant*density(A)^-1069036416).
All files 142--146 compile, oleans built, permitted axioms only.

Important limitation after 146: this is now a GENUINE POSITIVE GLOBAL DENSITY
INCREMENT ON AN INTERIOR QUADRATIC PHASE CELL. It is not an iteratable relative
increment. A phase cell is not an ambient finite group or an AP, so the global
inverse/counting theorem cannot simply be reapplied to A restricted to it.
Higher Gowers orders remain missing, and the quantitative losses are still
far from the reciprocal-summability requirement. Spec.lean remains unchanged
with its original sorry; no settlement has been submitted.

Technical note: InteriorQuadraticDensityIncrement deliberately omits an explicit
[DecidableEq G]. Its masks must match the classical instances in the generic
partition lemmas. Including that instance caused millions of failed definitional
reductions of bohr/filter/membership. Also, when rewriting the selected subtype
mean, first assign `have hinc' : r/16 <= E x:S, f(a+x) := hinc`, then unfold f;
a direct `change` on the original selected-subtype expression failed.

### 147. `Submission/DualLocalizedQuadraticCorrelation.lean`
New loss-saving Fourier step: extracting a coefficient of the SECOND,
Bohr-supported function yields normalized squared local correlation
>=kappa*density(H), with NO density(Q) factor. The averaged local integration
version gives average_z normalized correlation on Q >=(kappa/4)*density(H).
The direction set H need not lie in Q. Requires approximate integration on HxQ
and local additivity on a domain containing H+Q. Compiles, olean built, permitted
axioms only.

### 148. `Submission/SmallBaseQuadraticIntegration.lean`
Proves approximate integration with base 2u small and direction h arbitrary:
 |D_h quadraticPhase(2u)-quadraticPhase(h)*F(h)(2u)| <= epsilon
assuming symmetry error |F(u)(h)-F(h)(u)|<=epsilon and local additivity on
u,2u,h,2u+h. Only u is halved/doubled; NO membership assumption on half(h) is
needed. The identity F(2u)(half h)=F(u)(h) avoids the square-root branch issue.
Compiles, olean built, permitted axioms.

Promising next assembly (NOT YET PROVED): common spectral periods already give
cross symmetry between a small Bohr set and EVERY biased difference d, not just
between two small points. From pairSkewBias>=Lambda, select a center t0 in T
with a polynomial-density fiber H={t-t0 : t in T and normalizedSkewBias(t-t0)>=Lambda/2}.
Preserve its coefficient correlations with the usual fixed offsets. Intersect
the common spectral Bohr domain with Bogolyubov(T), so Q lies in 2T-2T and
H+Q lies in 3T-3T, all inside the existing fourfold local-additivity domain.
Then file 148 gives integration on H x doubled-small-Bohr Q, and file 147
extracts average NORMALIZED local quadratic correlation >=kappa*density(H)/4,
which is polynomial in delta. This would remove the exponential correlation
loss caused by thinning directions into a Bohr set. The rank would remain
polynomial in inverse delta. Even that stronger inverse would still leave
relative iteration, higher Gowers orders, and summability-quality costs open.

### 149. `Submission/BiasedDifferenceFiber.lean`
`exists_biased_difference_fiber` proves the missing common-endpoint selection:
from Lambda<=E_{u,v in T} b(u-v) and b<=1, obtains t0 in T and nonempty H⊆T-T,
 Lambda*|T|<=2|H|,
 h+t0 in T and b(h)>=Lambda/2 for every h in H.
This preserves the original shifted derivative coefficients on every direction
of H after recentering. Compiles, olean built, permitted axioms.

More precise next assembly plan (still NOT yet implemented):
1. Prove cross version of file 135: fixed-radius E with rank<=fixedRadiusRank
   (alpha,Lambda,omega), bohr(E,1/2)⊆diffBall(T,2), and symmetry between every
   x in this Bohr set and EVERY d with normalizedSkewBias(d)>=Lambda/2.
   Use common_cubic_bohr_periods and common_periods_force_skew directly;
   intersect with Bogolyubov(T), not Bogolyubov(D). For Lambda<=1 its rank
   8/density(T)^2 is covered by the existing rawRank second term
   ceil(32/(Lambda*alpha)^2). The current sample/tolerance constants suffice.
2. Apply file149 to normalizedSkewBias, giving H,t0 with density(H)>=Lambda*alpha/2.
   On Q=doubledBohr(E,1/16), Q⊆bohr(E,1/8)⊆diffBall(T,2), while H⊆diffBall(T,1),
   hence Q+H⊆diffBall(T,3), inside the existing diffBall(T,4) extension domain.
   File148 provides approximate integration with error omega on HxQ; no
   direction thinning and no hypothesis on half(h) is needed.
3. File147 then gives averaged normalized correlation with the SECOND function
   v(x)=f(x)*(F(t0)+chi0)(x), on Q. Absorb the fixed character into the output
   phase. The first-function shift a0+t0 causes no center reindexing because
   the second function is the one extracted.
4. Set alpha=retainedDensity(delta), Lambda=(delta/2)^8*alpha^4,
   kappa=delta/2, omega=kappa/4=delta/8. Expected normalized squared correlation
   >=kappa*Lambda*alpha/8 = delta^9*alpha^5/4096, polynomial in delta, with
   rank fixedRadiusRank(alpha,Lambda,delta/8). Need actually prove this assembly.
5. For positive relative increments, use the finite partition argument on
   V=Q (normalized counting measure), with translation-center parameter G.
   The joint mean E_a E_{y in Q} (1_A(a+y)-density A) is zero. This should give
   a phase cell of relative size >=r^3/2048 and density increase>=r/16, both
   polynomial in delta. This would remove the ambient-Bohr-density loss in146.
   It STILL does not supply an iteratable relative inverse, higher orders,
   or reciprocal-summability-quality quantitative bounds.

### 150. `Submission/CrossSpectralSymmetry.lean`
Proves the fixed-radius cross-symmetry theorem described after149: same
fixedRadiusRank budget, bohr(E,1/2) contained in diffBall(T,2), and symmetry
error<=omega against EVERY biased difference d. Bogolyubov is applied to T,
not to the biased-difference set, and no restriction of the direction to the
Bohr domain is imposed. Compiles, olean built, permitted axioms.

### 151. `Submission/NormalizedCompatibleQuadraticCorrelation.lean`
Combines the biased common-endpoint fiber, small-base integration, and the
second-function Fourier extraction. Produces phases q(a,-), locally quadratic
on doubledBohr(E,1/16), with averaged NORMALIZED squared correlation
>=kappa*Lambda*density(T)/8. No exponential loss from restricting H to a Bohr
set; H+Q stays in diffBall(T,3). Both character offsets are handled explicitly.
Compiles, olean built, permitted axioms.

### 152. `Submission/NormalizedQuadraticInverse.lean`
The sharper normalized U3 inverse is now assembled UNCONDITIONALLY. Defines
 normalizedRank(delta)=fixedRadiusRank(alpha,(delta/2)^8*alpha^4,delta/8),
 normalizedCorrelation(delta)=delta^9*alpha^5/4096,
with alpha=retainedDensity(delta). Produces an ordinary radius-1/16 Bohr set
and locally quadratic q(a,-) for every translation center, with average
normalized squared correlation>=normalizedCorrelation(delta). Both rank and
inverse correlation are polynomial in inverse delta. Compiles, olean built,
only permitted axioms. This is still U3 only, not relative iteration or the
original reciprocal-summability conjecture.

### 153. `Submission/NormalizedQuadraticPowerBounds.lean`
Makes the normalized inverse costs explicit:
 normalizedRank(delta) <= rankConstant*delta^-33407388,
 normalizedCorrelation(delta) >= delta^1988534/correlationDenominator,
where correlationDenominator=4096*extractionConstant^5>0. Packages the averaged
normalized local inverse with BOTH polynomial bounds. Compiles, olean built,
permitted axioms only. Technical: reciprocal identities involving the huge
extractionConstant should be proved first for abstract real variables; broad
simp on the instantiated expression caused maximum-recursion-depth expansion.

### 154. `Submission/NormalizedPhaseIncrement.lean`
The finite phase-cell selection now works with separate center space Z and
local averaging space V. Only joint centering E_a E_x f(a,x)=0 is required.
Averaged normalized squared correlation>=r yields a cell in V of relative
size>=r^3/2048 and positive conditional mean>=r/16. This allows V to be the
subtype of a Bohr set, without giving that subtype a group structure.
Compiles, olean built, permitted axioms.

### 155. `Submission/NormalizedQuadraticDensityIncrement.lean`
Lifts phase cells from the Bohr-set subtype back to the ambient group, proving
exact cardinality and normalized-mean identities. The main global-to-local
increment has rank<=normalizedRank(delta), phase locally quadratic on the
whole bohr(C,1/16), and an INTERIOR phase cell S satisfying
 |S| >= r^3*|bohr(C,1/16)|/2048,
 density(A on a+S) >= density(A)+r/16,
for every 0<r<=normalizedCorrelation(delta). These are now POLYNOMIAL RELATIVE
size and gain, rather than quantities including the ambient Bohr density.
Compiles, olean built, permitted axioms only.

### 156. `Submission/FourPatternPolynomialIncrement.lean`
Combines the four-form counting lemma with the polynomial normalized increment.
Defines fourPolynomialGain(alpha)=alpha^63633088/fourPolynomialDenominator,
where fourPolynomialDenominator=correlationDenominator*8^15908272>0.
Four-pattern-free sets with 4<=alpha^3*|F| admit an interior phase cell with
density gain>=fourPolynomialGain(alpha)/16 and relative size>=gain^3/2048.
The Bohr rank is <=fourRankConstant*alpha^-1069036416. The local quadratic
phase, domain, explicit phase-cell shape, and positivity are all recorded.
Compiles, olean built, permitted axioms only.

Checkpoint after156: Spec.lean is STILL UNCHANGED with its original sorry.
No completed proof or disproof has been submitted. The normalized U3 inverse
and polynomial global-to-local quadratic density increment are now complete.
Missing: an iteratable relative increment inside existing quadratic phase
cells (such a cell is not an ambient group), higher Gowers orders, and costs
strong enough for reciprocal summability. Merely iterating polynomial-cost
classical increments does not automatically give the required summability.

Parsing note: put parentheses around subtraction in an expectation body:
`E x:S, (indicator A (a+x)-density A)`. Without parentheses, the notation can
parse the subtraction outside the expectation; that explained the earlier
failed `change` attempts, not just subtype-instance mismatches.

### 157. `Submission/LocalQuadraticProgressions.lean`
Exact local progression calculus. If a+n*d lies in the local quadraticity
domain for n<=N, then q(a+n*d)=q(a)*u^n*v^(choose(n,2)), with u=D_d q(a)
and v=D_d^2 q(a). Proves constant second derivatives, the first-derivative
formula, and oscillation <= n*|u-1|+choose(n,2)*|v-1|. All intermediate cube
vertices are verified to stay in the local domain. Compiles, olean built,
permitted axioms.

### 158. `Submission/QuadraticProgressionCurvature.lean`
Proves the binomial second-difference identity and exact curvature on every
subprogression: at stride d*h the second derivative is v^(d^2), independent
of the new base m. Three nearly equal phase values bound |v^(d^2)-1| by the
two distances to the middle value. Compiles, olean built, permitted axioms.

### 159. `Submission/QuantitativeMonochromaticThreeAP.lean`
Uses the previously verified quantitative integer three-AP-free bound to get
an explicit monochromatic three-term theorem for at most 2^l colors below
colorThreeBound(l)=2^thresholdExponent(l+2). The proof uses a largest finite
color fiber and the density bound, not an unbounded compactness argument.
Compiles, olean built, permitted axioms.

### 160. `Submission/SimultaneousQuadraticRecurrence.lean`
Defines recurrenceBound(m,t)=colorThreeBound((2t+8)m). For finite families of
unit phases w_i and v_j, proves existence of one positive d below this bound
with |w_i^d-1|<=2^-t and |v_j^(d^2)-1|<=2^-t simultaneously. Colors the sequences
w_i^n and v_j^choose(n,2) on one common phase grid, and uses the exact
three-point identity. Thus no square-root branch is inferred from a small
squared error. Compiles, olean built, permitted axioms.
This supplies uniform candidate strides but does not yet transfer the density
increment from a quadratic cell to a long arithmetic progression.

### 161. `Submission/LocalQuadraticFlattening.lean`
Chooses exact square roots of unit complex phases to express the local
quadratic progression formula as q(a)*w^n*z^(n^2). The simultaneous mixed
recurrence theorem then gives a bounded positive stride on which all local
quadratics oscillate by at most 2*L^2*2^-t for L steps. Every intermediate
point is assumed inside the local domain. No proximity of an arbitrary square
root to 1 is inferred. Compiles, olean built, permitted axioms only.

### 162. `Submission/BohrArithmeticProgressions.lean`
Elementary simultaneous linear Dirichlet approximation with explicit stride
bound (2n+1)^(2*card I), via finite phase grids. Produces progressions from
bohr(C,R) into bohr(C,R+2L/n), with uniformly bounded positive natural stride.
Natural stride positivity alone does not guarantee distinct group elements.
Compiles, olean built, permitted axioms only.

### 163. `Submission/BohrQuadraticFlattening.lean`
Combines linear Bohr approximation and local quadratic recurrence. Defines
flattenAccuracy, flattenMesh, and flattenStrideBound. Every inner Bohr point
has a progression of length L+1 in the enlarged Bohr set, on which all given
local quadratic phases oscillate by at most 2^-s. Stride is bounded uniformly
in the starting point. For ZMod p, the condition L*flattenStrideBound<p ensures
injectivity, so these are proper progressions. Compiles, olean built, permitted
axioms only. IMPORTANT: existence of a flat progression through each point does
not preserve density; no density-preserving transfer has yet been proved.

Checkpoint after163: Spec.lean remains unchanged with its original sorry.
No settlement has been submitted. Besides density-preserving transfer and
iteration, higher uniformity orders and summable extremal bounds remain open
in this development.

### 164. `Submission/VariableRadiusQuadraticCorrelation.lean`
Generalizes normalized_compatible_quadratic_correlation: after the character
set E is fixed, any 0<rho<=1/16 may be used for the normalized average on
doubledBohr(E,rho). The lower bound kappa*Lambda*density(T)/8 is unchanged.
The phase remains locally quadratic on the FULL doubledBohr(E,1/16), rather
than only on the smaller averaging domain. Compiles, olean built, permitted
axioms only.

### 165. `Submission/VariableRadiusQuadraticInverse.lean`
One character set C of rank <=normalizedRank(delta) works for EVERY positive
averaging radius rho<=1/16. Phases may depend on rho; they are locally quadratic
on bohr(C,1/16), with averaged normalized squared correlation at least
normalizedCorrelation(delta). The stable-radius corollary chooses
1/64<=rho<=1/32 with RelativeStable C z rho for arbitrary positive integer z,
without changing rank or correlation costs. Compiles, olean built, permitted
axioms only.

### 166. `Submission/DensityPruning.lean`
Generic finite-set pruning lemma. If density(P on S)>=alpha+g, alpha>=0,
g>0, and T subset S loses at most (g/2)*|S| elements, then T is nonempty,
|T|>=|S|/2, and density(P on T)>=alpha+g/2. The proof derives g<=1 from
the original density assumption; no independent bound on g is required.
Compiles, olean built, permitted axioms only. DecidablePred P is explicit:
otherwise specialization to finite-set membership led to filter-instance
mismatches in downstream applications.

### 167. `Submission/StableQuadraticDensityIncrement.lean`
Proves the stable Bohr inner-boundary estimate
 |bohr(C,rho) \ bohr(C,rho-relativeWidth)| <= |bohr(C,rho)|/z.
Combines the stable-radius inverse, phase-cell selection, and pruning. For
z>0 and 65536/r^4<=z, obtains an INNER phase cell S with
 |S| >= r^3/4096*|bohr(C,rho)|,
 density(A on a+S) >= density(A)+r/32.
The outer radius rho is in [1/64,1/32] and is RelativeStable C z rho.
S lies in bohr(C,rho-relativeWidth); q remains locally quadratic throughout
bohr(C,1/16). Thus a positive-width BOHR buffer is now available. Compiles,
olean built, permitted axioms only.
IMPORTANT: there is still NO phase-grid boundary buffer, no density-preserving
progression transfer, and no iteratable higher-order theorem.

Checkpoint after167: original Spec.lean is unchanged, with its original sorry.
No proof or disproof of the target has been completed or submitted. The new
results address only radius selection and Bohr-boundary loss in the U3 step.
Higher Gowers orders and quantitative bounds strong enough for reciprocal
summability remain independent unresolved requirements in this development.

### 168. `Submission/AveragedPartialPartitionIncrement.lean`
Averaged correlation selects a positive GOOD cell in an arbitrary center-dependent
partial partition c:Z->V->Option I. None is exceptional. Phase approximation
error epsilon and average exceptional mass tau cost epsilon+2*tau. If that is
at most r/2 and average squared correlation is at least r>0, obtains a nonempty
some-cell with mean>=r/16. Only joint centering E_a E_x f(a,x)=0 is needed.
This avoids any need to trim phase-grid boundaries. Compiles, olean built,
permitted axioms only.

### 169. `Submission/IntervalProgressionPartition.lean`
Explicit fixed-stride partition of Fin N: progressionLabel N d L uses complete
blocks of d*L points and groups residues into length-L arithmetic progressions.
For d,L>0, every nonempty some-cell has exactly L distinct natural indices,
with an exact fiber characterization. The none-cell has exactly N%(d*L)
points. Compiles, olean built, permitted axioms only.

### 170. `Submission/NearLinearProgressionPartition.lean`
Small-curvature quadratic phases are close to linear phases on a bounded
interval. Linear Dirichlet approximation gives one common stride d<=D,
D=(2n+1)^(2*card I), whose complete length-L progression cells have error
<=2*M^2*eta+2L/n; fewer than D*L indices are exceptional. Valid simultaneously
for finitely many phases. Compiles, olean built, permitted axioms only.

### 171. `Submission/PartialPartitionRefinement.lean`
Defines refineLabel for a two-level partial partition. Inner exceptional
proportion <=tau relative to EVERY good outer cell adds at most tau to the
total exceptional mass. No estimate on the number of outer cells is needed.
Compiles, olean built, permitted axioms only.

### 172. `Submission/ProgressionFiberEquivalence.lean`
Explicit equivalence from Fin L to every complete fixed-stride progression
fiber. Conditional sums and exceptional charges transfer EXACTLY to local
progression coordinates. Compiles, olean built, permitted axioms only.

### 173. `Submission/QuadraticSequenceDilation.lean`
Proves the exact binomial dilation identity and the representation of a
quadratic phase on an arbitrary dilated progression. Curvature becomes
v^(d^2), while the linear coefficient depends on the new base.
Compiles, olean built, permitted axioms only.

### 174. `Submission/RefinedProgressionPartition.lean`
Two-level progression partition geometry and exceptional-mass bookkeeping.
The inner stride may depend on the outer fiber. Every nonempty refined good
cell is a proper length-L progression with product stride. If each inner
partition loses <=B local indices, the added exceptional proportion is <=B/M.
Compiles, olean built, permitted axioms only.

### 175. `Submission/QuadraticProgressionPartition.lean`
A genuine almost-complete flat AP partition for finitely many quadratic
sequences on Fin N. Square recurrence first makes the curvature small; each
complete outer fiber then uses its own linear Dirichlet stride. Outputs
 c:Fin N -> Option(Fin N x Fin M), unit representatives w, and
 exceptional mass <= recurrenceBound(card I,t)*M/N
                       +(2n+1)^(2*card I)*L/M;
 phase error <=2*M^2*2^-t+2L/n;
 every nonempty good cell is a proper length-L AP of stride at most
 recurrenceBound(card I,t)*(2n+1)^(2*card I).
This preserves averages through a partition, unlike the earlier pointwise
flat-progression existence theorem. Compiles, olean built, permitted axioms.

### 176. `Submission/LocalQuadraticProgressionPartition.lean`
Transfers file175 to local quadratic phases on a coarse progression whose
ENTIRE initial interval lies in their common local domain. Costs and phase
error are identical. Geometry is proper in natural indices; image properness
in the group additionally needs injectivity of the initial progression map.
Compiles, olean built, permitted axioms only.

Checkpoint after176: Spec.lean STILL has its original sorry; no settlement.
New route avoids phase-grid boundaries: combine flat AP partitions directly
with averaged_partial_partition_increment. Still needed: partition the Bohr
averaging domain into complete coarse progression fibers, with boundary loss
controlled by stable radius, then refine those fibers using file176. This
would give a genuine global U3-to-AP density increment. Even that will not
supply higher Gowers orders or summability-strength bounds for all AP lengths.

### 177. `Submission/RestrictedPartialPartition.lean`
Restricts an arbitrary partial partition to a subset B, retaining only entire
original fibers. Retained fibers are explicitly equivalent to their originals.
If every fiber meeting B' is wholly contained in B, then the restricted bad
cardinality is at most old bad cardinality plus |B\B'|. Compiles, olean built,
permitted axioms only.

### 178. `Submission/BohrCoarseProgressionPartition.lean`
Defines bohrIndices(C,R,a,h,N) as indices k in Fin N with a+k*h in bohr(C,R).
One common Dirichlet stride d<=(2n+1)^(2*rank) works for all coarse fibers and
all N. If 4M/n<=eta, every complete length-M fiber meeting the inner Bohr set
of radius R-eta lies wholly in the outer radius-R Bohr set. The restriction
to complete outer-Bohr fibers has bad cardinality at most
 (2n+1)^(2*rank)*M + |bohrIndices(R)\bohrIndices(R-eta)|.
Compiles, olean built, permitted axioms only. No injectivity of the image in G
is claimed without separately checking the original index map.

### 179. `Submission/RestrictedProgressionRefinement.lean`
Exact conditional exceptional-mass transfer for a retained complete coarse
progression fiber in a subset B. The charge of its local exceptional label
is exactly outer cellMass times local exceptional cellMass. Uses the explicit
Fin M-to-coarse-fiber equivalence composed with the retained-fiber equivalence.
Compiles, olean built, permitted axioms only.

Checkpoint after179: Spec.lean unchanged with original sorry. No proof or
disproof submitted. Almost-complete flat progression partitions are now
verified (175-176), as are the Bohr coarse partition and exact mass-refinement
links (177-179). They are NOT YET assembled into a single Bohr-domain flat
partition or the global inverse-to-AP density increment.

Suggested next assembly, not proved:
- For each retained coarse Bohr fiber, use file176 on the entire length-K
  progression (all its points lie in the local quadraticity domain).
- Pull its local label back through the exact coordinate and refine the
  restricted coarse label. File179 controls conditional exceptional mass;
  file171 adds that mass to the coarse exceptional mass.
- Prove final fiber geometry by composing the arbitrary inner AP geometry
  from176 with the retained coarse AP geometry; product strides remain proper
  in natural indices. The inner partition is NOT necessarily progressionLabel
  for one fixed stride, so file174 alone is not this final composition theorem.
- On ZMod p, identify bohrIndices(C,rho,0,1,p) with bohr(C,rho), using the
  bijection of Fin p and ZMod p. Stable radius bounds control the boundary;
  a size budget controls the terminal incomplete-block loss.
- Apply file168 directly to correlations, avoiding phase-grid boundary trimming.
Even completing that U3 step leaves higher orders and summability-strength
bounds unresolved.

### 180. `Submission/RetainedProgressionAssembly.lean`
Assembles arbitrary local partial partitions on retained coarse progression
fibers. Conditional bad mass <=tau adds at most tau globally. Arbitrary inner
AP fibers compose to exact AP fibers with product stride. EVERY listed final
index is in B (not merely every fiber point); this supports exact averaging.
Compiles, olean built, permitted axioms only.

### 181. `Submission/SubsetLocalQuadraticPartition.lean`
Combines180 with local quadratic flat partitions176. Produces a flat partition
of an arbitrary subset B of Fin N, provided B's images lie in the local
quadraticity domain. The loss is the unretained coarse-fiber mass plus the
two local endpoint losses. Empty coarse fibers get a vacuous fallback label,
so no local-domain hypothesis is asserted for absent fibers. Every good cell
is exactly a proper AP in natural indices, entirely inside B. Compiles, olean
built, permitted axioms only.

### 182. `Submission/BohrLocalQuadraticPartition.lean`
The coarse Bohr partition178 and local refinement181 are now ASSEMBLED into
one theorem. Exceptional mass accounts explicitly for the terminal coarse
block, the inner Bohr boundary, and both local endpoint losses. Phase error
and product-stride bounds are retained. Compiles, olean built, permitted axioms.

### 183. `Submission/ZModBohrIndices.lean`
Explicit Fin p <-> ZMod p equivalence and its restriction to Bohr indices.
Cardinalities, boundary cardinalities, and normalized averages transport
exactly. Stable Bohr boundary fraction <=1/z. For rho>=1/64,
 p <=257^(2*rank)*|bohrIndices|.
Compiles, olean built, permitted axioms only.

### 184. `Submission/StableBohrQuadraticPartition.lean`
A flat partition on a stable cyclic Bohr domain, with exceptional mass at most
 ((2n0+1)^(2*rank)*K*257^(2*rank))/p + 1/z
 + recurrenceBound(card I,t)*M/K + (2n+1)^(2*card I)*L/M.
The phase error is 2*M^2*2^-t+2L/n, and all good AP fibers are proper in natural
indices. All costs are explicit in rank, modulus, and auxiliary parameters.
Compiles, olean built, permitted axioms only.

### 185. `Submission/ProgressionCellMean.lean`
Exact equivalence and normalized-mean transfer from any cell with the verified
AP fiber characterization to Fin L. Also proves injectivity of the translated
AP in ZMod p when its unshifted natural indices lie below p. Compiles, olean
built, permitted axioms only.

### 186. `Submission/QuadraticCorrelationProgressionIncrement.lean`
The density-preserving correlation-to-progression step is now complete.
Defines partitionError, partitionLoss, partitionStride. Averaged normalized
quadratic correlation>=r on a stable Bohr set, with joint centering and the
budget partitionError+2*partitionLoss<=r/2, gives a PROPER length-L cyclic AP
with positive mean >=r/16. Uses arbitrary partial partition selection168,
not phase-grid cells. Compiles, olean built, permitted axioms only.

### 187. `Submission/ProgressionIncrementParameters.lean`
Explicit non-circular parameter choices. Let roundedScale(A,r)=ceil(64A/r)+1.
 z=roundedScale(1,r), n=roundedScale(L,r),
 M=roundedScale((2n+1)^2*L,r),
 t=flattenAccuracy(M,clog(2,z)),
 K=roundedScale(recurrenceBound(1,t)*M,r),
 n0=256*K*windowDenominator(D,z)+1.
Defines incrementThreshold(D,L,r) by rounding
 ((2n0+1)^(2D)*K*257^(2D))/r with the same factor64.
For rank<=D and p>=threshold, proves the FULL partition error budget.
Also proves the Bohr mesh condition uniformly for rho>=1/64. Each individual
loss is <=r/64; phase error <=r/16. Compiles, olean built, permitted axioms.
Technical: do not use broad positivity on recurrenceBound parameters. Supply
Nat.cast_nonneg and multiplication/division nonnegativity explicitly.

### 188. `Submission/U3ProgressionDensityIncrement.lean`
The normalized inverse165 and progression transfer186-187 are now assembled.
For centered one-bounded real f on ZMod p with bijective doubling, delta>0,
 delta<=uniformityPower 2 f, 0<r<=normalizedCorrelation(delta), and
 p>=incrementThreshold(normalizedRank(delta),L,r),
produces a proper length-L AP with mean(f)>=r/16 and explicit stride bound.
The indicator corollary gives density(A on the AP)>=density(A)+r/16.
THIS CLOSES THE GLOBAL U3-TO-PROGRESSION DENSITY-TRANSFER GAP.
Compiles, olean built, permitted axioms only.

### 189. `Submission/FourPatternProgressionIncrement.lean`
Applies188 to four-pattern-free sets in prime cyclic groups. The gain is
fourPolynomialGain(alpha)/16, a fixed power of density. Defines
fourProgressionThreshold and fourProgressionStride. Four distinct slopes
force p>=4 and hence invertibility of doubling, proved explicitly. Above the
threshold, obtains a proper length-L AP with the polynomial density gain.
Compiles, olean built, permitted axioms only.

Checkpoint after189: Spec.lean STILL contains the unchanged original sorry.
No proof or disproof of the full conjecture has been completed or submitted.
The former U3 density-preserving transfer gap is CLOSED by188. Higher Gowers
orders and summability-strength quantitative estimates remain independent gaps.

Next iteration issue, NOT resolved: pulling a cyclic AP back to a finite
integer interval and re-embedding in a larger prime modulus loses a fixed
factor of ambient density, which overwhelms the small polynomial gain. Do
NOT assume that naive repeated cyclic embedding preserves increments.
A potential interval-relative route would use f=1_A-alpha*1_[N] (jointly
centered in the larger group), a two-function/masked counting lemma, and
careful cutting of the positive-mean AP into pieces lying inside the original
interval. None of those steps is yet assembled into an iteration theorem.
Classical iteration costs here also do not automatically imply reciprocal
summability, even if an integer four-term bound is completed.

### 190. `Submission/MaskedUniformityCounting.lean`
General two-function counting lemma, comparing any one-bounded f and g with
one-bounded difference. Specializes to 1_A-alpha*1_B, allowing a nonconstant
mask instead of the ambient constant baseline. If B has pattern average>=beta
and A's diagonal contribution<=alpha^k*beta/4, obtains a relative uniformity
lower bound. This works for every counting order n, although structural inverse
results remain U3-only. Compiles, olean built, permitted axioms only.

### 191. `Submission/CyclicIntervalMask.lean`
Defines castSet, intervalMask, intervalDensity, and relativeBalance. For
S subset [0,N), N<=p, relativeBalance=1_castS-(|S|/N)*1_intervalMask has EXACT
ambient mean zero and is one-bounded. It vanishes outside the interval mask.
A rectangle of initial points and differences gives a pattern-count lower
bound; for 8<=N<=p<=4N, the four-pattern average of the mask is >=1/1024.
Compiles, olean built, permitted axioms only.
Technical: annotate the domain in `S.image (fun k : Nat => (k : ZMod p))`.
Without `: Nat`, Lean inferred a ZMod-domain identity map and coerced the entire
finset first, creating a misleading nested-image definition.

### 192. `Submission/IntervalFourUniformity.lean`
Proves four balanced consecutive natural values in a four-AP-free set are
constant. For S subset [0,N) and 2N<=p, every modular four-pattern in castSet(S)
is consequently diagonal. Combines this with190-191 to prove
 ((intervalDensity(S,N)^4/8192)^8) < U3(relativeBalance)^8
when p<=4N, N>=8, and 4096<=intervalDensity(S,N)^4*p.
The density is the ORIGINAL interval density, not the diluted cyclic density.
Compiles, olean built, permitted axioms only.

### Strengthening of file186
Added `quadratic_correlation_progression_increment_with_span`, retaining
 (L-1)*d<p
from the original natural-index geometry. The previous theorem and its type
are preserved as a wrapper. Both compile, olean rebuilt, permitted axioms.
Properness alone does NOT imply this span bound; retaining the construction's
actual geometry is essential to the rectification argument.

### 193. `Submission/U3ProgressionSpan.lean`
Carries the stronger span conclusion through the normalized inverse and
explicit parameter choices. This enables at most one wraparound of the cyclic
AP. Compiles, olean built, permitted axioms only.

### 194. `Submission/NaturalProgressionCuts.lean`
Defines affineCut(A,d,T,L)=min(L,ceilDiv(T-A,d)). For A<p, d>0, span<p, and
N<=p, the condition (A+j*d)%p<N is exactly the union of two index intervals:
 [0,cut(N)) and [cut(p),cut(p+N)).
Gives exact unwrapped integer formulas on both pieces. No hidden assumption
that a proper cyclic AP has only one wraparound is used.
Compiles, olean built, permitted axioms only.

### 195. `Submission/TwoIntervalMeanSelection.lean`
If a function bounded above by1 has mean>=gamma>0 on Fin L and vanishes outside
two disjoint index intervals, one piece has length>=gamma*L/2 and mean>=gamma/2.
Proof selects a piece carrying at least half the signed total mass. Compiles,
olean built, permitted axioms only.

### 196. `Submission/IntervalProgressionRectification.lean`
Combines194-195. A positive mean gamma of relativeBalance on a span<p cyclic
AP yields a genuine integer AP wholly inside [0,N), of length>=gamma*L/2,
whose trace of S has density>=intervalDensity(S,N)+gamma/2. Defines
progressionTrace and proves exact mean identities and inheritance of
IsAPOfLengthFree(k) for every k>=2 under positive-stride pullback.
Compiles, olean built, permitted axioms only.

### 197. `Submission/IntegerFourDensityIncrement.lean`
The ITERATABLE integer-interval increment is now complete. For a fixed positive
lower density alpha, defines
 delta(alpha)=(alpha^4/8192)^8,
 intervalGain(alpha)=delta(alpha)^1988534/correlationDenominator,
 requestedCyclicLength(alpha,ell)=roundedScale(ell,intervalGain(alpha)),
and intervalStepThreshold(alpha,ell) controlling N>=8, diagonal negligibility,
and the U3 inverse modulus threshold. Bertrand chooses 2N<p<=4N.
If N is above the threshold and S subset [0,N) is four-term-free with actual
density beta>=alpha, produces T subset [0,m), still four-term-free, with
 0<m, ell<=m<=N, density(T)>=beta+intervalGain(alpha)/32.
NO fixed density factor is lost on embedding or rectification. Compiles,
olean built, permitted axioms only.

### 198. `Submission/IntegerFourDensityBound.lean`
Finite iteration of197, uniformly at the original lower density alpha.
 Q(alpha,0)=1; Q(alpha,t+1)=intervalStepThreshold(alpha,Q(alpha,t)).
Iteration proves density(S)+t*intervalGain(alpha)/32<=1 whenever N>=Q(alpha,t).
Taking t=ceil(32/intervalGain(alpha))+1 gives `fourIntervalBound(alpha)` and
 integer_four_density_bound:
  alpha>0, S subset [0,N), S four-term-free, density(S)>=alpha
  ==> N<fourIntervalBound(alpha).
This is a complete explicit finite four-term density bound. Compiles, olean
built, permitted axioms only.

Checkpoint after198: Spec.lean still has its unchanged original sorry. No proof
or disproof of the full conjecture has been submitted. The former integer
four-term iteration gap is now CLOSED by197-198. HOWEVER the resulting
threshold costs have NOT been shown to imply reciprocal summability; a finite
threshold for every positive density does not suffice. Higher uniformity
orders are also still missing. Thus neither arbitrary AP lengths nor the
original divergent-reciprocal-sum implication has been settled.

### 199. `Submission/QuadraticRecurrenceAverages.lean`
Finite complex averaging estimates, independent of progression-counting results:
Jensen for squared norm; exact pair-energy identity; upper and lower energy
bounds from off-diagonal correlation bounds; geometric-sum/mean norm bounds;
interval shift mean difference at most 2h/N; averaged short-shift bound.
Compiles, olean built, permitted axioms only.

### 200. `Submission/QuadraticRecurrenceExtraction.lean`
Two elementary extraction steps. `avoidance_frequency`: unit phases avoiding
1 by epsilon, with K*epsilon^2>=8, have some 0<k<K whose mean has norm>1/(4K).
Uses the diagonal contribution to a finite Fejer energy. `short_shift_correlation`:
a unit sequence with interval mean>=delta, 2H/N<=delta/2 and 1/H<=delta^2/8,
has distinct shifts i,j<H with correlation norm>delta^2/16.
Compiles, olean built, permitted axioms only.

### 201. `Submission/PolynomialSquareRecurrence.lean`
Exact geometric formula for correlations of square phases. Combines199-200 to
prove square_recurrence_parameters for arbitrary K,H,N with
 K*epsilon^2>=8, N>=16KH, H>=128K^2, epsilon*N>=1024K^3H.
The dyadic corollary `single_square_recurrence` proves, for every unit v,
 0<d<singleRecurrenceBound(t)=2^(11t+38)+1,
 norm(v^(d^2)-1)<=2^-t.
Thus the one-phase recurrence cost is degree ELEVEN in inverse accuracy,
without any AP theorem. Compiles, olean built, permitted axioms only.

### 202. `Submission/PolynomialMixedRecurrence.lean`
Elementary grid-pigeonhole linear recurrence plus201. Rescaling/induction
handles arbitrary finite collections of exponent-one and exponent-two phases.
 mixedExponent(0,t)=0;
 mixedExponent(m+1,t)=mixedExponent(m,23t+78)+11t+39.
 polynomialRecurrenceBound(m,t)=2^mixedExponent(m,t)+1.
Also proves 2*mixedExponent(m,t)+t+4<=23^m*(t+4), making the dependence on
inverse accuracy polynomial at each fixed number of phases.
`polynomial_mixed_recurrence` has the same conclusions as the old simultaneous
mixed recurrence. Compiles, olean built, permitted axioms only.

### Strengthening of file159 (`SimultaneousQuadraticRecurrence.lean`)
`recurrenceBound m t` now DEFINITIONALLY uses polynomialRecurrenceBound m t
from202, instead of colorThreeBound((2t+8)m). The public theorem types remain
unchanged. Their proofs now use202. The old phaseLabel_close lemma remains.
The imports were augmented in this AUXILIARY file (Spec imports unchanged).
ALL 22 previously compiled downstream principal files rebuilt successfully,
including IntegerFourDensityIncrement and IntegerFourDensityBound. Rebuild
log: /tmp/rebuild_recurrence.log. The old source backup is at
/tmp/SimultaneousQuadraticRecurrence.old.lean. No rollback is needed.

### 203. `Submission/PolynomialProgressionThresholds.lean`
Defines HasPolyBound(f,e): exists C, forall n, f(n)+1<=C*(n+1)^e, and proves
closure under affine operations, products, powers, composition, and roundedScale.
Quantifies the recurrence improvement:
 recurrenceBound(1,flattenAccuracy(M,s))+1
 <=(2^(11s+72)+2)*(M+1)^22.
Then incrementLocalLength has degree3, incrementCoarseLength and CoarseMesh
have degree69, and
 incrementThreshold(D,L,r)+1<=C(D,r)*(L+1)^(69*(2D+1)).
The coefficient is existential and depends on D,r; there is NO uniform-in-r
coefficient claim. Compiles, olean built, permitted axioms only.

### 204. `Submission/PolynomialFourDensityBound.lean`
Transfers203 to intervalStepThreshold. Defines
 fourStepDegree(alpha)=69*(2*normalizedRank(intervalUniformityThreshold(alpha))+1).
Proves an elementary polynomial iteration bound and
 fourIterationThreshold(alpha,t)+1<=B(alpha)^((fourStepDegree(alpha)+1)^t)
for some B(alpha)>=2. The resulting integer_four_power_density_bound is a
complete four-term finite-density theorem with this power-iteration threshold.
The dependence of B(alpha) on alpha is NOT quantitatively estimated in204.
Compiles, olean built, permitted axioms only.

Checkpoint after204: The polynomial recurrence improvement is COMPLETE and
fully integrated, not just an isolated lemma. The original Spec.lean remains
UNCHANGED with its original sorry. No proof or disproof has been submitted.
The new power-iteration threshold does NOT establish reciprocal summability.
In particular, the original task is STILL UNSOLVED. The separate missing
requirements remain reciprocal summability even at length4, and structural/
inverse/density arguments for all higher lengths. Do not present204 as a
settlement of Erdős3 or submit the admitted target.

### 205. `Submission/ExplicitProgressionThresholds.lean`
An explicit coefficient replaces the existential coefficient in203. For a
common natural base X satisfying
 X>=2^100, incrementPrecision(r)+2<=X, D+1<=X,
proves
 incrementThreshold(D,L,r)+1
 <=X^(500*(D+1))*(L+1)^(69*(2D+1)).
Tracks all scales: local length <=X^6*(L+1)^3, recurrence scale
<=X^144*(L+1)^66, coarse length <=X^151*(L+1)^69, and coarse mesh
<=X^155*(L+1)^69 (with +1 bounds as appropriate).
Compiles, olean built, permitted axioms only.
Technical note: simp only [pow_succ,Nat.mul_comm] caused enormous definitional-
equality work on natural powers. Replacing it by a two-step calc (multiply the
inequality, then a separate ring identity) fixed the timeout. The length
variable P is generalized, not let-bound, to avoid unnecessary expansion.

### 206. `Submission/DyadicFourParameters.lean`
Exact dyadic identities:
 intervalUniformityThreshold(2^-s)=2^-(32s+104),
 1/intervalGain(2^-s)=correlationDenominator*2^((32s+104)*1988534).
Uses the polynomial inverse rank bound from153 to prove existence of ONE
constant c>=100 such that, for every s, all of
 normalizedRank(intervalUniformityThreshold(2^-s))+1,
 incrementPrecision(intervalGain(2^-s))+2,
 fourIterationCount(2^-s),
 ceil(4096/(2^-s)^4)+10
are <=2^(c*(s+1)). Thus the density dependence left unspecified in204 is
now controlled. Compiles, olean built, permitted axioms only. A harmless
large-exponent non-evaluation warning appears; do NOT raise the exponentiation
threshold and attempt to compute the huge real constants.

### 207. `Submission/DyadicFourDensityBound.lean`
Combines205-206. If all parameters fit the common base X>=2^100, then
 intervalStepThreshold(alpha,ell)+1
 <=X^(1000X)*(ell+1)^(1000X).
Proves a purely numerical iteration lemma: for h>=100 and t<=2^h,
 ((2^h)^(1000*2^h)+2)^((1000*2^h+1)^t) <=2^(2^(2^(4h))).
The final `dyadic_four_density_bound` states:
 exists c>0, forall s N S,
 S subset range N, S four-term-free, 2^-s<=density(S,N)
 ==> N<2^(2^(2^(c*(s+1)))).
This is a UNIFORM quantitative four-term density theorem, with all dependence
on inverse density bounded. It corresponds to a double exponential in a
fixed power of inverse density. Compiles, olean built, permitted axioms only.

Checkpoint after207: The previously unspecified coefficient dependence in204
is now CLOSED, and the full dyadic quantitative theorem is verified. The
bound is still far too weak to yield summability of the geometric extremal-
density series. No four-term reciprocal-summability theorem and no higher-
length inverse theorem has been proved. Spec.lean STILL has its original
unchanged sorry. NO proof or disproof has been submitted. The task remains
UNSOLVED; do not submit the admitted target.

### 208. `Submission/HigherPhaseDifferences.lean`
Generic additive finite-difference algebra. diffIter(k,f)=Delta_1^[k](f).
Proves mapping, subtraction, shift, and natural-to-integer pullback identities.
`shifted_difference_top`: if diffIter(k+1,f) is constant z, then the kth
unit-step difference of f(n+i)-f(n+j), j<=i, is constant (i-j) smul z.
`diffIter_monomial`: diffIter(k,n^k smul z) is constant k! smul z, in every
abelian group, using Mathlib's exact forward-difference factorial identity.
Defines phase:Additive Circle->Complex and verifies unit norm, add/subtract,
and nsmul/power coercion identities. Compiles, olean built, permitted axioms.

### 209. `Submission/HigherPhaseWeylInverse.lean`
A quantitative Weyl LEADING-COEFFICIENT estimate, NOT a Gowers inverse theorem.
Defines weylConstant(0)=2, weylConstant(k+1)=5*weylConstant(k)+10; k indexes
degree k+1. If diffIter(k+1,f)=constant z for a circle-valued sequence,
 norm(intervalMean_N phase(f))>=2^-s,
 N>=2^(weylConstant(k)*(s+1)),
then some 0<d<=2^(weylConstant(k)*(s+1)) satisfies
 norm(phase(z)^d-1)<=2^(weylConstant(k)*(s+1))/N.
Proof iterates200's short-shift correlation extraction: H=2^(2s+4), new mean
parameter s'=2s+4, with exact finite-difference bookkeeping from208.
Compiles, olean built, permitted axioms only.

### 210. `Submission/PolynomialMonomialRecurrence.lean`
Uniform monomial recurrence in EVERY POSITIVE DEGREE. Defines
 powerRecurrenceConstant(k)=
   (7*weylConstant(k)+(k+1)!+4)*(k+1)+1.
`monomial_recurrence`: for unit v and arbitrary k,t, there is
 0<d<=2^(powerRecurrenceConstant(k)*(t+1))
 with norm(v^(d^(k+1))-1)<=2^-t.
Proof uses Fejer frequency extraction200,209, the factorial top difference208,
and unit-power oscillation. Polynomial dependence on inverse accuracy at
fixed degree. The degree-zero assertion would be false and is NOT made.
Compiles, olean built, permitted axioms only.

### 211. `Submission/SimultaneousPolynomialRecurrence.lean`
Extends202 from degrees1,2 to arbitrary bounded positive degrees. Defines
 degreeRecurrenceConstant(K)=1+sum_{k<K} powerRecurrenceConstant(k),
 simultaneousPowerConstant(K,0)=0,
 simultaneousPowerConstant(K,m+1)=
   simultaneousPowerConstant(K,m)*(K*degreeRecurrenceConstant(K)+1)
   +degreeRecurrenceConstant(K).
For a finite family v_i of unit phases with 1<=e_i<=K, produces a common
 0<d<=2^(simultaneousPowerConstant(K,card I)*(t+1))
 with all norm(v_i^(d^e_i)-1)<=2^-t.
Also gives a simple exponential-in-m bound on simultaneousPowerConstant.
The optimized quadratic recurrence202 remains unchanged for existing uses.
Compiles, olean built, permitted axioms only.

### 212. `Submission/HigherPhaseRepresentation.lean`
Exact algebraic circle roots prove nsmul surjectivity. Uses these roots and208
to show every circle-valued sequence with zero (K+1)st difference has exact
monomial coordinates:
 f(n)=sum_{j=0}^K n^j smul c_j.
The proof removes the top monomial after taking an actual K!th root and then
inducts. NO inference that a root is close to1 is made. Complex product form,
phase-sum oscillation, and norm subtraction identities are included.
Compiles, olean built, permitted axioms only.

### 213. `Submission/LocalPolynomialPhaseExtension.lean`
Finite-interval version with NO assumptions outside [0,N]. If
 diffIter(K+1,f)(n)=0 whenever n+K+1<=N,
then truncated Newton's formula holds at every n<=N. Defines newtonExtension,
proves its (K+1)st difference vanishes globally and that it agrees with f on
[0,N]. Applying212 yields exact local monomial/product coordinates.
Compiles, olean built, permitted axioms only.

### 214. `Submission/HigherPolynomialFlattening.lean`
Simultaneous flattening for arbitrary finite-interval circle polynomial phases.
 monomialFlattenBound(K,m,t)=2^(simultaneousPowerConstant(K,m*K)*(t+1)).
If L>0, L*bound<=N, and each phase has vanishing (K+1)st finite differences
on [0,N], obtains 0<d<=bound with, for all phases and n<=L,
 norm(phase(f_i(nd))-phase(f_i(0)))<=K*L^K*2^-t.
Uses exact local coordinates213 and simultaneous recurrence211 on all
nonconstant coefficients. Sets
 higherFlattenAccuracy(K,L,s)=s+clog_2(K+1)+K*clog_2(L)
to obtain error<=2^-s. This is POINTWISE oscillation, NOT a partition theorem.
Compiles, olean built, permitted axioms only.

### 215. `Submission/HigherLocalPolynomialProgressions.lean`
Defines additive cubeDifference and IsLocallyPolynomial(R,K,f), requiring
zero difference on EVERY complete (K+1)-cube inside R. Proves that restriction
to a progression lying wholly in R has the finite-window vanishing differences
needed by213-214. `local_polynomial_progression_flattening` gives the resulting
bounded-stride, dyadic-accuracy flat subprogression for any fixed degree.
No injectivity is asserted for its image in an arbitrary ambient group;
torsion/properness still needs a separate geometric argument. No higher inverse
theorem producing these phases is asserted. Compiles, olean built, permitted axioms.

Checkpoint after215: Arbitrary-degree monomial recurrence, simultaneous
recurrence, exact finite-interval phase coordinates, and local POINTWISE
flattening are now COMPLETE. These do not supply higher Gowers inverse
structure or a density-preserving higher-degree flat AP partition. The latter
could be approached by recursively annihilating the top finite difference,
removing its small binomial term on each coarse fiber, and refining by a
lower-degree partition; the exact top-difference dilation and label bookkeeping
for that construction have NOT yet been proved in this development.
The reciprocal-summability gap at length4 also remains entirely open.
Spec.lean is still unchanged with its original sorry; NO proof or disproof
has been submitted. The original task is STILL UNSOLVED.

### 216. `Submission/HigherDifferenceDilation.lean`
Exact top-difference dilation: if diffIter(k,f) is constant z, then
 diffIter(k, n ↦ f(a+n*d)) is constant (d^k) smul z.
Also proves the binomial top-difference identity, degree lowering by subtracting
n.choose k smul z, and the resulting phase error bound M^k*eta on [0,M].
Compiles, olean built; permitted axioms only.

### 217. `Submission/CanonicalPartialPartition.lean`
Canonicalizes active labels of a partial partition by representative points.
Preserves exceptional mass, exact fibers, phase approximants and progression
geometry; no finiteness assumption on the original label type is necessary.
Compiles, olean built; permitted axioms only.

### 218. `Submission/IntervalPartitionAssembly.lean`
Refines every complete coarse progression by an inner partial partition.
Total exceptional mass is at most d*M/N plus the uniform inner loss.
Proves exact coordinate reconstruction and multiplication of stride bounds.
Compiles, olean built; permitted axioms only.

### 219. `Submission/HigherPartitionParameters.lean`
Defines recursive higher-degree partition thresholds and stride bounds.
At each degree step the error and exceptional-mass budgets are halved.
Proves positivity, top-coefficient error control and terminal block loss.
Compiles, olean built; permitted axioms only.

### 220. `Submission/HigherPolynomialProgressionPartition.lean`
Complete arbitrary-degree simultaneous phase partition on an interval.
For globally polynomial circle phases of degree k, sufficiently large N
admits an Option(Fin N)-labelled partition with exceptional mass <=2^-s,
phase oscillation <=2^-s, and exact proper length-L progression cells with
bounded natural strides. The proof annihilates the top coefficient, removes
the resulting small Newton term, inducts on degree in each coarse fiber,
assembles and canonicalizes. This closes the former pointwise-to-partition
gap; it does not supply an inverse theorem producing the phases.
Compiles, olean built; permitted axioms only.

### 221. `Submission/LocalHigherProgressionPartition.lean`
Extends220 to phases satisfying finite differences only inside [0,N), using
exact Newton extension. Also restricts locally polynomial group phases to
progressions lying wholly in their domain. Properness here concerns natural
coordinates; properness of the image in a torsion group needs geometry.
Compiles, olean built; permitted axioms only.

### 222. `Submission/HigherPartitionPowerBounds.lean`
Proves polynomial dependence on requested length L for both the threshold
and stride of220 at fixed degree, number of phases and accuracy. Degree is
recursive: e(0,m)=1,
 e(k+1,m)=e(k,m)*((k+1)*simultaneousPowerConstant(k+1,m)+1).
Compiles, olean built; permitted axioms only.

### 223. `Submission/BohrLocalPolynomialPartition.lean`
Assembles higher-degree phase partitions inside retained coarse fibers of
subsets and Bohr sets. The stable cyclic specialization has exceptional mass
 terminalCost/p + 1/z + 2^-s,
with explicit terminal cost and stride. Good cells have exact progression
fiber equivalence and lie wholly inside the Bohr domain.
Compiles, olean built; permitted axioms only.

### 224. `Submission/PolynomialCorrelationIncrement.lean`
CONDITIONAL arbitrary-degree correlation-to-progression density increment.
Given a centered one-bounded real f, locally polynomial phases q(a,x) on a
full Bohr neighborhood and averaged normalized squared correlation >=r>0,
a stable-radius partition satisfying the explicit budget produces a proper
length-L AP with mean f >=r/16 and (L-1)*d<p. Local polynomial correlation is
an explicit hypothesis, NOT a claimed higher-order inverse theorem.
Compiles, olean built; permitted axioms only.

### 225. `Submission/PolynomialIncrementParameters.lean`
Non-circular explicit parameters for224. Chooses accuracy using clog_2 of
incrementPrecision(r), a coarse length from219, and a mesh from the stable
radius window denominator. Proves mesh, terminal loss and full budget bounds.
Packages the conditional increment with explicit threshold and stride.
The threshold is polynomial in L at fixed k,D,r, of degree
 higherPartitionDegree(k,1)*(2D+1).
Compiles, olean built; permitted axioms only.

Checkpoint after225: The arbitrary-degree density-preserving partition and
conditional correlation-to-AP increment are COMPLETE. A higher-order inverse
theorem providing the requisite structure has NOT been proved. Even such an
inverse theorem with merely qualitative or current weak quantitative bounds
would not imply reciprocal summability. The reciprocal-summability gap at
length4 remains. Spec.lean is unchanged with its original sorry. The original
conjecture is STILL UNSOLVED; no settlement has been submitted.

### 226. `Submission/HigherUniformityDefect.lean`
Exact arbitrary-degree cube-defect identity and maximal-uniformity inverse.
Defines cubeDefect(k,q) as the mean squared norm of
 phase(cubeDifference(k,q,h,x))-1
averaged over ALL direction tuples and basepoints in a finite abelian group.
Verified:
* cubeDefect(n+1,q)=2*(1-uniformityPower(n,phase o q)).
* Defect zero iff all corresponding additive cube differences vanish.
* For a circle phase, maximal uniformity iff global polynomiality of degree n.
* uniformityPower(n,f)<=mean(norm(f)) for every one-bounded f.
* A one-bounded f has maximal uniformity iff it is EXACTLY a global circle
  polynomial phase of degree at most n. Norm one at every point is proved,
  rather than assumed or obtained by dropping zero values.
This is the EXACT extremal case only, NOT a general positive-uniformity inverse.
Compiles, olean built; permitted axioms only.

### 227. `Submission/HigherUniformityPerturbation.lean`
Dimension-free perturbation and radial normalization for arbitrary degree.
Verified:
* meanDistance(derivative(f,h),derivative(g,h))<=2*meanDistance(f,g).
* abs(uniformityPower(n,f)-uniformityPower(n,g))
  <=2^(n+1)*meanDistance(f,g) for one-bounded f,g.
* radialPhase(f,x)=Circle.exp(arg(f(x))) genuinely has norm one, also at zero.
* meanDistance(f,phase o radialPhase(f))=1-mean(norm(f)).
* If uniformityPower(n,f)>=1-epsilon, there is a circle phase q with
  meanDistance(f,phase o q)<=epsilon and
  cubeDefect(n+1,q)<=(2+2^(n+2))*epsilon.
This proves approximate cube polynomiality only. It does NOT assert a
correction to an exact polynomial, and it does NOT give an inverse theorem
for a small positive uniformity lower bound.
Compiles, olean built; permitted axioms only.

Dependency audit at this checkpoint: the local import closure of
ThreeAPReciprocalSummability, PolynomialIncrementParameters and
DyadicFourDensityBound comprises194 files. A source scan found no occurrences
of sorry, added axioms, native_decide or unsafe in this closure. The three-term
summability endpoint was rechecked and prints only permitted axioms.

Checkpoint after227: The exact maximal-uniformity classification and a
near-maximal cube-defect estimate are now complete in all degrees. Neither
handles the small uniformity lower bounds furnished by the AP counting lemma.
No general higher inverse theorem or new reciprocal-summability estimate has
been proved. In particular, the length4 summability gap persists. Spec.lean
is unchanged with its original sorry. NO proof or disproof of the original
conjecture has been submitted; the task remains UNSOLVED.

### 228. `Submission/HigherPolynomialSeparation.lean`
Uniform separation for polynomial phases on any finite abelian group.
Defines polynomialGap(n)=4^-n. A nonconstant global degree-n circle polynomial
q satisfies norm(mean(phase o q))^2<=1-polynomialGap(n). The proof inducts on
degree and uses a paired-direction argument; the gap is independent of |G|.
Distinct polynomial phases modulo constants have mean squared distance >=gap.
If their L1 distance is <gap/2, they differ by a constant; if they agree at zero,
they are identical. Includes derivative degree lowering and polynomial subtraction.
Compiles, olean built; permitted axioms only.

### 229. `Submission/DensePartialHomomorphism.lean`
Exact extension from a dense partial domain, for possibly noncommutative groups.
If S is a subset of a finite group with 4*(|G|-|S|)<|G|, and f preserves every
product whose two factors and product all lie in S, then f extends UNIQUELY to
a group homomorphism. No finiteness/topology assumption on the target.
The proof first gives a finite union-bound lemma for common good points under
arbitrary permutations, then proves f(xb)*f(b)^-1 independent of admissible b.
Compiles, olean built; permitted axioms only.

### 230. `Submission/PolynomialDerivativeConsistency.lean`
If P_h,P_k,P_(h+k) are degree-n polynomial phases approximating the respective
derivatives of a circle function q in L1 to error eta, with 3eta<gap(n)/2,
the normalized P's satisfy an EXACT cocycle identity on that triple. The
approximation error disappears via228's separation lemma, not by a limit or
an assumed coherence of independently selected phases. Includes L1 triangle,
translation and unit-phase product bounds, plus polynomial addition/translation.
Compiles, olean built; permitted axioms only.

### 231. `Submission/DensePolynomialCocycle.lean`
Constructs the semidirect group of translations and normalized circle functions.
Using229, extends normalized polynomial cocycles from a set of directions of
density >3/4 to all directions. Polynomial degree is preserved, using a good-pair
representation of each new direction. Combines230 with the extension theorem:
sufficiently accurate polynomial derivative approximations on a dense direction
set yield a global normalized polynomial cocycle. Still conditional on those
accurate approximations.
Compiles, olean built; permitted axioms only.

### 232. `Submission/PolynomialCocycleIntegration.lean`
Integrates every normalized circle cocycle on ZMod p, for p>0. This uses
CYCLICITY, not an unproved symmetry/integration principle for arbitrary groups.
Constructs a potential from partial sums in direction1, chooses an exact pth
circle root to cancel the period, and proves the resulting sequence periodic.
Normalized derivatives equal the prescribed cocycle in every direction by
induction on the natural representative. A degree-n polynomial cocycle yields
a global degree-(n+1) polynomial potential. No claim that the chosen root is
close to1 is used.
Compiles, olean built; permitted axioms only.

### 233. `Submission/PhaseApproximationAverages.lean`
Quantitative averaging tools for the near-maximal inverse argument:
* A circle phase q is L1-close to some constant c, with squared error
  <=2*(1-norm(mean(phase o q))^2).
* U2 near maximal similarly gives approximation by a character times a constant.
* Closeness to a constant lower-bounds squared mean modulus.
* badMass(S)=|G\S|/|G|; elementary mean-defect and threshold/Markov estimates.
* badMass<=1/8 implies the strict >3/4 density needed for229.
Compiles, olean built; permitted axioms only.

### 234. `Submission/DenseDerivativeIntegration.lean`
Quantitatively combines231-233. On a cyclic group, degree-n polynomial derivative
approximations on S with error eta, >3/4 density, and 3eta<gap(n)/2 produce an
ACTUAL degree-(n+1) polynomial phase r approximating q with squared L1 error
 <=4eta+2*badMass(S).
After integrating the cocycle, the residual has derivatives close to constants
on S, hence U2 near maximal. Fourier extraction provides the character twist
and constant needed for a phase close to q, not merely an arbitrary potential.
Compiles, olean built; permitted axioms only.

### 235. `Submission/NearMaximalCyclicInverse.lean`
COMPLETE dimension-free near-maximal (99-percent) inverse theorem in ALL degrees.
For every n and epsilon>0, there exists delta>0, UNIFORM in p>0, such that
any one-bounded complex f on ZMod p with
 uniformityPower(n,f)>=1-delta
is L1-close (error<=epsilon) to an exact global circle polynomial of degree n.
First proves the unit-phase version by induction: take a near-full set of good
derivatives, approximate them by the inductive hypothesis, and use234. Then
radial normalization plus227's perturbation bound gives the one-bounded version.
The quantified NeZero p instance is explicit; no primality assumption is needed.
Compiles, olean built; printed axioms are exactly the permitted three.

Checkpoint after235: The previously missing correction from sufficiently small
average higher cube defect to an exact polynomial phase is now COMPLETE on
finite cyclic groups, in all degrees, with thresholds independent of modulus.
This does NOT extend the inverse statement to an arbitrary small positive
uniformity lower bound. In particular the AP counting lemma's hypotheses do
NOT place a balanced indicator in the near-maximal regime. No improvement of
the length4 reciprocal-summability estimate has been obtained. Spec.lean remains
unchanged with its original sorry, and the original conjecture remains UNSOLVED.
No settlement has been submitted.

### 236. `Submission/CyclicStabilityParameters.lean`
Explicit power-law parameters for235. Defines
 E(0)=2, E(n+1)=2+2E(n),
 A(0)=1, A(n+1)=4+A(n)+(2n+5)E(n),
 phaseTolerance(n,epsilon)=2^-A(n)*epsilon^E(n),
 derivativeAccuracy(n,epsilon)=4^-n*epsilon^2/32.
Proves E(n)+2=2^(n+2) and the exact recursive identity
 tolerance(n+1,epsilon)=(epsilon^2/16)*tolerance(n,derivativeAccuracy(n,epsilon)).
Also positivity, all density/separation/error budget bounds for 0<epsilon<=1,
and tolerance(n,epsilon)<=epsilon on the unit interval.
Compiles, olean built; permitted axioms only.

### 237. `Submission/QuantitativeCyclicInverse.lean`
Replaces235's existential threshold by236's explicit modulus. For unit phases,
 uniformityPower(n,f)>=1-phaseTolerance(n,epsilon)
forces L1 error<=epsilon from a degree-n polynomial phase. For general one-bounded
complex functions, uses
 boundedTolerance(n,epsilon)=phaseTolerance(n,epsilon/2)/2^(n+2).
Uniform in every nonzero cyclic modulus. The exponent is explicitly 2^(n+2)-2.
Compiles, olean built; permitted axioms only.

### 238. `Submission/NearConstantUniformity.lean`
A local estimate that allows a major stability bootstrap. On any finite abelian
group, if a one-bounded f satisfies
 meanDistance(f,1)<=localRadius(n)=2^-(n+3),
then uniformityPower(n,f)<=uniformityPower(0,f).
Proof: a trivial Fourier coefficient carrying >=half the energy is maximal,
so the fourth Fourier moment is at most its squared norm. Induct on n, using
that every derivative is at most twice as far from1 in L1.
Also proves exact invariance of uniformityPower(n,f) under multiplication by
any global degree-n polynomial phase, for arbitrary complex f (not only units).
Compiles, olean built; permitted axioms only.

### 239. `Submission/SharpCyclicStability.lean`
Upgrades coarse stability to square-root defect control. Introduces
meanSquareDistance=mean(norm(f-g)^2), with the L1 Jensen bound.
For one-bounded complex f, a unit constant approximates it with mean-square
error <=2*(1-uniformityPower(0,f)); zero values are not discarded.
`improve_coarse_polynomial_approximation`: on ANY finite abelian group, an
L1 polynomial approximation within localRadius(n) can be improved to an exact
degree-n polynomial phase with mean-square error
 <=2*(1-uniformityPower(n,f)).
Uses exact polynomial twisting and238's near-constant bound.
On ZMod p,237 supplies the coarse approximation once the defect is at most
 sharpTolerance(n)=boundedTolerance(n,localRadius(n))>0.
`sharp_cyclic_inverse_L1` consequently uses the threshold
 min(sharpTolerance(n),epsilon^2/2)
to give L1 error<=epsilon. Thus the small-error exponent improves to TWO,
once capped by the explicit degree-only near-maximal threshold.
Compiles, olean built; permitted axioms only.

### 240. `Submission/CenteredUniformityBarrier.lean`
Applicability audit of the new stability theorem. Proves for ALL finite abelian
groups and ALL n that if 0<=f<=1, then
 uniformityPower(n, f-mean(f))<=1/4.
Uses the general bound uniformityPower(n,g)<=(mean(norm(g)))^2 and the bound
mean(abs(f-mean(f)))<=1/2. Also sharpTolerance(n)<=1/16.
Therefore a centered indicator cannot meet239's near-maximal hypothesis: the
former is <=1/4 while the latter requires >=15/16. This is a formal exclusion
of a DIRECT application, not a disproof of Erdős3 or a claim that localization
cannot help. No hidden implication from small positive to near-maximal
uniformity has been asserted.
Compiles, olean built; permitted axioms only.

Checkpoint after240: Quantitative stability in all degrees is complete with
mean-square error <=twice the defect below an explicit degree-only threshold.
The missing small-positive-uniformity/local-structure step remains;240 verifies
that the balanced indicator cannot directly invoke the new theorem. No new
reciprocal-summability estimate for length4 or longer has been proved.
Spec.lean is unchanged with its original sorry. The original task remains
UNSOLVED, and no proof/disproof has been submitted.

### 241. `Submission/LinearOrbitCompression.lean`
An elementary lattice compression lemma. A short difference of two near-integer
linear orbit points gives q<Q and an error e. The integer determinant
 D(h)=q*z(h)-b*h=h*e-q*(alpha*h-z(h))
has at most 6E+1 values. Two well-separated points in a large determinant fiber
then give |e|<=2QE/(N*m). Includes reusable short_pair and wide_pair lemmas.
Compiles, olean built; permitted axioms only.

### 242. `Submission/DenseLinearOrbitInverse.lean`
Density-form specialization of241. If H is contained in [0,N),
 N<=R*|H|, 8R(6E+1)<=N,
and every h in H has |alpha*h-z(h)|<=E/N, then some 0<q<4R satisfies
 |alpha*q-b|<=64R^2 E(6E+1)/N^2.
Compiles, olean built; permitted axioms only.

### 243. `Submission/CircleIntegerApproximation.lean`
Exact circle/real conversions, including principal angle normalization:
 unitAngle(v)=arg(v)/(2*pi), ephase(t)=exp(2*pi*i*t).
For |v|=1, ephase(unitAngle(v))=v and |unitAngle(v)|<=|v-1|/4.
For every real t there is an integer b with
 |t-b|<=|ephase(t)-1|/4.
Conversely |ephase(t)-1|<=8|t-b| for every integer b.
Also exact integer-translation and power identities.
The unfinished draft was repaired (in particular the exponential chord upper
bound lives in namespace Real, not Complex).
Compiles, olean built; permitted axioms only.

### 244. `Submission/DilatedQuadraticShift.lean`
Dilated short-shift correlation extraction, followed by the degree-two
leading-phase estimate. If diffIter(2,f)=z and the phase mean is at least delta,
then for EACH t satisfying 2Ht/N<=delta/2 and 1/H<=delta^2/8, some 0<d<H has
 |phase(z)^(d*t)-1|<=32/(delta^2*N).
This produces near-integer bounded multiples at every short dilate, not just
one short shift. The proof uses shifted averages, pair energy, and the exact
geometric-sequence formula for a first-degree difference.
Compiles, olean built; permitted axioms only.

### 245. `Submission/MultipleLinearOrbitInverse.lean`
A bounded-multiple form of242. If every t<N/D has some 0<d<H such that
 |alpha*d*t-b|<=E/N, and N>=8(2DH)(6E+1), then some 0<q<8DH^2 satisfies
 |alpha*q-b|<=256D^2 H^2 E(6E+1)/N^2.
Select d on a large fiber, whose density is at least 1/(2DH), then apply242
to slope d*alpha. No injectivity of the original multiple-selection map is
assumed. Compiles, olean built; permitted axioms only.

### 246. `Submission/SharpQuadraticWeylInverse.lean`
An unconditional inverse-square quadratic leading-phase estimate:
 diffIter(2,f)=z, mean(|phase f|)>=2^-s in the sense
 2^-s <= norm(intervalMean(N,phase o f)), N>=2^(14s+42)
imply some 0<q<=2^(14s+42) with
 |phase(z)^q-1|<=2^(14s+42)/N^2.
Uses244 with H=2^(2s+4), D=2^(3s+6), then243 and245 with E=H.
All constants and casts have been checked explicitly.
This improves the N^-1 scale of the earlier general leading-phase inverse
in the quadratic case. It does NOT assert an inverse theorem for arbitrary
functions, nor an improved dimension dependence for simultaneous recurrence.
Compiles, olean built; permitted axioms only.

Checkpoint after246: The sharp scalar quadratic Weyl estimate is COMPLETE.
The all-length summable extremal-density bound remains missing. In particular,
none of241--246 proves the original target or its negation, and no new
four-term reciprocal-summability result has been asserted. Spec.lean remains
unchanged with its original sorry. The original task remains UNSOLVED.
No proof/disproof has been submitted.

### 247. `Submission/FineMultipleOrbitCompression.lean`
Fine-error bootstrap of245. First obtain the coarse N^-2 approximation. For a
long enough short dilate t, the determinant of the coarse approximation and
the near-integer bounded multiple at t has absolute value <=1/4, hence is zero.
The exact identity retains the finer input error epsilon and gives
 |alpha*q-b|<=32D^2 H^2 epsilon/N, 0<q<8DH^2,
under explicit polynomial lower bounds on N. Thus one gains a length factor
without discarding a previously obtained N^-k scale.
Compiles, olean built; permitted axioms only.

### 248. `Submission/DyadicFineOrbitInverse.lean`
Dyadic circle form of247. For a unit complex v, k>=1, and
 N>=2^(13+2d+3h+2e),
if every t<N/2^d has 0<a<2^h with |v^(a*t)-1|<=2^e/N^k, then some
 0<q<2^(3+d+2h)
has |v^q-1|<=2^(8+2d+2h+e)/N^(k+1).
Compiles, olean built; permitted axioms only.

### 249. `Submission/SharpHigherPhaseWeylInverse.lean`
The natural-scale leading-coefficient estimate is now proved in ALL positive
degrees. Define C(0)=2, C(k+1)=30C(k)+50. If
 diffIter(k+1,f)=z, 2^-s<=norm(intervalMean(N,phase o f)),
 N>=2^(C(k)*(s+1)),
then some 0<q<=2^(C(k)*(s+1)) has
 |phase(z)^q-1|<=2^(C(k)*(s+1))/N^(k+1).
The induction uses dilated differencing at each t, the previous degree's sharp
estimate, and248. Also proves the dyadic dilated-shift extraction lemma.
This is a Weyl inverse for an ALREADY polynomial phase, not a higher Gowers
inverse theorem for an arbitrary function.
Compiles, olean built; permitted axioms only.

### 250. `Submission/FiniteFiberEnergy.lean`
A finite map phi:I->J has collision probability at least 1/|J|. Consequently,
for unit functions constant on phi-fibers, small off-fiber correlations force
pair energy >=1/|J|-eta. Energy <=1/(2|J|) therefore gives a correlation
>1/(4|J|) between distinct fibers. The diagonal mass uses the number of fibers,
not the much larger original sample space.
Compiles, olean built; permitted axioms only.

### 251. `Submission/TensorFejerKernel.lean`
Finite tensor Fejer kernels for m phases, raising each geometric average to
the mth power. The sample index is Fin m -> Fin m -> Fin K; the frequency
index records each coordinate's sum, all <mK. If one phase avoids epsilon and
 K*epsilon^2>=8m,
then squared norm of the kernel mean is <=1/(2(mK)^m). All expansions are
finite, using geometric sums and product-expectation factorization.
Technical note: the complex generic product-expectation lemma explicitly
accepts DecidableEq on the index type, avoiding the classical/canonical Fin
Fintype mismatch encountered earlier in the project.
Compiles, olean built; permitted axioms only.

### 252. `Submission/SimultaneousAvoidanceFrequency.lean`
If a tuple of m unit phases indexed by a nonempty finite X never enters the
epsilon-neighborhood of 1 in every coordinate, then (for K epsilon^2>=8m)
some nonzero integer vector h satisfies
 |h_j|<mK,
 norm(mean_x prod_j v(x,j)^h_j)>1/(4(mK)^m).
Uses250 with the coordinate-sum fibers of251. Frequencies are not assumed
positive; exact integer-power identities handle negative components.
Compiles, olean built; permitted axioms only.

### 253. `Submission/PhaseIntegerLinear.lean`
Exact integer linear combination identities for additive circle phases,
including phase(n*z)=phase(z)^n for signed n, finite sums, and commutation
between integer frequencies and natural powers.
Compiles, olean built; permitted axioms only.

### 254. `Submission/PolynomialRecurrenceObstruction.lean`
Failure of simultaneous monomial recurrence gives a bounded nonzero integer
relation at the NATURAL inverse-degree error scale. Let
 s=m*(2t+2m+3)+2, B=C(k)*(s+1),
and suppose no n in [1,N] simultaneously returns all degree-(k+1) monomial
phases within 2^-t, with N>=2^B. Then some nonzero integer vector h satisfies
 |h_j|<=2^(B+(k+1)!+2t+2m+3),
 |phase(sum_j h_j*z_j)-1|<=2^B/N^(k+1).
The tensor cutoff is K=m*2^(2t+3). Apply252, then249 to the integer linear
combination polynomial; absorb the factorial and denominator into h.
At fixed degree, logarithms of the coefficient and error-numerator bounds
are O_k(m*t+m^2). This is a relation certificate, NOT a completed efficient
lattice dimension-reduction recurrence theorem.
Compiles, olean built; permitted axioms only.

Checkpoint after254: Natural-scale Weyl inversion is complete for every
degree, and simultaneous recurrence failure now has a quantitative small
integer-relation certificate. A recurrence bound with polynomial rather than
exponential dependence of its accuracy exponent on dimension still requires
a volume-controlled lattice reduction; naive coordinate elimination loses
accuracy too quickly. This has NOT been assumed or asserted.
More importantly, none of these results supplies the missing all-length
small-positive-uniformity inverse/density estimate or the summable extremal
series needed by Erdős3. Spec.lean remains unchanged with its original sorry.
The original task is UNSOLVED. No proof or disproof has been submitted.

### 255. `Submission/AnisotropicFejerKernel.lean`
Anisotropic finite kernels with independent power r and coordinate cutoffs K_i.
If every phase tuple avoids some epsilon_i, all K_i*epsilon_i>=4, and
 2*prod_i(r*K_i)<=4^r,
then a nonzero integer frequency has |h_i|<r*K_i and mean >1/(4*prod_i(r*K_i)).
Compiles, olean built; permitted axioms only.

### 256. `Submission/AnisotropicAvoidanceParameters.lean`
For dyadic precisions t_i, let L=m+sum(t_i)+1, r=16L^2, K_i=2^(t_i+2).
Proves the kernel volume condition and the frequency mean lower bound 2^-s,
where s=sum(t_i)+6m+2Lm+2. Thus the coordinate frequency cutoff is LINEAR in
inverse coordinate accuracy, times a polynomial in total precision.
Compiles, olean built; permitted axioms only.

### 257. `Submission/AnisotropicPolynomialObstruction.lean`
Combines256 and249. Failure of degree-(k+1) monomial recurrence yields a short
nonzero integer vector h, |h_i|<r*2^(t_i+2), and a SEPARATE denominator q with
 0<q<=2^(C(k)*(s+1)+(k+1)!),
 |phase(q*sum h_i*z_i)-1|<=2^(C(k)*(s+1))/N^(k+1).
Also gives real-coordinate form with an exact integer correction.
This separation is essential: absorbing q into h would spoil geometric
volume control. Compiles, olean built; permitted axioms only.

### 258. `Submission/LatticePhaseCoordinates.lean`
For a finite real basis b, defines continuous coordinate functionals and the
integer dual frequency sum_i h_i*coordinate_i. Proves nonvanishing,
integrality on span_Z(b), and its operator-norm bound.
Small coordinate phase chords imply an actual nearby lattice point, with
error <=sum_i epsilon_i*norm(b_i)/4.
Compiles, olean built; permitted axioms only.

### 259. `Submission/LatticeRecurrenceObstruction.lean`
Failure of recurrence near span_Z(b) gives a nonzero integral dual functional
F, with operator norm <=r*sum_i 2^(t_i+2)*norm(coordinate_i), and a separate
rational denominator and inverse-degree approximation error.
Also proves the bound <=4r*m*A*D under the EXPLICIT hypotheses
 2^t_i<=A*norm(b_i), norm(b_i)*norm(coordinate_i)<=D.
No well-conditioned basis is assumed without stating it.
Compiles, olean built; permitted axioms only.

### 260. `Submission/PrimitiveIntegerFrequency.lean`
Primitive normalization of a nonzero finite integer vector h. Produces a
positive g, h0, and Bezout coefficients c with
 h_i=g*h0_i, sum c_i*h0_i=1,
 |h0_i|<=|h_i| and g<=natAbs(h_i) for each nonzero coordinate.
Uses the principal ideal generated by h. Compiles, olean built; permitted axioms only.

### 261. `Submission/PrimitiveLatticeFunctional.lean`
Normalizes an integral nonzero lattice functional F=g*F0. The primitive F0
has norm <=norm(F) and takes value1 on an actual lattice vector v. The common
divisor g is bounded by some |F(b_i)|. Integrality of F0 is proved, not inferred
from dividing circle errors. Compiles, olean built; permitted axioms only.

### 262. `Submission/KernelProjectionEstimates.lean`
Explicit projection x -> x-F(x)*u when F(u)=1. For Hilbert spaces, the Riesz
normal u=Riesz(F)/norm(F)^2 has F(u)=1 and norm(u)=1/norm(F), giving exact
projection error |F(x)|/norm(F). Compiles, olean built; permitted axioms only.

### 263. `Submission/KernelMonomialLift.lean`
Exact lifting from the primitive kernel. If |qF(alpha)-c|<=epsilon, adjust
 beta=q^(k+1)*alpha-q^k*c*v, F(v)=1,
and project beta into ker(F). A degree-(k+1) near return there at n lifts to a
return of alpha at q*n, with additional error
 n^(k+1)*q^k*epsilon/norm(F).
Every integer correction is proved to remain in the original lattice.
Compiles, olean built; permitted axioms only.

### 264. `Submission/LinearScaleKernelLift.lean`
Proves the linear interval-loss budget: if q*M*S<=N and
 A<=rho*norm(F)*S^(k+1),
then an approximation error A/N^(k+1) contributes at most rho when lifting
any return n<=M. The lifted time is positive and <=N. No root-scale shortening
is used. Compiles, olean built; permitted axioms only.

### 265. `Submission/PrimitiveKernelLattice.lean`
The integer lattice intersected with the kernel of a primitive integral
functional is a genuine full lattice in that kernel: discreteness and full
real span are proved. Its real dimension is exactly one less than the original.
The integral projection along a lattice vector v with F(v)=1 proves spanning.
Compiles, olean built; permitted axioms only.

### 266. `Submission/PrimitiveLatticeSplitting.lean`
Constructs the integer linear equivalence
 Z x (L intersect ker F) ~= L, (c,w) -> c*v+w,
and an adapted integer basis. Used for exact determinant comparisons.
The one-point index type is explicitly Unit (not universe-polymorphic PUnit).
Compiles, olean built; permitted axioms only.

### 267. `Submission/NormalOrthonormalBasis.lean`
Constructs an orthonormal basis of E from the normalized Riesz normal of F
and any orthonormal basis of ker(F). All orthogonality and spanning claims
are proved. The normal-coordinate formula is F(x)/norm(F).
Compiles, olean built; permitted axioms only.

### 268. `Submission/PrimitiveKernelCovolume.lean`
The EXACT primitive-kernel covolume identity:
 covolume(L intersect ker F)=norm(F)*covolume(L).
Uses266's adapted integer basis,267's adapted orthonormal basis, and a block
triangular determinant. The separate rational denominator does not occur in
the geometric cost. Both basis-indexed and basis-independent versions proved.
Compiles, olean built; permitted axioms only.

Checkpoint after268: The local arithmetic, kernel lattice, linear-scale lift,
and exact covolume steps for an efficient recurrence proof are complete. A
reduced-basis construction with dimension-only conditioning/product bounds
is still needed to iterate these steps with polynomial dimension cost.
Even that recurrence result would NOT by itself supply the missing all-length
summable extremal-density estimate. Spec.lean is unchanged with its original
sorry. The Erdős3 task remains UNSOLVED; no proof/disproof has been submitted.

### 269. `Submission/ShortestLatticeVector.lean`
A shortest nonzero vector exists in every nonzero discrete lattice in a proper
normed space. In a full finite-dimensional lattice it is primitive: an integral
dual functional takes value one on it. The proof uses finite-ball minimization,
integer coordinate gcd normalization, and Bezout. Compiles, olean built;
permitted axioms only.

### 270. `Submission/KernelShearLattice.lean`
For F(v)=G(v)=1, projection along v is an explicit continuous linear equivalence
between ker F and ker G. Transporting the primitive kernel lattice along this
equivalence gives a full discrete lattice equal to the projection of the original
lattice, even when G is not integral. Its basis is given explicitly by projected
kernel basis vectors. Compiles, olean built; permitted axioms only.

Checkpoint after270: The conjecture remains UNSOLVED. The new geometry supports
a possible efficient recurrence argument; it does not give the all-length
summability estimate. Spec.lean retains its original sorry.

### 271. `Submission/OrthogonalProjectionCovolume.lean`
Proves the covolume formula for orthogonal projection along a primitive lattice
vector v. The integral splitting functional F and geometric functional G are
kept separate throughout. A block triangular determinant, with bottom-left zero,
gives covolume(projected L)=norm(G)*covolume(L). For
 G(x)=inner(v,x)/norm(v)^2,
this is covolume(projected L)=covolume(L)/norm(v). The proof does not assume G
integral. Includes basis-indexed and basis-independent forms, the geometric
functional's norm, and its orthogonality property. Compiles, olean built;
primitive_vector_projection_covolume depends only on propext, Classical.choice,
and Quot.sound.

Checkpoint after271: The next proposed reduced-basis construction has its exact
projection-covolume ingredient. The reduced-basis product bound itself is not yet
proved. More importantly, the all-length summable extremal-density estimate is
still absent; completing lattice recurrence would not supply that missing step.
Spec.lean is unchanged and still contains its original sorry. No complete proof
or disproof exists in this development, and no proof has been submitted.

### 272. `Submission/RoundedLatticeLift.lean`
For G(v)=1, rounding x by round(G(x))*v preserves its projection and costs at
most norm(v)/2. If v is shortest and the projection is nonzero, the rounded
lift has norm at most twice the projected norm. This uses only the triangle
inequality and shortest-vector minimality, not a squared-norm argument.
Compiles, olean built; permitted axioms only.

### 273. `Submission/ShortLiftLatticeBasis.lean`
An explicit integer upper-triangular shear preserves a lattice basis. Any basis
of the projected lattice pulls back to the primitive kernel, then lifts to an
integer basis with first vector v and other vectors rounded modulo v. When v
is shortest, each lifted vector has norm <=2 times the corresponding projected
basis norm. Hence the basis-product lifting cost is <=norm(v)*2^dimension.
Compiles, olean built; permitted axioms only.

### 274. `Submission/ReducedLatticeBasis.lean`
Every full lattice L in a finite-dimensional real inner-product space has an
integer basis b indexed by Fin(d), d=finrank(E), satisfying
 prod_i norm(b_i) <= 2^(d^2)*covolume(L).
Proof by induction on dimension: choose a shortest primitive vector, project
orthogonally, apply induction to the full projected lattice, lift its basis
using273, and cancel norm(v) with the exact covolume quotient from271.
The zero-dimensional case is included. This is a proved dimension-only
orthogonality-defect bound, not an assumption. Compiles, olean built; permitted
axioms only. The next geometric step is to derive dual coordinate conditioning.
The original conjecture remains UNSOLVED and Spec.lean remains unchanged.

### 275. `Submission/ConditionedLatticeBasis.lean`
Derives dual coordinate conditioning from the product/covolume bound. Replacing
basis vector i by the normalized Riesz representative of its coordinate
functional gives a determinant identity. Hadamard's inequality then proves
 norm(b_i)*norm(coordinate_i)*covolume(L) <= prod_j norm(b_j).
Consequently a full Euclidean lattice has a real basis spanning exactly L over
Z with BOTH product defect <=2^(d^2) and coordinate conditioning <=2^(d^2).
Compiles, olean built; permitted axioms only.

### 276. `Submission/LatticePrecisionBudget.lean`
Chooses dyadic coordinate precisions t_i from individual basis lengths. If every
length is >=1 and their product is <=2^W, then
 precisionMass(t) <= m*(s+m+2)+W+1,
 2^t_i <=2^(s+m+1)*norm(b_i),
 sum_i 2^-t_i*norm(b_i) <=2^-s.
Together with275, W can be taken as m^2+V when covolume(L)<=2^V. Also bounds the
avoidance mean exponent by (2m+9)*precisionMass. Compiles, olean built; permitted
axioms only. The original conjecture remains UNSOLVED.

### 277. `Submission/LatticeCoordinateBounds.lean`
If basis lengths are all >=1, each length is bounded by their product. A nonzero
integral dual functional has norm >=2^-U when the product is <=2^U: some integral
basis value is nonzero and hence has absolute value >=1. Compiles, olean built;
permitted axioms only.

### 278. `Submission/PrimitiveHeightObstruction.lean`
Combines the conditioned basis, total dyadic precision budget, sharp Weyl
obstruction, and primitive normalization. For dimension m, accuracy2^-s,
covolume<=2^V and lattice minimum>=1, let
 P=m*(s+m+2)+(m^2+V)+1,
 T=s+m^2+2m+7,
 W=sharpWeylConstant(k)*(2m+9)*P.
Avoidance through N>=2^W gives a primitive integral nonzero F with
 2^-(m^2+V)<=norm(F)<=2^T*P^2,
 F(v)=1 at a lattice vector,
 0<q<=2^(W+(k+1)!+T+m^2+V)*P^2,
 |q*F(alpha)-c|<=2^W/N^(k+1).
The norm cost is polynomial in logarithmic covolume; the larger denominator is
separate. Compiles, olean built; permitted axioms only.

### 279. `Submission/LatticeHeightDescent.lean`
Uniform height bookkeeping with fixed H>=16, D<=H, m<=D,
 dualHeight(m,s)<=H, V<=(3*(D-m)+1)*H.
Proves P<=(4D+2)H<=2^H, so norm(F)<=2^(3H). Covolume exponent rises by at most
3H at each descent, without repeatedly exponentiating the initial height.
Defines
 baseWeylCost(k,D)=sharpWeylConstant(k)*(2D+9)*(4D+2),
 stepHeight(k,D,H)=(2*baseWeylCost(k,D)+6D+10)*H+(k+1)!.
Proves all combined stride, denominator, and inverse-degree lifting budgets.
Compiles, olean built; permitted axioms only.

### 280. `Submission/PolynomialDimensionLatticeRecurrence.lean`
COMPLETES polynomial-dimension monomial lattice recurrence. For every full
Euclidean lattice L with minimum nonzero length>=1 and covolume<=2^V, every
alpha, k,s admits 0<n<=2^(d*stepHeight(k,d,H)) and y in L with
 norm(n^(k+1)*alpha-y)<=2^-s,
where d=dimension and H=d^2+2d+s+V+32. Includes dimension zero.
Proof descends through primitive kernels, applies the uniform height controls
from279, and lifts at a linear interval scale using264. The exponent is
polynomial in dimension and linear in s,V. Compiles, olean built; permitted
axioms only.

Checkpoint after280: The efficient lattice recurrence branch is now complete.
A useful next corollary is simultaneous circle/real monomial recurrence via
the standard integer lattice. The original conjecture is still UNSOLVED:
small-positive-uniformity structure for all lengths and a summable all-length
extremal-density estimate remain absent. Spec.lean remains unchanged with its
original sorry. No complete proof or disproof has been submitted.

### 281. `Submission/PolynomialDimensionTorusRecurrence.lean`
An orthonormal integer-span lattice has minimum nonzero length>=1 and covolume1.
Applying280 gives simultaneous real monomial approximation by integers. The
unit-angle conversion then gives, for an m-tuple of unit phases and degree k+1,
 0<n<=2^(tupleRecurrenceConstant(k,m)*(s+1)),
 norm(v_i^(n^(k+1))-1)<=2^-s for every i,
where tupleRecurrenceConstant is explicitly polynomial of degree5 in m.
Compiles, olean built; permitted axioms only.

### 282. `Submission/PolynomialDimensionMixedRecurrence.lean`
Simultaneous recurrence in every positive degree<=K for every coordinate.
Induction is on degree, not tuple length: previously controlled degrees survive
a suitably small-error dilation, while281 handles the next degree for the whole
tuple at once. Gives both all-degrees and mixed-degrees versions with an explicit
recurrence constant. Compiles, olean built; permitted axioms only.

### 283. `Submission/MixedRecurrencePolynomialBound.lean`
Explicit polynomial-in-dimension bounds:
 tupleRecurrenceConstant(k,m)<=degreeCoefficient(k)*(m+1)^5,
 degreeCoefficient(k)=2592*sharpWeylConstant(k)+360+(k+1)!;
 mixedTupleConstant(K,m)<=mixedDegreeCoefficient(K)*(m+1)^(5K),
where mixedDegreeCoefficient is an explicit degree-only recursion.
Final theorem polynomial_dimension_mixed_recurrence gives a common positive
return d<=2^(mixedDegreeCoefficient(K)*(m+1)^(5K)*(s+1)) for arbitrary m-tuples of
unit phases with positive assigned degrees<=K, with every chord error<=2^-s.
Compiles, olean built; permitted axioms only.

Checkpoint after283: Efficient simultaneous recurrence is now available for all
fixed positive degrees, with a polynomial-dimensional exponent. This removes
the earlier exponential-in-tuple-length recurrence bottleneck. It does NOT
supply an arbitrary-function higher-order inverse theorem, nor an all-length
extremal-density estimate whose geometric-scale series is summable. The original
Erdos3 conjecture remains UNSOLVED. Spec.lean still contains its original sorry,
its statement and imports are untouched, and no complete proof/disproof has
been submitted.

### Conjecture-focused reassessment after283
Reviewed PolynomialIncrementParameters, IntegerFourDensityIncrement,
IntegerFourDensityBound, PolynomialFourDensityBound, DyadicFourDensityBound,
and the exact summability reduction. The available four-term increment has
only a fixed-power-in-density gain, so iteration retains an inverse-log-log
barrier. Efficient simultaneous recurrence does not by itself turn that bound
into a summable geometric-scale density estimate. In the existing conditional
single-phase progression partition, the recurrence tuple count is already one;
the improved general tuple dependence must not be claimed to close this gap.
The precise sufficient all-length finite harmonic bound remains unproved.
No new proof or counterexample to the original conjecture was obtained in this
reassessment. Spec.lean is unchanged; no submission is warranted.

### 284. `Submission/ParameterizedPartitionCosts.lean`
Separates the progression-partition induction from its recurrence input. For
any monomial recurrence exponent C(k), defines flatThreshold, flatStride and
flatExponent, and proves
 flatStride(C,k,L,s)<=flatThreshold(C,k,L,s) for L>0,
 flatThreshold(C,k,L,s)<=2^(flatExponent(C,k)*(s+k+1+clog_2 L)).
The exponent recursion is
 E(0)=1, E(k+1)=E(k)*((k+1)*C(k)+1)+C(k)+1.
Compiles, olean built; permitted axioms only.

### 285. `Submission/ParameterizedProgressionPartition.lean`
The arbitrary-degree density-preserving partition proof now accepts an explicit
simultaneous monomial recurrence hypothesis with exponent C(k). Every good cell
is exactly a proper length-L progression; the exceptional proportion and all
phase oscillations are <=2^-s. The threshold and stride use284. This retains all
boundary, refinement, and exact-fiber checks. Compiles, olean built; permitted
axioms only. No inverse theorem producing these phases is assumed.

### 286. `Submission/EfficientPolynomialPartition.lean`
Instantiates285 with the proved polynomial-dimensional monomial recurrence from
281. Proves the explicit threshold and stride upper bound
 2^(partitionCoefficient(k)*(m+1)^(5k)*(s+k+1+clog_2 L)),
where partitionCoefficient is an explicit degree-only recursion. All but2^-s of
the interval is partitioned into exact proper length-L progressions on which
every one of m degree-k phases oscillates by at most2^-s.
Compiles, olean built; permitted axioms only.

### 287. `Submission/EfficientLocalPolynomialPartition.lean`
Finite-window and local-cube versions of286. The finite-window Newton extension
is proved equal to the supplied phases only at the points used in the partition;
no global polynomiality is assumed without proof. Compiles, olean built;
permitted axioms only.

### 288. `Submission/EfficientBohrPolynomialPartition.lean`
Extends the efficient partition to retained progression fibers and stable Bohr
sets. All terminal-block and boundary exceptional mass, integer stride bounds,
and exact good-cell progression geometry are retained. Compiles, olean built;
permitted axioms only. This is still a theorem about supplied polynomial phases,
not an arbitrary-function higher-order inverse theorem or a settlement.

### 289. `Submission/PolynomialFactorCorrelationIncrement.lean`
Generalizes the local correlation-to-progression increment from a single circle
phase to a bounded Lipschitz function Phi of a finite tuple of local polynomial
phases. Coordinatewise partition errors <=2^-s give factor error <=Lip(Phi)*2^-s
in the sup norm. The averaged partial-partition theorem applies to bounded,
not necessarily unit-valued, tests. All exceptional mass and exact progression
geometry are retained. Produces a proper length-L AP with mean increment r/16.
Compiles, olean built; permitted axioms only. The factor and its averaged
correlation are explicit hypotheses; no higher-order inverse theorem is claimed.

### 290. `Submission/PolynomialFactorIncrementParameters.lean`
Non-circular parameters for289. Accuracy is chosen by rounding 64*(Lip(Phi)+2)/r,
so phase-composition and partition losses fit the correlation budget. Mesh and
terminal costs are explicit, and the final modulus threshold is polynomial in
requested length with degree
 partitionCoefficient(k)*(m+1)^(5k)*(2D+1),
where m is phase count and D is Bohr rank. The theorem
polynomial_factor_increment_explicit has all geometric and error hypotheses
supplied by these parameters. Compiles, olean built; permitted axioms only.

Checkpoint after290: Polynomial-dimensional recurrence is now connected to
finite-window/local/Bohr polynomial partitions and a general Lipschitz-factor
correlation-to-progression density increment. This remains conditional on the
existence of the supplied factor and its correlation. The missing small-positive-
uniformity structure and all-length summability estimate remain unproved.
Spec.lean is unchanged with its original sorry; the conjecture is UNSOLVED and
there is no complete proof or disproof to submit.

### 291. `Submission/QuadraticModelCounting.lean`
Proves that the balanced four-variable relation count
 E[x,y,z] f(x)f(y)f(z)f(x-T(y)+T(z))
is a squared shifted-convolution average, hence at least (E f)^4.
No positivity of f or linearity of T is needed. A triangular bijection identifies
the pure quadratic Newton-coefficient model with T(y)=3y, giving the same bound.
Compiles, olean built; permitted axioms only. This is a model counting theorem,
not a structural/equidistribution theorem for arbitrary sets. The target is
still unproved; Spec.lean is unchanged.

### 292. `Submission/FourierMultilinearTransfer.lean`
Exact Fourier expansion of arbitrary finite multilinear averages. If all
product-character tests of two distributions differ by at most epsilon, their
products-of-functions averages differ by at most epsilon times the product of
the Fourier l1 masses. Includes real-valued transfer and Parseval/Cauchy bounds
mass(f)^2 <= |G| E|f|^2, and mass(f)^4 <= |G|^2 for |f|<=1.
Compiles, olean built; permitted axioms only. Equidistribution is a hypothesis.

### 293. `Submission/QuadraticModelTransfer.lean`
Under the exact relation d=a-3b+3c, product-character discrepancy for four values
reduces to joint character discrepancy for the first three values. Transfers
291 to give E f(a)f(b)f(c)f(d) >= (E_G f)^4 - epsilon*mass(f)^4, or the coarser
error epsilon*|G|^2 for |f|<=1. Compiles, olean built; permitted axioms only.
The joint distribution hypothesis is explicit and has not been proved for
arbitrary sets or factors. The original conjecture remains unsolved.

### 294. `Submission/BinaryQuadraticGauss.lean`
For primitive complex characters on finite fields of odd characteristic, proves
exact inverse-field-size squared norm for a quadratic polynomial with nonzero
leading coefficient, even with arbitrary lower terms. Averaging and a shear
then give square-root cancellation for every nonzero binary quadratic form.
Also proves every character is a multiplicative shift of a fixed primitive one.
Compiles, olean built; permitted axioms only.

### 295. `Submission/QuadraticSquareDiscrepancy.lean`
Verifies293's discrepancy hypothesis for squareSample(n,j,v)=sum_i(x_i+j*d_i)^2.
Tensorization yields discrepancy <= sqrt(1/|F|)^n for all triple character tests.
Consequently every unit-bounded real f has four-point average at least
 (E_F f)^4 - sqrt(1/|F|)^n*|F|^2.
This is unconditional for the specified structured class. It does not assert
that arbitrary subsets admit such a representation or finite-field model.
Compiles, olean built; permitted axioms only. Spec.lean remains unchanged.

### 296. `Submission/QuadraticFactorCounting.lean`
Combines293 with the previously proved generalized von Neumann counting bound.
A [0,1]-valued factor Phi(q(x)) with small U3 error relative to 1_A, the exact
four-point quadratic relation, and triple-character discrepancy epsilon gives
an actual nontrivial four-point configuration whenever
 (E_G Phi)^4 > epsilon*|G|^2 + 4*eta + density(A)/|F|.
Accounts for the exact diagonal contribution rather than merely proving a
positive total count. Compiles, olean built; permitted axioms only. Factor
existence, the small error, and discrepancy remain explicit hypotheses.

### 297. `Submission/LinearQuadraticDiscrepancyBarrier.lean`
For every nontrivial finite-field character chi, the triple character test
 (chi, chi^(-2), chi)
has average1 on (x,x+d,x+2d), and average0 on independent coordinates. Thus a
linear factor has pure-quadratic model discrepancy exactly1 and cannot satisfy
a discrepancy bound epsilon<1. This is a model-hypothesis obstruction, not a
counterexample to the target. Compiles, olean built; permitted axioms only.

Checkpoint after297: Completed the Fourier transfer and verified its hypothesis
for independent sums of squares, then connected it to a genuine four-term
configuration criterion. The criterion still assumes an appropriate structured
factor, small uniformity error, and joint equidistribution. Linear factors show
that the last condition cannot be inferred merely from polynomiality. There is
still no summable all-length extremal bound or complete proof/disproof.
Submission/Spec.lean is unchanged with its original sorry; no valid settlement
has been submitted.

### 298. `Submission/PairedEvenModelCounting.lean`
General mixed-convolution energy identity for a function f on G, a function g
on any finite Y, and any map T:Y->G. Taking g to be a product of m independent
copies of f gives a paired (2m+2)-value model with average at least (E f)^(2m+2).
Includes exact indexed paired values and character-discrepancy transfer.
Compiles, olean built; permitted axioms only.

### 299. `Submission/EvenDifferencePairing.lean`
For odd n, the alternating binomial coefficients satisfy c(n-i)=-c(i).
Splits the odd-order finite-difference equation into opposite pairs and solves
it for the final value. Includes the converse, so the paired equation is
exactly equivalent to vanishing of the single top difference on that window.
Compiles, olean built; permitted axioms only.

### 300. `Submission/EvenPolynomialModel.lean`
An explicit bijection indexes the paired model in progression order. Its values
have an exact Newton extension of degree <=2m, with vanishing (2m+1)st difference.
Proves for every real f on a finite abelian group that the average product of
its values at the resulting (2m+2) polynomial samples is >=(E f)^(2m+2).
The model has 2m+1 independent free group coordinates. Compiles, olean built;
permitted axioms only. This is not a structural theorem for arbitrary sets.

### 301. `Submission/EvenPolynomialCoordinates.lean`
The model is additive in its free coordinates. Every finite window with zero
top difference reconstructs exactly from its 2m+1 free values. Conversely the
coordinates of a model polynomial recover its parameter. Products of characters
of all model values are single additive characters of the free coordinate group.
Compiles, olean built; permitted axioms only.

### 302. `Submission/EvenPolynomialModelTransfer.lean`
For supplied polynomial windows, character discrepancy epsilon of their free
coordinate distribution transfers300 with error epsilon*mass(f)^(2m+2).
For |f|<=1 the error is at most epsilon*|G|^(m+1).
Compiles, olean built; permitted axioms only. Discrepancy remains explicit; it
does not follow from polynomiality alone, as297 already shows for linear factors.

### 303. `Submission/EvenPolynomialFactorCounting.lean`
All-even analogue of296: combines302's model lower bound with the generalized
von Neumann counting bound for 2m+2 distinct field slopes. The result produces
an actual AP with nonzero common difference under explicit polynomiality,
free-coordinate discrepancy, and small uniformity-error assumptions, when
 (E_G Phi)^(2m+2) > epsilon*|G|^(m+1)+(2m+2)*eta+density(A)/|F|.
The exact diagonal contribution is accounted for. Compiles, olean built;
permitted axioms only.

Checkpoint after303: Model positivity, coordinate reconstruction, discrepancy
transfer, and a conditional nontrivial-AP criterion now hold at every even
length. They do not supply the required structured approximation for arbitrary
sets. Lower-degree factors need not satisfy the pure-top-degree discrepancy
hypothesis, and no general higher-order inverse or summable all-length extremal
bound has been obtained. The precise series sum_j r_k(4^j)/4^j is still unproved
summable for general k (even k=4 remains unresolved here). Spec.lean is unchanged
with its original sorry; no complete proof/disproof has been submitted.

### 304. `Submission/AnchoredModelCounting.lean`
A nonnegative even-length model whose zero coefficient slice is constant has
count >= (E f)^k/|C|, where C is its coefficient space. Uses only the exact mass
of that slice and Jensen. Includes Fourier character-discrepancy transfer with
its explicit Fourier-mass error. Compiles, olean built; permitted axioms only.

### 305. `Submission/GradedPolynomialModel.lean`
Allows a family of finite abelian coordinate groups with independently assigned
degrees d_i, rather than only a pure top degree. Gives exact Newton polynomial
samples, proves the prescribed componentwise finite-difference vanishing, and
establishes count >= (E f)^k / prod_i |G_i|^(d_i) for nonnegative f and even k.
If every group has cardinality p, the denominator is exactly p^(sum_i d_i).
Compiles, olean built; permitted axioms only. This makes the mixed-degree
complexity loss explicit, but does not establish a structural approximation for
arbitrary sets or a summable all-length density bound.

### 306. `Submission/TopDegreeFiberCounting.lean`
Improves305 by not freezing the highest even-degree component. Conditional on
the lower base coordinate, applies300's paired polynomial count to the top
component, then Jensen across lower base points. Only the lower coefficient
space contributes to the denominator. For graded lower groups and arbitrary
finite top group Q, the bound is
 (E f)^(2m+2) / prod_lower_i |G_i|^(d_i),
independent of Q's cardinality or rank. Compiles, olean built; permitted axioms
only. The model still needs an approximation/equidistribution theorem before
it can be applied to arbitrary sets.

Checkpoint after306: Mixed-degree models are now allowed, with exact complexity
loss, and the highest even-degree rank has been removed from that loss. The
lower-degree coefficient complexity and structural approximation remain
uncontrolled at the strength needed for reciprocal summability. These model
bounds do not close the original all-length conjecture. Spec.lean remains
unchanged with sorry, and no complete proof or disproof has been submitted.

### 307. `Submission/RobustTopDegreeCounting.lean`
If the lower factor changes by at most tau on every position for coefficients
in S, its mixed model count is >= density(S)*(delta^k-k*tau), k even. Uses an
explicit product perturbation bound and the top-degree paired model. The whole
set S of approximate returns replaces the single zero coefficient slice.
Compiles, olean built; permitted axioms only.

### 308. `Submission/BohrTopDegreeCounting.lean`
For lower samples a+L_j(c), a character-coordinate Lipschitz factor is almost
constant when c lies in a Bohr set of the pulled-back characters chi_i o L_j.
There are at most r*k such frequencies. The elementary Bohr-volume estimate
then gives an explicit model count independent of the sizes of H, C, and Q.
An explicit return mesh q=ceil(4*k*A/delta^k)+1 fits the product-error budget.
Compiles, olean built; permitted axioms only.

### 309. `Submission/BohrCountingPowerBound.lean`
Eliminates the rounded return mesh from308's bound. For k=2m+2, lower character
rank r and coordinate Lipschitz constant A, positive-mean unit-bounded f has
mixed model count at least
 delta^(k*(2*r*k+1)) / (2*(8*k*A+5)^(2*r*k)).
All group cardinalities and top-degree rank are absent from this bound.
Compiles, olean built; permitted axioms only. The result still depends on lower
rank/Lipschitz complexity and applies to the specified model, not arbitrary sets.

Checkpoint after309: Robust approximate returns remove the full coefficient-
cardinality loss and give an explicit rank/Lipschitz counting bound. There is
still no appropriate structural approximation and equidistribution theorem for
arbitrary reciprocal-divergent sets, nor a summable all-length extremal estimate.
Spec.lean remains unchanged with its original sorry. No complete proof or
disproof has been submitted.

### 310. `Submission/ClippedWeakRegularity.lean`
A bounded correlation detector yields a clipped weak-regularity decomposition.
Clipping to [0,1] cannot increase squared distance to a [0,1]-valued target. Each
test with pairing >=rho decreases mean squared error by at least rho^2. The
number of tests is bounded by ceil(mean(f)/rho^2)+1, retaining the density gain.
Proves all residuals stay unit bounded, so detector hypotheses remain valid.
Compiles, olean built; permitted axioms only.

### 311. `Submission/QuadraticAverageDetectors.lean`
Converts the normalized averaged local U3 inverse into a globally bounded real
test, without a Bohr-density loss. The test is the real part of the average over
y in B of b(x-y)*conj(q_(x-y)(y)). Taking b(a)=conj(localPairing(a)) gives exact
global real correlation equal to the averaged squared normalized local
correlation. Defines IsQuadraticAverageTest with explicit local quadratic,
rank, and bounded center-weight witnesses. Compiles, olean built; permitted
axioms only.

### 312. `Submission/WeakQuadraticRegularity.lean`
An unconditional weak U3 regularity theorem for every [0,1]-valued function on
finite abelian groups with bijective doubling. The approximant is a bounded
clipped combination of tests from311, and its residual uniformityPower2 is <=delta.
With update gain delta^1988534/correlationDenominator, test count is at most
 mean(f)*correlationDenominator^2*(1/delta)^3977068+2,
and every test has rank <=normalizedRank(delta). Compiles, olean built; permitted
axioms only. This constructs an approximation; it does not yet turn the averaged
local phases into an equidistributed factor satisfying the counting criteria.

Checkpoint after312: A genuine bounded weak U3 approximation is now proved,
using the existing inverse theorem rather than assuming factor existence.
The approximants are clipped combinations of local quadratic averages, not
single global polynomial-phase factors. Their conversion to suitable local
factors and joint distribution control remain unproved here, as does a general
higher-order inverse and a summable all-length extremal bound. Spec.lean still
contains the original sorry; no complete proof/disproof has been submitted.

### 313. `Submission/StableQuadraticRegularity.lean`
The weak U3 decomposition can use local quadratic averages on relatively stable
Bohr radii r in [1/64,1/32], for any preselected positive stability parameter z.
Increasing z does not worsen either the rank bound or the number of tests.
Phases remain quadratic on the larger Bohr set of radius 1/16. Compiles, olean
built; permitted axioms only. The approximation is still by averages of
center-dependent phases, not a single equidistributed polynomial factor.

### 314. `Submission/FixedCenterQuadraticAverage.lean`
A stable quadratic average, evaluated at a+t, differs from its fixed-center
average E_(y in B) b(a-y)*conj(q_(a-y)(y+t)) by at most 1/z throughout the
relative stability window. Proved via a complex weighted L1 translation bound.
Every shifted phase is locally quadratic on that window: r<=1/32 and width<=r/4
fit inside the original radius-1/16 quadraticity domain, without trimming y.
Compiles, olean built; permitted axioms only. This is a local representation
lemma, not a transfer of the global U3 residual to the small window.

### 315. `Submission/SampledQuadraticAverage.lean`
Normalized finite sampling gives mean squared error <=1/M on any nonempty
coordinate space. A stable quadratic average consequently has an M-phase local
factor approximation on any nonempty subset W of the relative stability window,
with mean squared error <=2/z^2+2/M. The M coordinate phases are unit-valued and
locally quadratic on W; coefficient norms are <=1. All errors are independent
of the cardinalities/densities of W and of the original Bohr set. Compiles,
olean built; permitted axioms only. This is an approximation of one test, not
a counting or equidistribution theorem for arbitrary sets.

### 316. `Submission/ClippedSumPerturbation.lean`
Clipped combinations satisfy a pointwise sum-of-input-errors bound. For L tests
with individual normalized mean squared errors <=epsilon, the output error is
<=rho^2*L^2*epsilon. If each test is A-Lipschitz, the clipped combination is
|rho|*L*A-Lipschitz. Compiles, olean built; permitted axioms only.

### 317. `Submission/CommonQuadraticWindow.lean`
For T stable quadratic tests, each of rank <=R and radius >=1/64, a common Bohr
window has rank <=T*R and width (1/64)/windowDenominator(R,z). It lies in every
test's relative stability window. Its relative size is at least
 (256*windowDenominator(R,z)+1)^(-2*T*R).
Compiles, olean built; permitted axioms only.

### 318. `Submission/SampledClippedFactor.lean`
A sampled phase coordinate is 1-Lipschitz in the supremum norm when its
coefficient norms are <=1. A clipped factor built from T such coordinates is
[0,1]-valued on its entire complex coordinate space and |rho|*T-Lipschitz,
independently of the number of samples per coordinate. Proves the exact
composition/evaluation identity. Compiles, olean built; permitted axioms only.

### 319. `Submission/LocalQuadraticRegularityFactor.lean`
Combines313--318. A list of T stable quadratic-average tests of rank <=R has,
on one common window of rank <=T*R and width (1/64)/windowDenominator(R,z), a
local representation at every base point by a bounded Lipschitz factor of T*M
unit locally quadratic phases. Lipschitz constant is |rho|*T; normalized mean
squared error is <=rho^2*T^2*(2/z^2+2/M). The common window has the cardinality
bound from317. The unconditional theorem weak_U3_local_factor additionally
constructs the bounded global approximant from the inverse theorem, retaining
the global U3 residual bound and the original explicit test-count bound.
Compiles, olean built; permitted axioms only.

Checkpoint after319: The previously planned localization/sampling step is now
complete, including the common window, clipping-error propagation, and bounded
Lipschitz factor representation. This is NOT a settlement. The global U3 error
has not been transferred without loss to that window; joint phase distribution
is not supplied by local quadraticity; and neither an all-degree small-positive-
uniformity inverse nor a summable all-length extremal bound has been proved.
Spec.lean is unchanged with its original sorry. No complete proof or disproof
has been submitted.

### 320. `Submission/StepWeightedCounting.lean`
Weighted generalized von Neumann and two-function counting bounds for every
system of at least three distinct slopes. A character of the common difference
is absorbed into two nondistinguished slope functions, preserving the residual
and its required uniformity order. An arbitrary complex step weight costs its
Fourier L1 mass: count error <=k*fourierMass(weight)*eta. No density-independent
localization claim is used. Compiles, olean built; permitted axioms only.

### 321. `Submission/DifferenceStepCounting.lean`
The normalized difference distribution of a nonempty finite B has Fourier L1
mass exactly 1/density(B), total mass one, and support B-B. For Bohr B of radius
r its support is inside radius2r. Proves the exact identity with independent
uniform b,c in B, and a localized counting comparison with error k*eta/density(B).
Compiles, olean built; permitted axioms only. This tracks rather than discards
the genuine density loss in passing from global uniformity to restricted steps.

### 322. `Submission/StableWindowCounting.lean`
On a relatively stable Bohr window, translating the normalized mean squared
error of two [0,1] functions costs at most1/z. If epsilon+1/z<=kappa^2, a local
configuration count with k small shifts changes by at most k*kappa. Averaging
the window base point exactly restores the global uniform base point, so the
same estimate holds with a different approximating factor at each base point.
No inverse-window-density loss. Compiles, olean built; permitted axioms only.

### Extension to319
The stronger stable_test_list_local_factor_on_subwindows was added. The common
window is chosen once, after which the same rank, phase-count, Lipschitz and
normalized L2 error bounds hold on ANY nonempty subset of it. The original
stable_test_list_local_factor and weak_U3_local_factor remain proved corollaries.
This avoids erroneously restricting a sampled approximation and paying the
inverse relative size of the new window. Compiles; permitted axioms only.

### 323. `Submission/StableLocalQuadraticFactor.lean`
The common factor window can itself be selected relatively stable at ANY extra
positive tolerance u, with radius between half the original common width and
the original width. No change to rank, phase count, Lipschitz constant or local
L2 error. Its size is bounded below with base512*windowDenominator(R,z)+1 and
exponent2*T*R. Sampling is performed on the final stable window. Compiles,
olean built; permitted axioms only.

### 324. `Submission/LocalizedPatternCriterion.lean`
Combines global residual control with local stable-window approximation:
 count error <=k*(eta/density(B)+kappa).
The exact diagonal for independent difference steps c-b is density(A)/|B|.
A local count exceeding the two errors and this diagonal forces an actual
nonzero-difference configuration. Compiles, olean built; permitted axioms only.
The criterion requires a lower bound for the ACTUAL local factor count, which
has not been supplied by local polynomiality alone.

### 325. `Submission/BohrPatternGeometry.lean`
A Bohr set is closed under n-fold dilation with n-fold radius. Steps from a
Bohr set of radius h/(2k), taken as differences c-b, keep every first-k AP
shift inside radius h. On a relatively stable window of tolerance1/z, the
mass of configurations with any vertex outside the domain is <=k/z. Masking
out these boundary configurations changes a unit-bounded average by <=k/z.
Compiles, olean built; permitted axioms only. Boundary points are not silently
regarded as satisfying the local polynomial identities.

### 326. `Submission/QuadraticCircleBridge.lean`
Converts every unit complex locally quadratic phase into an Additive Circle-
valued degree-two locally polynomial map. Complex coordinate values are
unchanged exactly, and all eight complete-cube vertices are checked. This
bridges the sampled factor output to the existing all-degree polynomial
recurrence/partition language. Compiles, olean built; permitted axioms only.

### 327. `Submission/LocalFactorMean.lean`
Every uniformity norm dominates the absolute global mean. A residual with
uniformityPower(n)<=eta^(2^(n+1)) changes the mean by at most eta. If local
factor approximations have normalized L2 error <=kappa^2, their averaged local
mean differs from the global approximant's mean by <=kappa. Hence the averaged
local factor mean is at least density(f)-eta-kappa. Compiles, olean built;
permitted axioms only.

Checkpoint after327: The global-to-local counting bridge is now explicit.
Global uniformity error contributes k*eta/density(B); local approximation
contributes k*kappa under epsilon+1/u<=kappa^2; the exact diagonal is density(A)/|B|.
Stable factor windows, actual small Bohr steps, boundary masking (cost<=k/u),
and mean preservation are all proved. The local complex phases also have exact
additive-circle polynomial lifts. There is still no sufficient joint
equidistribution/actual local count lower bound, nor a way to close the
quantitative error budget at reciprocal-summability strength, nor an all-degree
small-positive-uniformity inverse. These lemmas are not a settlement of Erdos3.
Spec.lean remains unchanged with its original sorry. No complete proof or
disproof has been submitted.

### 328. `Submission/ConvexLeastSquares.lean`
Least-squares minimizers over compact convex approximation classes exist and
satisfy a variational/Pythagorean inequality. For nested classes, the mean
squared distance between coarse and fine minimizers is bounded by the drop in
squared error to f. An energy pigeonhole gives a small coarse/fine step among
more than mean(f)/epsilon^2 stages, even when fine accuracies vary by stage.
Compiles, olean built; permitted axioms only.

### 329. `Submission/BoundedFeatureClasses.lean`
Defines compact convex classes of [0,1]-valued functions with changes bounded
by a weighted sum of test-coordinate changes. Adding a weighted test enlarges
the class and admits its clipped update. Projecting to the new class retains
at least the clipped-step energy decrease and adds Pythagorean control. No
unbounded least-squares approximant is introduced. Compiles, olean built;
permitted axioms only.

### 330. `Submission/ProjectedWeakRegularity.lean`
A detector-based weak regularity theorem that REFINES an existing bounded
feature minimizer. It adds <=ceil(mean(f)/rho^2)+1 tests, preserves old features
as a suffix, reaches the requested residual predicate, and retains the
coarse/fine mean-square bound by energy drop. Compiles, olean built; permitted
axioms only. This prepares a coarse/fine adaptive-accuracy decomposition.

### 331. `Submission/AdaptiveStrongRegularity.lean`
A generic bounded coarse/fine strong regularity theorem from detectors. Fine
accuracy Good(m) may be any predicate with a positive bounded detector, indexed
by the COARSE complexity m. Nested feature minimizers and an energy pigeonhole
produce coarse g and fine g' with mean squared difference <=epsilon^2, while
f-g' satisfies Good(m). The explicit number of outer stages is
 ceil(mean(f)/epsilon^2)+1;
the complexity bound iterates m -> m+ceil(mean(f)/rho(m)^2)+1. Feature certificates
retain the stage and weight of every test. Compiles, olean built; permitted axioms.

### 332. `Submission/StrongQuadraticRegularity.lean`
Instantiates331 with the stable local U3 detectors. Unconditionally, on finite
abelian groups with bijective doubling, bounded f has a coarse bounded feature
minimizer g and a bounded fine g' with L2 difference <=epsilon and U3-power of
f-g' <=delta(m), for ANY prescribed positive delta(m)<=1. Coarse features are
stable quadratic-average tests, with their exact stage-dependent ranks,
stability parameters and weights certified. Compiles, olean built; permitted
axioms only. The growth iteration can be very large; no summable density bound
or all-degree small-uniformity inverse follows from this theorem alone.

### 333. `Submission/FeatureLipschitzEnvelope.lean`
A finite McShane-type envelope gives an EXACT global [0,1]-valued Lipschitz
factor representation for every member of a bounded feature class. The
Lipschitz constant is the sum of test weights, and the stronger bound by the
weighted sum of individual coordinate errors is retained. Hence the coarse
least-squares minimizer is a genuine bounded factor of its test coordinates,
not merely an abstract approximation. Compiles, olean built; permitted axioms.

### 334. `Submission/StrongLocalizedCounting.lean`
A global L2 error between bounded functions changes any translated configuration
average by <=k*epsilon, even for arbitrary restricted step distributions.
There is NO inverse step-density loss for this error. Combining the coarse/fine
decomposition with the local factor approximation gives
 k*(eta/density(B)+epsilon+kappa),
with only the fine uniformity residual paying inverse density. Compiles, olean
built; permitted axioms only.

### Important certificate strengthening in331--332
FeatureCertificate now requires every coarse feature to come from an index
j STRICTLY LESS THAN m. The block size is positive, so the construction proves
this stronger property. It is essential: a non-strict j<=m certificate would
allow a coarse rank bound involving the current fine accuracy delta(m), thereby
obscuring the intended adaptive separation. All dependent files were rebuilt.

Checkpoint after334: A genuine bounded strong-U3 decomposition is now proved
using least-squares projection onto compact convex weighted-feature classes.
The fine residual accuracy can be prescribed from a STRICT prior prefix of
feature parameters, while the coarse/fine L2 error is independently small.
This supplies an alternative to the weak-regularity accuracy circularity, but
its recursive complexity can be enormous and does not give the required
summable density bound. The next structural work would be localizing the
weighted feature factors with stage-dependent stability tolerances (using
333's weighted-coordinate error bound), and obtaining joint distribution/
actual local factor counts. No all-degree small-positive-uniformity inverse,
all-length summability estimate, or settlement of Erdos3 is proved. Spec.lean
remains unchanged with its original sorry; no complete proof/disproof submitted.

### 335. `Submission/WeightedFeatureErrors.lean`
Weighted finite Minkowski: coordinate mean-square errors <=epsilon_i^2 give
factor mean-square error <=(sum_i w_i*epsilon_i)^2 under the weighted-coordinate
Lipschitz bound. No extra feature-count or maximum-error loss. Compiles, olean
built; permitted axioms only.

### 336. `Submission/VariableSampleCoordinates.lean`
Each feature can have its own sample count M_i. The resulting complex phase
coordinate space has dimension sum_i M_i, while the sampling map is 1-Lipschitz
and the composed factor has Lipschitz constant sum_i w_i, independent of the
sample counts. Compiles, olean built; permitted axioms only.

### 337. `Submission/WeightedLocalQuadraticFactor.lean`
Localizes arbitrary weighted Lipschitz factors of stable quadratic averages
with individual ranks, stability tolerances and sample counts. A common window
uses upper bounds R and Z; every nonempty subwindow works. The phase count is
sum M_i and the mean-square error is (sum w_i*epsilon_i)^2. Compiles, olean
built; permitted axioms only.

### 338. `Submission/WeightedFeatureLocalization.lean`
Applies337 to the exact feature-class envelope from333. With z_i^2 samples
per test, coordinate error is <=2/z_i. Thus sum w_i/z_i<=tau/2 gives local
mean-square error <=tau^2, including on a final relatively stable window chosen
at any additional tolerance. Compiles, olean built; permitted axioms only.

### 339. `Submission/BudgetedStrongRegularity.lean`
Strengthens adaptive strong regularity by retaining an actual list of stage-
tagged tests. Labels are strictly earlier than m, and total per-test cost is
bounded by sum_(j<m) blockSize(f,rho,j)*cost(j). This is proved through the
refinement construction, not inferred from the weaker existence-of-stage
certificate. Compiles, olean built; permitted axioms only.

### 340. `Submission/SummableStageBudgets.lean`
Chooses z_j=ceil(2^(j+2)*unitBlockSize(rho,j)*rho_j/tau)+1. Every prefix of actual
regularity stages then spends at most tau/2 on sum blockSize*rho_j/z_j. The
choice uses the current gain and tau only, not the final coarse complexity.
Compiles, olean built; permitted axioms only.

### 341. `Submission/BudgetedStrongQuadraticRegularity.lean`
Unconditional strong U3 regularity with the weighted stability budget proved:
 sum_(selected tests) rho_stage/z_stage <=tau/2.
The actual tags, strict prior-stage property, coarse/fine L2 error, and fine
U3 residual delta(m) are all retained. Compiles, olean built; permitted axioms.

### 342. `Submission/TaggedFeatureLocalization.lean`
Uses the tagged budget directly to localize the coarse convex feature factor.
A stable common window has a bounded Lipschitz unit-quadratic phase-factor
representation at every base point with normalized L2 error <=tau, independent
of the number of selected tests. The number of sampled phases is at most
(number of tests)*Z^2 when all prior stage tolerances are <=Z. Compiles, olean
built; permitted axioms only.

### 343. `Submission/StrongLocalQuadraticRepresentation.lean`
Combines budgeted strong U3 regularity and tagged stable local factors into one
unconditional theorem. The coarse window rank, radius, cardinality bound and
phase count depend only on accuracy indices strictly earlier than the final
fine residual index. The local factors are bounded in [0,1] and m-Lipschitz;
coarse/fine and local L2 errors are independently prescribed. Fixed the explicit
function argument in Finset.le_sup. Compiles, olean built; axiom audit gives
only propext, Classical.choice, Quot.sound.

Checkpoint after343: The approximation/localization construction is complete,
but actual local configuration-count lower bounds and sufficiently efficient
quantitative estimates are still missing. No all-degree small-positive-
uniformity inverse or all-length reciprocal-summability theorem has been
proved. Spec.lean is unchanged and still contains its original sorry.

### 344. `Submission/UniformFactorDistribution.lean`
Derives joint character discrepancy along n+2 distinct finite-field slopes
from small U^(n+1) power for every nontrivial character composed with the factor
map. No polynomiality assumption is needed for this implication. Specializing
to three slopes supplies the actual joint-discrepancy hypothesis in the
quadratic-model counting criterion, and yields a nontrivial four-point pattern
under explicit character-U2, residual-U3, exact-relation and numerical bounds.
Compiles, olean built; permitted axioms only. The character-U2 hypotheses are
not proved for the local factors of343; this is not a settlement of Erdos3.

### 345. `Submission/PolarizedQuadraticUniformity.lean`
For global quadratic maps q:H->G with an explicitly biadditive polarization B,
proves the exact identity
 U2Power(chi o q) = density{h : chi o B(h,-) is the trivial character}.
Also proves maximal U3 power and the exact four-point quadratic relation. An
explicit bound on each nontrivial character radical therefore supplies the
triple-distribution hypothesis and an actual nontrivial four-term progression
criterion. The domain and target in the identity can be arbitrary finite
abelian groups. Compiles, olean built; permitted axioms only.

Checkpoint after345: The global high-rank counting step now has a direct
polarization-radical formulation instead of a joint-discrepancy assumption.
This does NOT apply automatically to343: those phases are only locally
quadratic on Bohr windows, whose domain is not a group. Appropriate local
rank/distribution regularization remains missing. More importantly, no
summable all-length extremal bound or general small-positive-uniformity
higher-degree inverse is proved. The original target remains UNSOLVED;
Spec.lean is unchanged with its original sorry. No valid proof/disproof has
been submitted.

### 346. `Submission/StableMaskedUniformity.lean`
Ambient uniformity of a zero-extended local function bounds its normalized
configuration average on a stable Bohr window. For n+3 distinct slopes, one of
which is zero, with differences sampled from B-B, the bound is
 eta/(density(window)*density(B)) + (n+3)/z,
provided the masked distinguished function has U^(n+2) power <=eta^(2^(n+2)).
Includes complex boundary masking and the exact supported-average density
identity. No group structure on the window is assumed. Compiles, olean built;
permitted axioms only. Obtaining the masked uniformity hypotheses is separate.

### 347. `Submission/LocalQuadraticDistribution.lean`
Derives local triple-character discrepancy from masked ambient U2 bounds,
then transfers to the positive quadratic model with an explicit boundary
error. Local quadraticity is used only when all four vertices are inside the
Bohr window. The combined actual local count bound is
 mean_target(Phi)^4 - (eta/(density(W)*density(B))+3/z)*|target|^2 - 4/z.
The target here is a finite abelian group. Compiles, olean built; permitted
axioms only. Masked character uniformity is still an explicit hypothesis;
the circle-valued factors of343 need a further finite/compact-model bridge.

### 348. `Submission/FiniteCircleGrid.lean`
Quantizes every unit complex phase into ZMod N with chord error <=8/N.
Quantization has quadratic-word defect <=64/N, not an exact polynomial
identity. These estimates hold in the sup metric for arbitrary finite tuples.
Also derives the exact quadratic word identity for a four-term AP entirely
inside a locally quadratic phase's domain, checking all cube vertices.
Compiles, olean built; permitted axioms only.

### 349. `Submission/ApproximateLocalQuadraticCounting.lean`
Strengthens the local model transfer to an observable-level quadratic defect
nu on interior configurations. The count loss is nu+4/z in addition to the
character-discrepancy term. For an L-Lipschitz function of circle phases, finite
grid rounding changes the observable by <=8L/N and gives relation defect
<=64L/N. Compiles, olean built; permitted axioms only.

### 352. `Submission/AveragedLocalCircleCounting.lean`
Uses the averaged actual local mean, rather than a minimum over base points,
to lower-bound the averaged local counts. Fourier mass is bounded uniformly
by the target cardinality; fourth-moment convexity is applied after averaging
model means. Explicit modelMeanError and modelCountError retain all density,
grid, dimension, and stability costs. Compiles, olean built; permitted axioms.

### 353. `Submission/StrongLocalCharacterCriterion.lean`
Combines strong coarse/fine counting, local circle counting, averaged mean
preservation, and the exact diagonal density(A)/|B|. Gives a complete four-AP
criterion under explicit error/size budgets and masked-U2 bounds for every
nontrivial rounded local factor character. Contrapositively, under the same
budgets a four-AP-free set forces some base point and nontrivial rounded
character to have masked U2 power >theta^4. Compiles, olean built; permitted
axioms only.

Checkpoint after353: The actual local circle-factor counting bridge is now
proved, conditional on masked lower-order uniformity. It includes boundary,
finite-grid, local/global approximation, mean transfer, and diagonal errors.
The main new structural obstruction is explicit: a bad rounded local factor
character. This alternative has not been eliminated or converted into a
sufficiently efficient density increment. Rounded characters need not be
locally polynomial, so their large Fourier coefficients cannot silently be
used as exact polynomial relations. Local rank/distribution regularization,
quantitative reciprocal summability, and the arbitrary-length argument remain
missing. Spec.lean is unchanged with its original sorry. No valid proof or
disproof of the conjecture has been submitted.

### 354. `Submission/PositiveSpectralKernel.lean`
A dual-character set S defines the nonnegative probability kernel
 K_S(x)=|sum_(chi in S) chi(x)|^2/|S|.
Its Fourier coefficient at psi is exactly |{b in S : b*psi in S}|/|S|,
so its spectrum is supported in S/S. The weighted chord-square moment in
coordinate psi is exactly twice the relative dual boundary. Compiles, olean
built; permitted axioms only.

### 355. `Submission/PositiveSpectralSmoothing.lean`
Convolution with K_S preserves means and [0,1] bounds and has Fourier support
inside S/S. Its fourth Fourier-L1 power is <=|S/S|^2, independently of ambient
group size. For L-Lipschitz observables of designated characters, coordinate
dual boundaries <=sigma_i^2/2 give uniform approximation <=L*sum sigma_i.
Compiles, olean built; permitted axioms only.

### 356. `Submission/FiniteFrequencyCoordinates.lean`
Explicit injective coordinates for finite-torus characters, including integer
representatives and frequency bounds stable under products, quotients, and
powers. Retains actual coefficient sizes, rather than arbitrary residues.
Compiles, olean built; permitted axioms only.

### 357. `Submission/RectangularSpectralCutoff.lean`
A dual box with coefficients 0,...,K has size (K+1)^m when K+1<=N. Its ratio
set has size <=(K+1)^(2m) and frequency bound K. Each coordinate dual boundary
has relative size <=1/(K+1), yielding chord second moment <=2/(K+1).
Compiles, olean built; permitted axioms only.

### 358. `Submission/BoundedFrequencyObservable.lean`
Positive smoothing of an L-Lipschitz grid observable has frequency bound K,
fourth Fourier mass <=(K+1)^(4m), and uniform error <=L*m*sigma when
2/(K+1)<=sigma^2. Mean and [0,1] bounds are retained. Includes explicit rounding
and approximate-quadratic-observable error bounds. No ambient-modulus factor
appears in the mass estimate. Compiles, olean built; permitted axioms only.

### 359. `Submission/SparseFourierModelTransfer.lean`
Multilinear discrepancy is required only on tuples with nonzero Fourier
coefficients. For frequency-bound-K observables, quadratic model transfer
therefore uses only triple character tests of frequency bound 4K. This removes
the need to control every high-frequency character of the finite grid.
Compiles, olean built; permitted axioms only.

### 360. `Submission/BoundedFrequencyPhaseApproximation.lean`
A character represented by |k_i|<=R differs from the exact product Q_i^k_i by
at most 8*m*R/N after grid rounding. The masked U2 powers differ by at most
32*density(W)*m*R/N. The unrounded integer product is proved genuinely locally
quadratic, including negative exponents. Compiles, olean built; permitted axioms.

### 361. `Submission/LocalFrequencyModel.lean`
Local triple discrepancy and boundary-tolerant observable-defect model counting
now accept bounded-frequency character tests only. The Fourier loss remains
the observable's actual Fourier mass. Compiles, olean built; permitted axioms.

### 362. `Submission/BoundedFrequencyLocalCircleCounting.lean`
Actual local circle-factor count using only bounded-frequency combinations.
The count loss is
 (theta/(density(W)*density(B))+3/z)*(K+1)^(4m) + 4/z + 6*L*m*sigma + 96*L/N,
with 2/(K+1)<=sigma^2. The grid modulus appears only in the vanishing rounding
error, not in the Fourier-mass cost. After a stated rounding budget, the only
distribution hypotheses concern exact, nonzero integer products of the original
locally quadratic phases with |k_i|<=4K. Compiles, olean built; permitted axioms.

### 363. `Submission/BoundedFrequencyLocalMean.lean`
Mean transfer now needs bounded-frequency tests only, with Fourier mass
<=(K+1)^m rather than a grid-size factor. The actual local mean differs from
the grid mean by at most L*m*sigma+8L/N+theta/density(W)*(K+1)^m. Includes a
reusable exact-phase-to-rounded-character U2 conversion. Compiles, olean
built; permitted axioms only.

### 364. `Submission/AveragedExactPhaseCounting.lean`
Combines bounded-frequency mean transfer and local counts, averaging before
applying fourth-moment convexity. All character hypotheses concern exact
nonzero integer combinations |k_i|<=4K of the original local phases. Grid
size contributes only inverse-modulus errors. Compiles, olean built; permitted
axioms only.

### 365. `Submission/StrongExactPhaseCriterion.lean`
Updates the full strong-decomposition four-AP criterion and its contrapositive.
Under explicit mean, boundary, grid, residual, and diagonal budgets, a four-AP-
free set forces a nonzero vector |k_i|<=4K whose exact original phase product
has masked U2 power >theta^4/2. The rounded-character obstruction has thus
been replaced by a genuinely locally quadratic, bounded-frequency obstruction.
Compiles, olean built; permitted axioms only.

### 366. `Submission/ExactPhaseLinearObstruction.lean`
Retains support density in the elementary Fourier inverse estimate. Every
unit local phase q admits a linear character psi with
 U2Power(1_W*q) <= density(W)^3 * |E_(t in W) q(t)*conj(psi(t))|^2.
The exact bounded-integer phase obstruction from365 therefore has a normalized
linear-correlation certificate while retaining its local quadraticity.
Compiles, olean built; permitted axioms only.

Checkpoint after366: Positive spectral smoothing and restricted Fourier
transfer remove the spurious high-frequency rounding obstruction. The current
counting alternative is an exact locally quadratic integer product with
bounded coefficients and a quantitative local linear correlation. This is NOT
a density increment or a rank-reduction theorem: a correlated phase combination
could encode a dependency among factor coordinates, and a valid efficient
refinement still has to be constructed. No summable four-term extremal estimate,
arbitrary-degree small-positive-uniformity inverse, or arbitrary-length
reciprocal-summability proof is established. Spec.lean remains unchanged with
its original sorry. No complete proof/disproof is available for submission.

### Backfilled entries 350-351 (completed before352)
350. `Submission/LocalCircleFactorCounting.lean`: actual local circle-factor
count via grid quantization, with explicit 96L/N error and hypotheses on all
nontrivial rounded characters. Compiled and audited.
351. `Submission/LocalCircleFactorMean.lean`: transfers those character bounds
to observable means, connecting the model density to the actual local mean.
Compiled and audited. Both use only permitted axioms; their broad character
hypotheses have now been sharpened in362-365.

### 367. `Submission/LocalCharacterApproximation.lean`
For a unit phase q with local overlap relation q(x+h)=c(h)q(x), Fourier
translation gives |hat(1_W q)(psi)|*|psi(h)-c(h)| <= boundary(W,h).
A family P with boundary <=density(W)/2 forces masked U2 at least
 density(P)*density(W)^2/4.
This gives normalized character approximation error <=delta/rho under
4*rho^2*density(W)<=density(P). Approximation is not an exact extension.
Compiles, olean built; permitted axioms only.

### 368. `Submission/LocalQuadraticPolarization.lean`
Defines localPolar(q,h,x)=D_h q(x)*conj(D_h q(0)). It is unit and symmetric.
The eight-vertex local quadratic identity proves its local multiplicativity,
with every domain condition retained. Applies367 to derivatives without
requiring stronger inverse witnesses. Compiles, olean built; permitted axioms.

### 369. `Submission/LocalCharacterEnergy.lean`
Strengthens367: if local multiplicativity covers every nonempty W-overlap,
 U2Power(1_W q)=U2Power(1_W) >=density(W)^4.
The normalized correlation can therefore be any positive rho with
rho^2<=density(W), independent of the final stability tolerance. This avoids
a circular choice of fine radius versus correlation. Compiles, olean built;
permitted axioms only.

### 370. `Submission/BohrDerivativeCharacters.lean`
For any unit phase locally quadratic on Bohr(D,R), a stable r in [R/8,R/4]
supports ambient characters F(h) approximating every derivative h in
Bohr(D,R/4) on Bohr(D,relativeWidth(D,z,r)). The error is 1/(z*rho), with
rho^2<=density(Bohr(D,R/8)); rho is independent of z. The radius is selected
before the phase. No assertion that F is exactly additive or that the local
characters extend exactly is used. Compiles, olean built; permitted axioms.

Checkpoint after370: Approximate derivative-character representations for
arbitrary local quadratic phases are now available, so stronger inverse
witness propagation is unnecessary for that step. Efficient spectral
refinement/rank reduction, summable four-term bounds, and all-length bounds
remain unproved. Spec.lean is unchanged with its original sorry.

### 371. `Submission/WeightedSpectrumPacking.lean`
For a complex weight bounded by one on C, an epsilon-orthogonal family
of coefficients of size at least eta has cardinality <=2/eta^2 when
epsilon<=eta^2/2. A maximal family covers every large coefficient by one
selected character modulo a character with C-mean >epsilon. Consequently
all large weighted-spectrum characters have phase <=delta/epsilon+gamma
on Bohr(D,gamma) intersected with a C-stability window of tolerance delta.
Unlike relative Chang for a sparse indicator, the unit-weight case needs
only this Bessel packing bound, without an exponential dissociation tolerance.
Compiles, olean built; permitted axioms only.

### 372. `Submission/BiasedPhaseSpectrum.lean`
A phase with C-bias >=beta, derivative approximation error a, and translation
error b has derivative characters in its weighted spectrum at threshold
beta-a-b. Combining371 with approximate polarization gives a bounded-rank
set controlling all derivative characters simultaneously, independent of
the number of derivative shifts. Mixed polarizations are then small with
explicit error a+delta/epsilon+gamma. Compiles, olean built; permitted axioms.

### 373. `Submission/BiasedPolarizationFlattening.lean`
If a beta-biased unit phase has a derivative within a of a constant c on
its averaging window, and translating that window costs b, then
 |c-1| <=(a+b)/beta.
Small mixed polarization thus controls both the phase at the base point
and its translations throughout the biased window. Compiles, olean built;
permitted axioms only.

### 374. `Submission/WindowBiasLocalization.lean`
Bias on W transfers to a translated smaller window T with only the W
translation error, not a density(T) loss. Centers may be restricted to
an interior set S, at the additional cost of the excluded-center fraction.
Compiles, olean built; permitted axioms only.

### 375. `Submission/BiasedQuadraticTranslateFlattening.lean`
Proves translation invariance of local polarization from the connecting
cube identity with all eight domain conditions. Combines374 and373 to
obtain a translated flat inner window from bias and small mixed polarization.
A Bohr-domain version replaces the domain checks with a radius-sum budget.
Compiles, olean built; permitted axioms only.

### 376. `Submission/BiasedQuadraticBohrRefinement.lean`
Packages372 and375 into a bounded-rank single-phase flattening theorem.
For a phase locally quadratic on Bohr(D,R), biased on stable Bohr(D,r),
with derivative character approximation error a for shifts in stable
Bohr(D,s), add a frequency set E of cardinality <=2/eta^2. On a translated
inner window, the phase is almost invariant under Bohr(D union E,t).
The base-point error is explicitly
 (a+1/z/epsilon+t+1/w)/(beta-1/z).
All stability, bias, approximation, and radius budgets are stated. Compiles,
olean built; permitted axioms only.

Checkpoint after376: The former local-character gap now has a valid
approximate solution and a bounded-rank single-phase flattening theorem.
This is NOT a factor-coordinate rank reduction, a density increment, or a
summable extremal-density bound. Combining the certificate from366 with
these results still requires selecting nested windows and transferring
bias without losing control of the factor complexity. Four-term reciprocal
summability and arbitrary-length progression results remain unproved.
Spec.lean remains unchanged with its original sorry; there is no valid
complete proof/disproof to submit.

### 377. `Submission/InteriorBohrBiasTransfer.lean`
A relatively stable outer Bohr window loses at most 1/o of its centers when
restricted to the boundary-buffer interior. Bias transfers to any nonempty
smaller window inside the translation buffer with total loss <=2/o. The
translated phase retains local quadraticity on the entire buffer domain.
Compiles, olean built; permitted axioms only.

### 378. `Submission/UnconditionalBiasedPhaseRefinement.lean`
Constructs three nested stable radii, independently of the phase, and removes
the derivative-character hypothesis from376. Applies377 to localize bias,
then370 to construct the characters, then376 to refine. The output includes
all translated domain containment, not merely oscillation bounds. Raw
precision and radius budgets remain explicit. Compiles, olean built;
permitted axioms only.

### 379. `Submission/PhaseRefinementBudgets.lean`
Explicit geometry and numerical estimates for378. With A_j=4*j*(7*d+1),
the base radius is >=R/(128*A_o*A_v*A_z), and the refined radius can be
>=min(R/(512*A_o*A_v*A_z*A_w),sigma*beta/16). Precision budgets
 1/o<=beta/8, 1/(v*rho)<=sigma*beta/16,
 1/z<=sigma*beta^3/512, 1/w<=sigma*beta/16
make eta=beta/4 and epsilon=beta^2/32 valid and give final oscillation <=sigma.
Compiles, olean built; permitted axioms only.

### 380. `Submission/QuantitativeBiasedQuadraticFlattening.lean`
Combines378-379. A biased unit locally quadratic phase admits translated
flattening with at most32/beta^2 new frequencies and the explicit positive
radius lower bound above. The phase oscillates <=sigma/2 at the base point
and <=sigma throughout the translated inner window. All such points remain
in the original local-quadratic domain. No derivative representation is
assumed. Compiles, olean built; permitted axioms only.

### 381. `Submission/ExplicitPhaseFlattening.lean`
Eliminates the remaining free correlation and inner precision parameters.
For U=R/A_o, M=ceil(16/U)+1 and rho=(2*M+1)^(-d), the elementary Bohr-cardinality
bound proves rho^2<=density(Bohr(D,U/8)). Closed ceiling choices specify v,z,w.
Thus the final rank and positive radius bounds depend only on d,R,beta,sigma,o.
The sole outer-window requirement is relative stability fine enough that
1/o<=beta/8. Compiles, olean built; permitted axioms only.

### 382. `Submission/LocalQuadraticU2Linearization.lean`
Connects the masked-U2 Fourier certificate to381. If
 beta^2*density(W)^3 <=U2Power(1_W*q),
a unit phase locally quadratic on stable W admits an ambient character psi
and an explicit bounded-rank refined Bohr window where
 |q(b+x+y)-q(b+x)*psi(y)|<=sigma.
The same rank32/beta^2 and positive radius bounds are retained. No derivative
representation, bias on a finer window, or polarization bound is assumed.
Compiles, olean built; permitted axioms only.

Checkpoint after382: The large-U2 exact local phase obstruction can now be
converted into a quantitative approximate linear dependency on a translated
refined window. The next structural issue is turning a bounded-integer
combination dependency into a lower-dimensional factor while controlling
root branches, local observables, and complexity across base points. This
is not yet a factor-rank reduction or density increment. The summable
four-term extremal bound and all-length argument remain unresolved.
Spec.lean is unchanged with its original sorry; no valid settlement exists
for submission.

### 383. `Submission/RootFreeQuadraticDilation.lean`
Defines T_n(q,b,x)=(D_x q(b))^2*(D_x D_x q(b))^(2n-1). For a unit locally
quadratic phase and an admissible progression through b,
 q(b+2n*x)=q(b)*T_n(q,b,x)^n.
If q agrees with q(b)*psi at x and2x to precision delta, then
 |T_n(q,b,x)-psi(x)^2|<=6*n*delta. No roots or divisibility assumptions occur.
Compiles, olean built; permitted axioms only.

### 384. `Submission/RootFreePhaseStructure.lean`
Local quadraticity is closed under unit constants, multiplication, conjugation,
natural powers, and affine additive-homomorphism pullbacks. T_n retains local
quadraticity whenever the first two sampled points lie in the original domain.
T_n commutes exactly with arbitrary integer phase combinations. Compiles,
olean built; permitted axioms only.

### 385. `Submission/RootFreeCoordinateReconstruction.lean`
For a relation with positive pivot k_j=n, the tuple c_i*v_i^n is reconstructed
from all v_i except v_j, up to exactly the relation error |prod v_i^k_i-1|.
The pivot formula uses prod_(i!=j) v_i^(-k_i), not an nth root. Reconstruction
ignores the pivot input and preserves unit tuples. Compiles, olean built;
permitted axioms only.

### 386. `Submission/ReducedObservableExtension.lean`
Reconstruction on unit tuples is Lipschitz with cost n+sum_i |k_i|. A bounded
L-Lipschitz observable therefore admits a reduced observable, globally
bounded in[0,1] and globally L*(n+sum|k_i|)-Lipschitz. McShane extension followed
by clipping agrees exactly on all unit input tuples. No global Lipschitz
claim is made for negative powers near zero. Compiles, olean built;
permitted axioms only.

### 387. `Submission/RootFreeFactorElimination.lean`
Combines383-386 into an actual one-coordinate reduction on the2n-dilate.
The reduced index type {i:I // i!=j} has exactly |I|-1 elements. All new phases
are unit and locally quadratic, and the observable error is at most
 L*(6*n*delta+2*gamma), where gamma controls the linear character's phase.
Also proves the cost <=(|I|+1)*K for coefficients bounded by K. Compiles,
olean built; permitted axioms only.

### 388. `Submission/BohrFactorCoordinateElimination.lean`
Combines382 with387. A positive-pivot large-U2 dependency gives one-coordinate
reduction on a dilated Bohr domain, rank <=d+32/beta^2+1, and explicit radius
 >=min(explicitBase/(2n),explicitStep/2,tau/8).
The observable error is <=L*tau; all original sample points remain in the
quadraticity domain. Compiles, olean built; permitted axioms only.

### 389. `Submission/OrientedPhaseDependency.lean`
Conjugation preserves every uniformity power, including masked powers.
Any nonzero pivot can be made positive by reversing the relation's sign;
coefficient magnitudes and reconstruction costs remain unchanged. Compiles,
olean built; permitted axioms only.

### 390. `Submission/LocalFactorDimensionReduction.lean`
The nonzero-pivot local dimension reduction is now complete. When multiplication
by 2*|k_j| is bijective, transport the dilation through an additive equivalence
to obtain an ordinary translated Bohr window. Rank and radius bounds are
unchanged, and the factor has |I|-1 unit locally quadratic coordinates with a
bounded global Lipschitz observable. This condition on dilation holds in prime
cyclic groups larger than twice the pivot coefficient. Compiles, olean built;
permitted axioms only.

Checkpoint after390: Root branches are no longer an obstacle to one local
factor-coordinate elimination: root-free2n-dilation resolves them, and390
returns an ordinary Bohr domain. The remaining iteration issue is preserving
the original observable/set density or average mass across refined windows.
A window selected for the phase dependency need not be a high-density window
for the original observable. No density-preserving factor refinement, summable
four-term extremal estimate, or all-length argument has been established.
Spec.lean remains unchanged with its original sorry; no valid complete
proof/disproof is available for submission.

### 391. `Submission/DoublingOverlapEnergy.lean`
Completed overlap-energy estimates in terms of relative difference-set doubling,
and the bound |W-W| <= 81^rank(W)*|W| for Bohr windows. Compiled.

### 392. `Submission/RobustLocalCharacter.lean`
Completed robust local-character approximation from approximate multiplicativity
on overlaps. Correlation depends on relative doubling rather than ambient density.
Compiled; permitted axioms only.

### 393. `Submission/RobustBohrLinearization.lean`
Completed radius-independent character approximation on stable Bohr windows,
with error 2*9^rank*(1/z+a), and linearization at any prescribed center whose
polarization satisfies the overlap bound. Compiled; printed axiom checks report
only propext, Classical.choice, Quot.sound.

Final checkpoint: the original conjecture has NOT been proved or disproved.
Density-preserving refinement, summable four-term estimates, and the all-length
argument remain missing. Spec.lean still contains its original sorry. No valid
settlement is available for submission.

### 394. `Submission/AdmissibleCenterPolarization.lean`
Proved localPolar_centers: the normalized second derivative agrees at any two
centers provided the four parallelogram vertices at each center lie in the
local quadraticity domain. The displacement between centers need not lie in
that domain. Compiled and built olean; axiom check reports only propext,
Classical.choice, Quot.sound. This supplies center transport but NOT a common
refinement window or density-preserving averaging. The conjecture is unresolved.
