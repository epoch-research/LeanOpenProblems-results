# Latest verified bound (supersedes the historical summaries below)

BuchstabPolylogarithmicGrowth.lean now proves:
  exists_quadratic_polylogarithmic_bound:
    exists d : Nat, exists A > 0, forall k > 0,
      h(k) <= A*k^2*log(k+2)^d.
The natural exponent d is fixed, but NOT asserted to be zero. The original
quadratic conjecture remains unsolved. This improves the previous family
of fixed 2+epsilon upper bounds. Every actual error cost is included.

BuchstabEulerUniformMain.lean gives a quantitative comparison of the actual
finite-prime main recurrence, uniform in all depths and all prime prefixes,
with an explicit O(depth) shift in log(D). See the newest log entry below.
Spec.lean remains unchanged with its original sole sorry at line2177.

NEWEST FINITE CORRELATION DEVELOPMENT:
  WeightedCoverageCollision.lean gives an exact insertion covariance
  identity, including a negative product of mean completion increments,
  and a positive recursive majorant retaining actual completion weights.
  WeightedCoreCollision.lean transfers it through a core with a capped
  remainder <= both actual union coverage and the former raw collision
  remainder. CompletionCollisionFibers.lean identifies the increments as
  genuine nonempty concentrated-survivor probabilities.
  No sufficiently small RELATIVE bound for this correction is proved.

NEWEST CONDITIONAL REDUCTION (LogLossSquareCubicReduction.lean):
  A fixed B>0 exists such that eventual budget-uniform square-cubic doubling
  with loss exp(C*k/log(k)^B), for any fixed C>=0, would prove the quadratic
  target. The correlation premise is STILL UNPROVED.
NEWEST ONE-HIT BARRIER (OneHitCollisionBarrier.lean):
  If one tail modulus is <= half the mean core population mu, the additive
  coreCollisionFraction is >=1-4/mu. At m>=k^2 it tends uniformly to one
  whenever the tail contains a modulus O(k*log(k)^d), with fixed d.
  This is a limitation of that remainder decomposition, NOT a disproof of
  the correlation premise or the original conjecture.

NEWEST UNCONDITIONAL VOID ESTIMATES (LogCriticalVoid.lean):
  For one fixed b : Nat with b>0, uniformly over prime sets P.card<=k,
  eventually V_P(k) <= exp(-sqrt(k)/(800*log(k)^b)), and
  eventually V_P(k^2) <= exp(-k/(800*2^b*log(k)^b)).
  These improve the previous fixed subcritical power rates. They still
  do NOT reach the k*log(k) phase-entropy rate and do NOT settle the target.

---

# Recursive sieve research status

CURRENT BEST VERIFIED UNRESTRICTED GROWTH RESULTS:
  BuchstabArbitraryGrowth.lean, Erdos970.RecursiveSieve.Buchstab:
    exists_growth_above_two:
      for every fixed real s>2, h(k) <= C_s*k^s*log(k+2)^(s-1), all k>0.
    exists_near_quadratic_bound:
      for every epsilon>0, h(k) <= C_epsilon*k^(2+epsilon), all k>0.
  These improve the previously fixed exponent51/25. The old explicit
  four-refinement result remains valid but is no longer the best exponent.
  All real powers are genuine Real.rpow. All axiom audits are clean.
  The constants and prime thresholds depend on s/epsilon. NO uniform bound
  as epsilon tends to zero was proved. The ORIGINAL QUADRATIC CONJECTURE
  REMAINS UNSOLVED; Spec.lean still contains its original sorry.

LATEST MAIN-TERM TRANSFER:
  BuchstabContinuousMain.lean proves continuous_model_transfer at every
  fixed depth, and exists_referenceLower_positive_above_two for every s>2.
  This is now a theorem about ACTUAL finite-prime refinements, not just the
  continuous model. Variable terminal tails and arbitrary finite-sector
  meshes replace the old fixed mesh1/50 and cutoff12 in this transfer.
  The continuous clamped profile is still proved zero at s=2 at every depth.
  No quantitative depth-uniform prime-error estimate has been established.

ERROR COSTS UNCHANGED:
  Complete smooth source cost at depth n is at most
    (60*smoothLeafConstant 1*3600^n)*D*log(p_k)/log(D)^3.
  The separate all-depth bound4*exp(1)*D*(1+log D) does NOT retain that
  inverse-log-square saving. No error constant was silently made uniform.

LATEST UNCONDITIONAL VOID AND CONDITIONAL QUADRATIC DEVELOPMENT:
  ArbitraryExposureBudget.lean proves the power exposure budget whenever
  2*a<b, using the new near-quadratic bound. ArbitrarySubcriticalExposure.lean
  proves, uniformly over prime sets P of cardinality at most k, eventually:
    V_P(k) <= exp(-k^sigma/400), for every fixed sigma<1/2;
    V_P(k^2) <= exp(-k^tau/400), for every fixed tau<1.
  Thresholds depend on sigma/tau. This supersedes the fixed49/100 and49/50
  exponents in NearCriticalExposure.lean, which remain valid.
  SubexponentialSquareCubicReduction.lean supplies a CONDITIONAL quadratic
  route from V_P(2m)^2 <= exp(C*|P|^beta)*V_P(m)^3 (m>=|P|), with
  C>=0 and0<=beta<1. This weakens the older polynomial-loss premise in
  SquareCubicDyadicReduction.lean. The nonlinear premise remains UNPROVED.
  The unconditional void exponents remain below the phase-entropy scale.
  No target settlement.

LATEST ALL-DEPTH ERROR DEVELOPMENT (does not improve that growth bound):
  BuchstabOrderedCost.lean proves a depth-uniform finite prefix-product bound.
  BuchstabOrderedZeta.lean sharpens the prime product to zeta(a)<=1+1/(a-1).
  BuchstabOrderedSharp.lean applies the optimized estimate to the actual
  scaled canonical source: complete lower error <=4*exp(1)*D*(1+log D)
  for D>1, uniformly in every depth and prime prefix. All audits are clean.
  This is NOT an all-depth inverse-log-square cost bound.

The original conjecture is STILL UNSOLVED. Spec.lean has not been changed in this round;
it still has its sole original sorry at line 2177. Do not submit it as a completed proof.

## New verified Lean files (all oleans built)

* RecursiveSieve.lean (169 lines)
  - exact first-hit decomposition for finite nonnegative weighted populations;
  - envelope_sound;
  - weighted_survivor_of_positive_envelope;
  - survivor_of_positive_envelope.
* RecursiveSieveTransfer.lean (129 lines)
  - added_hits_moment_error (namespace FiniteSelberg): independent virtual OR hits
    preserve the uniform absolute moment error <=1;
  - survivor_from_dominating_envelope: coefficient-free reference-marginal transfer.
* RecursiveSieveRational.lean (131 lines)
  - computable polymorphic linearEnvelope;
  - linearEnvelope_eq_envelope;
  - linearEnvelope_congr (only coordinates below k matter);
  - cast_linearEnvelope: rational kernel evaluation transfers to real evaluation;
  - survivor_of_positive_linearEnvelope.
* RecursiveReferenceCriterion.lean (84 lines)
  - ReferencePositive k m, the rational recurrence at the first k primes;
  - survivor_of_referencePositive;
  - isJacobsthalBound_of_referencePositive (pads prime sets to exact cardinality k);
  - quadratic_bound_of_referencePositive, CONDITIONAL on uniform positivity.
* RecursiveSieveExample.lean (43 lines)
  - firstFifty_linear_positive: kernel-checked rational recurrence at k=50,m=15000;
  - firstFifty_nth: kernel-checked explicit prime list and prime counts;
  - isJacobsthalBound_fifty;
  - jacobsthalFunction_fifty_le : jacobsthalFunction 50 <= 15000.

All printed axioms are only propext, Classical.choice, Quot.sound.
No native_decide was used. These are DEVELOPMENT FILES, NOT integrated into Spec.
The finite k=50 result is NOT a uniform quadratic theorem.
Also built the previously unbuilt FirstHitSelberg.olean.

## Numerical recursive construction

First-hit lower/upper polynomials give the following absolute-error objectives:

  L_i(x) = max(0, x - 1 - sum_{j<i} U_j(x/p_j))
  U_i(x) = x + 1 - sum_{j<i} L_j(x/p_j).

The Lean evaluator is allowed to discard a lower branch when x <= i+1.
The same pruning was used in diagnostics.
At the very root, the original Python script /tmp/recursive_sieve.py omits the
constant-coefficient error, so its reported root margin is 1 larger than the
Lean linearEnvelope objective. Its emitted polynomial's full L1 threshold
must include this distinction.

Scripts:
* /tmp/recursive_sieve.py k m [--rounded] [--certificate]
  - direct recursive construction, fast for modest k;
  - emits /tmp/recursive_sieve_<k>_<m>.json.
* /tmp/recursive_fast.py k --ratio 25 --small 10 --thresholds 1500
  - uses the second-order lower recurrence and small-prefix piecewise-linear splines;
  - /tmp/recursive_fast_data.json has primes, prefix reciprocal sums, splines, thresholds.
* /tmp/recursive_eval.cpp and compiled /tmp/recursive_eval
  - /tmp/recursive_data.txt has the first million primes and precomputed small data;
  - /tmp/recursive_eval.log has completed large-k threshold diagnostics.

Threshold diagnostic (full constant-coefficient error included):
  k=1000:    m/k^2 = 9.37626463, m/p_k^2 = 0.14951652
  k=10000:   m/k^2 = 14.6508780, m/p_k^2 = 0.13357640
  k=100000:  m/k^2 = 21.3403642, m/p_k^2 = 0.12633090
  k=1000000: m/k^2 = 29.4335291, m/p_k^2 = 0.12273587

These are floating-point diagnostics only, not formal asymptotic claims.
They do NOT supply a uniform quadratic bound and suggest this particular
recursive construction retains the classical logarithmic loss.

## LP updates

k50,m10000 finished full numerical separation; file
/tmp/sieve_glpk_50_10000_dual.json exists.
Both k50 certificates (m10000 and m12500) normalize to coefficients all +/-1.
All have a factor (1-X_2).

m12500:
  476 terms, rounded main 238, mean ~0.0379273448440,
  full L1 absolute margin ~-1.90819, absolute threshold ~12550.31171.
m10000:
  500 terms, rounded main 153, mean ~0.0398239780775,
  absolute threshold ~12555.24998.
k30,m4500:
  204 terms, rounded main 126, mean ~0.0501850944671,
  full L1 margin ~21.832925, absolute threshold ~4064.952.

These LP witnesses have NOT been Lean checked. The newer recursive construction
is kernel checked at m15000 instead and avoids any dependence on solver output.

Stopped k100,m50000 GLPK PID23596 after iteration9 because MILP separation was
consistently timing out with large positive upper bounds. It had not certified
full feasibility or infeasibility. State and current dual remain for restart:
/tmp/sieve_glpk_100_50000_state.json
/tmp/sieve_glpk_100_50000_current_dual.json
No computational worker from this round is still running.

## Other diagnostic

Checked adjacent-gap sums for primorials through the first9 primes. The necessary
condition max_two_adjacent_gaps <= max_single_gap + 2k held throughout:
max gaps 2,4,6,10,14,22,26,34,40;
max adjacent sums 4,6,10,14,22,26,34,40,46.
This is not a proof of LargestPrimeIncrement or even its two-survivor consequence.

## Mathematical blocker

No uniform ReferencePositive bound was proved. No general proof or disproof of
quadratic Jacobsthal growth was found. Classical first-hit/linear-sieve arguments
appear to need an additional ingredient beyond the established unit-error
intersection framework. Extra positional correlations, stronger cover exchange
arguments, and the largest-prime increment remain unproved directions.

# Subsequent parity / increment investigation

Still NO proof or disproof of the original conjecture. Spec was not changed.
New file `ParitySeparation.lean` (olean built, all printed axioms allowed):

Namespace Erdos970.IncrementReduction:
* modEq_two_of_avoids
* two_mul_le_sub_of_modEq
* primeSetBound_insert_of_two_of_two_mem
* primeSetBound_insert_iff_two_of_two_mem

The latter sharpens the earlier two-survivor equivalence: if 2 is in P,
P has a bound g, p is a new prime, and g < 2*p, then insertion of p is
exactly a two-survivor test. The previous version required g < p.
This does NOT prove the unproved LargestPrimeIncrement.

Namespace Erdos970.OptimalCoverCore:
* two_mul_used_prime_lt_length:
  IsOptimal m P r -> 2 in P -> p in P -> p != 2 -> 2*p < m.
* survivor_card_le_two_of_two_not_mem:
  IsOptimal m P r -> 2 not in P -> survivors.card <= 2.

No assertion that a globally optimal core must contain 2 was proved.
No assertion that it must have a nonempty survivor set was proved.

## Exact integer diagnostic scans (not kernel checked)

/tmp/gap_increment_scan.cpp, compiled /tmp/gap_increment_scan.
Both processes finished; no workers remain.

For odd prime sets Q, the proposed LargestPrimeIncrement would imply
max_adjacent_gap_sum(Q) - max_gap(Q) <= Q.card + 1 after adjoining parity
and then a sufficiently large prime. Searched this necessary condition:

* /tmp/gap_increment_scan6.log:
  All 1330 sets {3,5,7} union three primes chosen from [11,97].
  Total 16,422,261,450 period positions scanned.
  Largest observed difference: 4 (required upper bound 7).
* /tmp/gap_increment_scan7.log:
  365 sets {3,5,7} union four primes chosen from [11,53], restricted to
  product <=100,000,000.
  Total 16,812,612,075 period positions scanned.
  Largest observed difference: 3 (required upper bound 8).

No counterexample was found. These scans do NOT prove any uniform increment.

## Mathematical cautions / remaining directions

* A covariance-only Janson lower-tail argument for random residue classes is invalid
  without more assumptions. One rare prime residue can block a large common class;
  its failure probability is 1/p, not exp(-c*p). Ordinary overlap-based Janson bounds
  do not give the desired entropy gain. No valid uniform probabilistic proof resulted.
* A putative near-mean bound on higher reduced-residue gap sums could potentially
  give an increment recurrence with coefficient <2, but no such bound was proved.
  Uniform near-mean discrepancy for arbitrarily long intervals is too strong;
  short-interval versions remain speculative.
* Square candidate sets have smooth differences, but sieving their index set leaves
  too few candidates at quadratic length. This did not remove logarithmic losses.
* Largest-prime deletion doubling, existence of an optimal core containing 2, and
  absence of empty optimal cores are all still UNPROVED, not safe lemmas to use.

# Subsequent LP performance investigation

The conjecture is STILL UNSOLVED. No change was made to Spec.lean in this round.
Recompiling it succeeded with the original sorry warning; the only sorry remains
at line 2177. No proof submission was made.

* /tmp/sieve_highs_master.py (k100,m25000, highs-ipm) completed its cold master
  in 469 seconds. Restricted slack = 0.04701912400712444.
  This is NOT full-relaxation infeasibility. Output:
  /tmp/sieve_glpk_100_25000_highs_dual.json.
  Its 4389 coefficients have many different magnitudes and do not factor parity.
* /tmp/sieve_glpk_dual_cg.py, PID26135, reached its 1800-second initial-master
  limit without a usable solution. Backend reported `Solution is infeasible`;
  this is recorded as MASTER UNKNOWN, not a mathematical infeasibility result.
  The explicit dual master is itself feasible, so that message cannot certify
  the intended full moment relaxation. Log:
  /tmp/sieve_glpk_100_25000_dualmaster.log.
* /tmp/sieve_glpk_cg_shrink.py shrinks locally violated patterns to inclusion-
  minimal positive patterns. This made matrices sparse but weakened progress
  drastically: the restricted slack was still about .405 after 67 iterations.
  PID26351 was stopped. Its prefix seed omitted the dense initial prefixes;
  restoring those prefixes makes a large difference to the restricted master.
* /tmp/sieve_glpk_cg_balanced.py restores all initial prefixes and shrinks
  violations while retaining 25% of their original value. This gives a better
  balance between matrix size and cut strength. PID26524 was still running at
  this entry; log /tmp/sieve_balanced_100_25000.log. At iteration28 the restricted
  slack was .01251749, with ~31-second master solves and ~664MB RAM. State and
  dual output use the prefix /tmp/sieve_balanced_100_25000 (separate from older
  /tmp/sieve_glpk files).

All these calculations are floating-point diagnostics, not Lean proofs.
Only an independently valid global separation bound can establish infeasibility
of the full moment relaxation. Feasibility does not construct an interval cover.
The earlier fully separated numerical k30 and k50 duals have coefficient signs
exactly (-1)^degree, as in inclusion-exclusion; mixing such certificates cannot
improve their absolute L1 ratio through sign cancellation.

Balanced-pricing outcome: PID26524 finished at iteration32, after 638.75 seconds.
Restricted slack = 5.49e-13, with 5286 positive nonempty atom masses, so the
rounded moment relaxation at k100,m25000 is NUMERICALLY FEASIBLE. Artifact:
/tmp/sieve_balanced_100_25000_feasible.json.
This is not an exact rational or kernel-checked witness, nor an actual residue
cover, and it does not settle the conjecture. No worker from this round remains
active. The original theorem in Spec.lean is unchanged and still unproved.

# Positional pattern-packing investigation

STILL NO proof or disproof of erdos_970. Spec.lean remains unchanged at 2179 lines,
with its sole original sorry at line 2177. The following are DEVELOPMENT FILES.
They all compile, their oleans are built, and printed axioms are only propext,
Classical.choice, Quot.sound. No native_decide was used.

## New verified Lean results (364 lines across three files)

* PatternPacking.lean (158 lines), namespace Erdos970.PatternPacking:
  - pattern_union_card_le_one: if every pair A,B in a family (including equal
    members) has product(A intersection B) >= m, at most one position below m
    can hit every prime of some member of that family.
  - three_of_four_card_le_one: for four primes whose pairwise products >= m,
    at most one position hits at least three.
  - three_of_four_indicator and three_of_four_polynomial_sum_le_one:
    threshold >=3 of4 equals sum of the four triple monomials minus three times
    the full-block monomial. Its interval sum is <=1.
  - fourPatternDoubleCount_bounds: a small half-weight nonempty population on
    {2,3,5,7}, total mass2, obeys every separate rounded moment bound.
  - actual_three_pattern_packing: its patterns {2,3},{2,5},{3,5} belong to a
    family that can occur at at most one actual position in length2. Their
    synthetic half-weights instead sum to3/2. This illustrates an additional
    constraint, NOT a disproof of the main conjecture.

* PatternPackingGeneral.lean (149 lines):
  - all_but_one_card_le_one: for a block P with >=2 primes, if every product of
    |P|-2 block primes is >=m, at most one position hits >=|P|-1 block primes.
  - all_but_one_indicator: for |P|=n+1, threshold >=n is sum of all n-subset
    monomials minus n times the full-block monomial.
  - separated_card_le_ceil: minimum spacing d gives cardinality <=ceil(m/d).
  - pattern_union_card_le_ceil: common products >=d give that exact packing budget.

* PatternPackingCriterion.lean (57 lines):
  - weighted_pattern_union_sum_le.
  - survivor_of_packing_certificate: if a rounded sieve polynomial is bounded
    above, on covered positions, by a nonnegative weighted sum of packing
    indicators, and its rounded main exceeds the packing budget, a survivor
    exists. The positivity hypothesis remains UNPROVED uniformly in k.

IMPORTANT: independent virtual OR hits do not preserve positional packing.
The earlier reference-marginal transfer theorem cannot automatically be applied
with these new constraints. A certificate at the first k primes would need a
separate argument before yielding a bound for arbitrary sets of k primes.

## Numerical diagnostics, all at k100,m25000

1. The original balanced population has a pairwise-incompatible family of 127
   dense patterns with total mass ~5.51457, although a real interval allows at
   most one such position. Artifact /tmp/sieve_clique_violation_100_25000.json.
   The common-product tests used exact integer arithmetic, but the masses are
   numerical and the large family has not been Lean encoded.

2. /tmp/packing_four.cpp and executable /tmp/packing_four enumerate all four-
   element blocks in the 63-prime tail starting at index37 (prime163). All their
   pair products exceed25000. Input /tmp/packing_four_input.txt, initial cuts
   /tmp/packing_four_cuts.txt. Found299 violations, maximum mass1.3604876.

3. /tmp/sieve_glpk_cg_packing.py adds those threshold-three cuts, then uses
   column generation plus further exhaustive four-tail-cut scans. It finished
   after154 seconds, with307 cuts and a numerical feasible population of5186
   atoms. /tmp/sieve_packing_100_25000_feasible.json. It satisfies ALL four-tail
   cuts numerically, but this is not full positional feasibility or an actual cover.

4. /tmp/packing_local.py searches all-but-one blocks of sizes4 through10 by
   local swaps, checking exact integer validity prod(smallest b-2 primes)>=m.
   It found96 new cuts for the previous population, maximum mass about1.59017.
   /tmp/packing_generic_initial.json, /tmp/packing_local_first.log.

5. /tmp/sieve_glpk_cg_generalpacking.py added these and further heuristic cuts.
   Finished at iteration32 in407.53 seconds, with1192 valid packing cuts and
   5306 positive atoms. Log /tmp/sieve_generalpacking_100_25000.log; outputs
   /tmp/sieve_generalpacking_100_25000_{feasible,state}.json.
   All four-tail cuts were exhaustively checked; other block sizes only had
   LOCAL separation. 'No new heuristic cuts' is NOT a global certificate for
   every possible packing inequality. Numerical audit: total-mass error7.3e-12,
   maximum rounded moment violation1.64e-11, packing violation7.1e-13.

6. Dense patterns are not necessary for numerical moment feasibility.
   /tmp/sieve_glpk_cg_bounded8.py restricts every atom to size<=8, uses single-
   coordinate and swap local pricing, and adds cardinality<=8 to MILP pricing.
   Finished at iteration17 in160.38 seconds, with5117 positive atoms.
   /tmp/sieve_bounded8_100_25000_feasible.json. Maximum degree8; mass at degree8
   about134.979. Its rounded moment errors are <=1.1e-11. It also happens to
   satisfy every one of the final1192 cuts from the other run, but violates
   other locally found packing cuts. Thus removing the earlier 20+-hit patterns
   by itself does not resolve the relaxation obstruction.
   A positive restricted optimum with degree8 separation would only establish
   DEGREE-8 model infeasibility, NOT full-model infeasibility. This run instead
   achieved a feasible population, which is valid for the full moment relaxation.

7. packing_local.py now also accepts a spacing budget: valid if
   budget * prod(smallest b-2 block primes) >=m. It searched budgets1..6 on the
   degree8 population and found33 new cuts, including a budget2 violation.
   /tmp/packing_spacing_initial.json, /tmp/packing_spacing_first.log.
   No LP run incorporating these spacing-budget cuts has been performed.

Audit script: /tmp/packing_feasibility_audit.py <artifact-prefix>.
All populations above are FLOATING POINT, not exact rational or kernel-checked
witnesses, and none constructs actual residue classes on an interval.
All workers from this investigation have finished; no known active worker remains.

## Remaining mathematical obstacle

No uniform quadratic positivity theorem was obtained. The new packing framework
is genuinely stronger than separate rounded moment constraints, but its finite
numerical feasibility results do not establish or refute quadratic growth.
A fixed improvement in an appropriate uniform upper-sieve density estimate might
break the usual critical-level cancellation, but no such improvement was proved.
In particular, do not infer a main theorem from the new finite packing lemmas.

# Quantitative packing transfer (latest completed formal development)

Two further development files compile, with only permitted axioms:

* PolynomialBoostError.lean (imports RecursiveSieveTransfer):
  - abs_average_le_average_abs, average_abs_le_of_bound,
    average_change_le_support_sum;
  - boosted_polynomial_interval_error: virtual independent OR hits retain the
    ordinary coefficient-L1 moment-error bound;
  - polynomial_boost_remainder_change: for a polynomial P supported on B,
    the change in its interval remainder under OR-boost probabilities a_i has
    absolute value at most 2 ||P||_1 sum_{i in B} a_i.
    This follows by restricting monomial supports for each added pattern and
    observing that the remainder is unchanged when no coordinate in B is added.

* PackingTransfer.lean (imports PolynomialBoostError):
  - boostProbability q q' i = (q'_i-q_i)/(1-q_i), with bounds
    0 <= boostProbability <= q'_i and the required marginal identity;
  - dominating_polynomial_upper: a nonnegative packing polynomial G, supported
    on B and having actual sum <= cap, has boosted sum bounded above by
      cap + m E_{q'}G + 2 ||G||_1 sum_{i in B} q'_i;
  - survivor_from_dominating_packing_polynomials: a base polynomial F bounded
    above on all nonempty patterns by sum_u w_u G_u, w_u >= 0, yields a survivor
    if
      ||F||_1 + sum_u w_u [cap_u + m E_{q'}G_u
                           + 2 ||G_u||_1 sum_{i in B_u} q'_i]
        < m E_{q'}F.

This is quantitative transfer, NOT exact preservation of packing under OR hits.
In particular the mean-increase and support-error terms must not be omitted.
No uniform family satisfying the displayed positivity inequality at m = C k^2
has been constructed. The theorem erdos_970 in Spec.lean remains UNSOLVED.

Potential indexed-reference instantiation remains unwritten. It would combine
indexed pattern packing with nth_prime_le_sorted and padding prime sets to size
k. Even if completed, this would be another conditional reduction, not the
missing uniform positivity proof.

A possible sharper transfer for a factor avoidSmall * Q(large coordinates) was
considered but has NOT been proved. Its motivation is that OR hits decrease the
avoidance factor, so a one-sided change estimate might charge only the large
coordinates. This idea alone supplies no uniform positive sieve certificate.

# Interval-aware recursive sieve (new verified development)

The main conjecture remains UNSOLVED. Spec.lean has not been modified in this round.

## Verified files

* IntervalRescaling.lean:
  - progressionLength, lt_progressionLength_iff, residueClass_eq_image,
    progressionLength_eq_card, progressionLength_bounds;
  - exists_affine_residue: a+p*j == r (mod q) is equivalent to j == s (mod q)
    whenever p and q are coprime;
  - count, firstHitCount, count_mono_length;
  - firstHitCount_rescale: the intersection with the next prime class is an
    actual interval sieve by the preceding moduli after affine rescaling.
    Its integer length is between floor(m/p) and ceil(m/p).

* IntervalRecursiveSieve.lean:
  - count_succ_partition, count_firstHit_tail;
  - intervalEnvelope p b lo hi keep k m, a computable natural-valued recurrence;
  - intervalEnvelope_sound for positive pairwise coprime actual moduli;
  - survivor_of_positive_intervalEnvelope.

With base prefix b and verified base lower/upper bounds L_b,U_b, the recurrence is
  L_k(n) = max(0, L_b(n) - sum_{b<=i<k} U_i(ceil(n/p_i))),
  U_k(n) = U_b(n) - sum_{b<=i<k} L_i(floor(n/p_i)).
The lower branch may be discarded by the keep flag. The formal upper subtraction
is natural subtraction; soundness proves the needed inequalities without an
assumption of nonnegative untruncated arithmetic.

* IntervalRecursiveExample.lean:
  - first_fifty_interval_envelope_positive, by decide +kernel;
  - first_fifty_interval_survivor, an actual survivor below5000 for the listed
    first fifty primes and every indexed choice of residues.
  The example uses b=0, lo=hi=id, and keep(k,n)=(k<n).

All three files compile and have built oleans. Printed axioms are exactly from
[propext, Classical.choice, Quot.sound]. No native_decide was used.

IMPORTANT: the new first-fifty result is NOT jacobsthalFunction 50 <=5000.
It bounds a SPECIFIED prime set only. The older, separately verified uniform
jacobsthalFunction 50 <=15000 remains the relevant arbitrary-set result.
Neither this example nor the new conditional recurrence settles Erdős970.

## Diagnostic implementation

/tmp/interval_firsthit.cpp and /tmp/interval_firsthit implement this integer
recurrence for the first k primes, with optional exact small-wheel base counts.
Memoization and pruning make it much cheaper than naive expansion. No numerical
output beyond the separate Lean example has been kernel checked.

With exact wheel base {2,3,5}:
  k100,   m10000:      lower55;
  k1000,  m2000000:    lower9339;
  k10000, m400000000:  lower1866083;
  k100000,m40000000000:lower51993517;
  k1000000,m4000000000000: lower0.

Logs /tmp/interval_firsthit_100000.log and _1000000.log.
The million-prime job reached its time limit after the ratio4 result; subsequent
ratios were NOT completed. There are no known active workers from this round.

These improve finite diagnostics substantially but do NOT prove a uniform ratio.
The raw integer envelope has no proved transfer from the first primes to arbitrary
larger primes. Independent OR hits do not retain the interval-rescaling property.

## Continuous transfer idea, not yet formalized

A possible valid replacement is to use convex lower and concave upper envelopes.
The sharp residue length error is
  |c - n/p| <= 1 - 1/p,
not merely <=1. Under an OR boost a=(q'-q)/(1-q), the mixture of an interval of
length n and its progression of length c has mean between
  (n+1)q' - 1 and (n-1)q' + 1.
Jensen plus monotonicity would therefore support the real recurrence
  L_k(x)=max(0, x - sum_i U_i(1+(x-1)q_i)),
  U_k(x)=x - sum_i L_i((x+1)q_i-1),
with lower functions extended by zero on negative inputs. Concavity, convexity,
monotonicity, and the full boost-transfer theorem have NOT been proved in Lean.
They must not be inferred from the integer recurrence's soundness theorem.

/tmp/continuous_interval_sieve.cpp and executable provide FLOATING-POINT
illustrations, not verified statements. For base0 or exact convex/concave parity
base, k10000 gives zero at ratio5 and positive ~137392 at ratio6. This still offers
no proof of uniform quadratic positivity.

# Continuous interval transfer (new completed formal development)

The earlier section's proposed convex/concave transfer is now PROVED in five
new development files. This closes the transfer gap for the continuous envelope,
NOT for the raw integer envelope, and does NOT settle uniform quadratic growth.
Spec.lean is unchanged and erdos_970 remains UNSOLVED.

## 1. ContinuousIntervalEnvelope.lean

Definitions clip, Regular, stepLower, stepUpper, envelope, density.
The continuous recursion is written in successor form:
  L_0(x)=max(0,x), U_0(x)=x;
  L_{k+1}(x)=max(0, L_k(max(0,x))
                    - U_k(1+(max(0,x)-1)q_k));
  U_{k+1}(x)=U_k(x)-L_k((x+1)q_k-1).
For x>=0 this agrees with the first-hit form used in the earlier C++ diagnostic,
because upper functions are nonnegative and repeated lower clipping is harmless.
That equivalence to the C++ loop has not separately been formalized; the Lean
finite evaluations use the proved successor recursion directly.

Verified:
  - clip_regular and clip_lipschitz;
  - Regular.step;
  - envelope_regular, for 0<=q_i<=1;
  - lower_at_card_zero and lower_zero_of_le_card.
The regularity package proves global convexity and monotonicity of L, vanishing
on negative inputs, concavity and monotonicity of U on [0,infinity), U(0)=0,
  L(y)-L(x) <= density(k)*(y-x),
  U(y)-U(x) >= density(k)*(y-x) for 0<=x<=y,
where density(k)=prod_{i<k}(1-q_i).
The lower envelope vanishes for every x<=k. Thus pruning is justified without
assuming an unproved gap bound or an empirical zero test.

## 2. ContinuousIntervalTransfer.lean

Verified:
  - quotient_sandwich_sharp: floor/ceiling interval lengths c satisfy
      (m+1)/p-1 <= c <= 1+(m-1)/p;
  - boost_bounds and boost_identity, for a=(Q-q)/(1-q);
  - mixture_sandwich: the mixture a*m+(1-a)*c lies between
      (m+1)Q-1 and 1+(m-1)Q;
  - normalization and its nonnegativity;
  - envelope_normalized_bound;
  - survivor_of_positive_envelope.

Main bound: if the actual moduli p_i>1 are pairwise coprime and
  1/p_i <= Q_i <=1,
then the reference envelope at Q bounds
  [prod_{i<k}(1-boost(1/p_i,Q_i))] * actual_survivor_count.
Its proof combines actual interval rescaling with Jensen's inequality, rather
than incorrectly pretending OR hits preserve exact interval structure.
Positive reference lower envelopes therefore force actual survivors.

## 3. ContinuousIntervalRational.lean

Computable fastEnvelope over any linearly ordered field, using the proved
zero-for-x<=k pruning rule. Verified fastEnvelope_eq over the reals,
fastEnvelope_congr, cast_fastEnvelope, and real_positive_of_rational.
No native evaluator or extra axiom is used.

## 4. ContinuousIntervalReference.lean

referenceMarginal(i)=1/(ith prime) over the rationals, and ReferencePositive.
Verified sorted-prime instantiation and padding to exactly k primes:
  survivor_of_referencePositive;
  isJacobsthalBound_of_referencePositive;
  jacobsthalFunction_le_of_referencePositive.
This is a genuine transfer to arbitrary prime sets, but requires the explicitly
stated finite numerical positivity hypothesis.

## 5. ContinuousIntervalExample.lean

The first100 primes are explicitly listed and identified with Nat.nth Nat.Prime
using kernel-checked primality and counting facts.
Two positive rational evaluations were checked with decide +kernel:
  k50,m5000 and k100,m25000.
Consequently the following UNIFORM finite bounds are proved:
  jacobsthalFunction_fifty_le_five_thousand : jacobsthalFunction 50 <=5000;
  jacobsthalFunction_hundred_le_twenty_five_thousand :
    jacobsthalFunction 100 <=25000.

These supersede the earlier uniform h(50)<=15000 bound. In contrast to the
previous IntervalRecursiveExample, these do concern arbitrary prime sets.
They still do not imply a bound with one constant for every k.

All five files compile, have built oleans, and printed axioms use only
propext, Classical.choice, Quot.sound. No sorry/admit/native_decide appears in them.

## Remaining obstacle

There is still NO proved D such that ReferencePositive k (D*k^2) for every k>0,
nor any actual counterexample family with unbounded h(k)/k^2. The previous
floating diagnostics (for example zero at k10000,ratio5 and positive at ratio6)
are consistent with continuing logarithmic losses and cannot establish a fixed
quadratic constant. No general quantitative positivity argument was found in
this round. Do not submit the finite bounds as a proof of the main conjecture.

# Ordering and wheel-seed follow-up

Two new files compile and their printed axioms are only propext,
Classical.choice, Quot.sound:

* ContinuousIntervalOrdering.lean: for a Regular seed and 0 <= q <= p <= 1/2,
  applying p before q improves both continuous interval envelopes. The lower
  comparison uses B_p(A_q(x))-B_q(A_p(x))=2(p-q); the upper comparison uses
  A_p(B_q(x))-A_q(B_p(x))=-2(p-q). The upper proof needs p<=1/2. Dominates.step
  propagates improvement through subsequent stages.
* ContinuousIntervalSorting.lean: sorting any list of marginals in [0,1/2]
  in decreasing order dominates its original order. Thus reordering this
  particular recurrence cannot improve on increasing-prime order. This is NOT
  a limitation theorem for every possible sieve.

Unverified diagnostic program /tmp/wheel_seed_sieve.cpp computes exact circular
weighted interval excesses for small primorial wheels, then forms floating-point
convex/concave affine hulls and runs the continuous recurrence. It sampled 32
rational slopes on each side of the wheel density. For seed8, Q=9699690 and
phi(Q)=1658880; hulls have 8 lower and 14 upper lines. Selected diagnostics:
  seed8 k1000: ratio1 zero; ratio2 lower~10390.23;
  seed8 k10000: ratio2 zero; ratio2.5 lower~363525.20;
  seed8 k100000: ratio2 zero; ratio3 lower~4657810.09;
  seed3 k100000: ratios3,4,5 zero; ratio6 lower~49084057.05.
Here ratio means m/k^2. Logs are /tmp/wheel_seed_10000_8.log,
/tmp/wheel_seed_100000_8.log, /tmp/wheel_seed_100000_3.log.
These are finite diagnostics, not Lean-verified certificates or evidence of a
uniform constant. Exact wheel seeds require those primes to be present. A valid
arbitrary-prime route could adjoin missing prefix primes, but a generalized
seeded transfer and a uniform growing-seed estimate have not been proved.

Spec.lean remains unchanged with its original sole sorry. The conjecture is
still UNSOLVED. No complete proof or disproof has been submitted.

# Partition closure follow-up

NEW VERIFIED: ContinuousIntervalPartition.lean, with built olean.
Regular.partition proves, for every finite family of nonnegative lengths x_i,
  sum_i L(x_i) <= L(sum_i x_i),
  U(sum_i x_i) <= sum_i U(x_i).
The proof uses Jensen with coefficients x/(x+y), y/(x+y) to obtain
superadditivity of a convex function vanishing at zero, and its concave dual.
Printed axioms: propext, Classical.choice, Quot.sound.
Thus arbitrary finite subdivisions, using just the existing real envelopes,
cannot improve their values at the total length. This statement does NOT
include additional rounding or arithmetic information about survivor counts.

Integrality caution: the reference transfer bounds alpha * count, with real
alpha = normalization, not the integer count itself. Rounding this product as
though it were an integer is invalid. Actual-prime interval counts are integral,
but their stronger raw integer recurrences still lack a general reference-prime
transfer. No new asymptotic estimate was obtained from integrality in this round.

Possible future direction, NOT implemented or proved here: interpolate the
natural-length values of each convex lower/concave upper envelope linearly
between consecutive integers after each stage. This should improve the real
extension without changing its bounds at natural lengths, and would need a new
regularity/transfer proof. It is distinct from rounding normalized count values.
There is currently no evidence or proof that it supplies uniform quadratic
positivity, so it must not be treated as resolving the main obstacle.

Spec.lean is still unchanged: original import at line1, original erdos_970 at
line2175, sole sorry at line2177. No proof submission has been made.

# Lattice chord-patched interval sieve (new verified development)

The original conjecture remains UNSOLVED. Spec.lean has not changed.
Five new files, 492 lines total, compile and have built oleans. All printed
axioms are propext, Classical.choice, Quot.sound. No sorry/admit/native_decide
occurs in these files.

## ContinuousIntervalChord.lean

Defines chord f a x = f(a)+(x-a)*(f(a+1)-f(a)), and for natural a:
  patchLower L a x = max(L(x), chord L a x),
  patchUpper U a x = min(U(x), chord U a x).
Verified:
  chord_le_outside, le_chord_outside;
  patchLower_nat, patchUpper_nat;
  patch_dominates;
  Regular.patch.
A chord patch changes only the real extension inside a unit lattice cell and
preserves every natural-length value. It preserves the full Regular package,
including the common density slope controls. This is NOT rounding the real
normalized survivor count as though it were an integer.

## ContinuousIntervalCertificate.lean

Defines IntervalBounds L U alpha p k as the normalized bounds at all natural
lengths and all forbidden residues.
Verified:
  IntervalBounds.patch;
  IntervalBounds.step.
The latter extracts the one-stage Jensen/rescaling argument for ANY regular
certificate, not just the original continuous recurrence. The next normalization
is alpha*(1-boost(1/p_k,Q_k)); the actual p_i remain pairwise coprime and may be
larger than the reference moduli.

## ContinuousIntervalPatched.lean

Defines chordPatches (finite list of cells) and patchedEnvelope Q cells k, which
applies arbitrary finite patches after each ordinary sieve stage.
Verified:
  Regular.chordPatches, IntervalBounds.chordPatches;
  chordPatches_dominates;
  patchedEnvelope_regular;
  patchedEnvelope_dominates;
  patchedEnvelope_normalized_bound;
  survivor_of_positive_patchedEnvelope.
Thus this stronger recursion has a rigorous arbitrary-larger-modulus transfer.
The last theorem still needs an explicit positive lower-envelope hypothesis.

## ContinuousIntervalInterpolation.lean

Verified:
  le_chord_inside, chord_le_inside;
  chord_nat_congr, chordPatches_nat, chordPatches_contains_chord;
  chordPatches_eq_chord_on_cell;
  chordPatches_optimal_on_cell;
  patched_lower_at_card_zero, patched_lower_zero_of_le_card.
On every selected cell, the patch result is exactly the linear interpolation of
its original natural endpoint values. It is the maximal convex lower extension
and minimal concave upper extension among regular functions with those same
natural values, ON THAT CELL. This is not optimality among all sieve methods.
The previous pruning rule x<=k -> lower=0 also remains valid.

## ContinuousIntervalChordExample.lean

A small exact kernel-checked example with q=(1/2,1/3,1/5):
  unpatched lower at k3,x19/2 = 0;
  patched lower at k3,x19/2 = 1/20,
using only a patch on cell [9,10] after stage3. This confirms a genuine strict
improvement at a noninteger recursive argument, not an asymptotic result.

## Unverified floating diagnostic

/tmp/lattice_interval_sieve.cpp and its binary implement interpolation at integer
lengths after every stage, using a first-hit expansion and cached integer-length
values. Float arithmetic is long double. Diagnostic logs:
  /tmp/lattice_interval_10000.log
  /tmp/lattice_interval_100000.log
Results (ratio=m/k^2):
  k10000 ratios3,4,5 -> zero;
  k10000 ratio6 -> lower~138146.1727 (old continuous ~137392);
  k10000 ratio8 -> lower~1900557.7448;
  k100000 ratios5,6,8 -> zero;
  k100000 ratio10 -> lower~83801420.6481;
  k100000 ratio12 -> lower~208605528.2359.
The mathematical patch/transfer and pruning are proved, but equivalence of this
C++ first-hit evaluator to the Lean patchedEnvelope, and these numeric outputs,
have NOT been kernel checked. Do not call them Lean certificates. There is still
no proof that the patched lower envelope is positive at D*k^2 for one fixed D
and all k. No computational workers remain.

The small primorial adjacent-gap scan through k8 was inadvertently repeated;
it agrees with the earlier k9 scan. The previous broad scans already checked
this necessary condition for LargestPrimeIncrement, without a proof or a
counterexample. Do not repeat them without a new structural reason.

Final audit for this round: Spec still has its sole import at line1, original
erdos_970 at line2175, and sole sorry at line2177. No submit_proof call was made.

# Aggregate first-hit investigation (no new proof)

Spec is still UNSOLVED and unchanged. This round investigated a genuinely
joint constraint: all first-hit progressions are cut from one parent interval,
whereas the envelope recurrence bounds their sizes separately. No new uniform
bound, Lean theorem, or disproof was obtained.

A standard weighted large-sieve estimate does not close this gap. Schematically,
for a fixed parent set S in an interval of length m, selected residue counts
N_p, prime cutoff P, and mu=sum_p 1/p, it gives the candidate aggregate bound
  sum_p N_p <= |S|*mu + sqrt(mu*(m+P^2)*|S|)
(up to harmless constants). This follows by the weighted variance version and
Cauchy-Schwarz; it was NOT added as a proved Lean lemma in this round.
For the relevant tail z~k through P~k log k, mu~loglog k/log k. To make this
particular bound smaller than |S| would require roughly
  |S| > mu*(m+P^2)/(1-mu)^2 ~ k^2 log k loglog k,
which is already larger than m~k^2. Thus even the weighted version is too weak
without additional information from the preceding sieve. This is a limitation
of this estimate, NOT a theorem ruling out every aggregate approach.

The more promising but still UNPROVED missing relation is between an unusually
small parent survivor count and the simultaneous sizes of its many rescaled
children. Child counts individually can be relatively large; treating parent
and child extrema as independent is precisely the existing loss. No uniform
relative-removal bound or aggregate cancellation theorem has been established.
Do not assume an O(1/p) relative-removal estimate; earlier investigations already
showed that such shortcuts fail in general.

No jobs remain running and no submit_proof call was made. The sole sorry in
Spec.lean is still at line2177, under the unchanged erdos_970 statement.

# Cardinality-bootstrap investigation (no new proof)

Still no proof/disproof of erdos_970 and no change to Spec.lean.
The existing modular/parity/two-survivor reductions and the exact fresh-prime
cover-budget criterion were reviewed for a bootstrap from finite bounds or a
strong induction on the number of primes.

The exact budget criterion already says that a bound at j primes forces at
least j-b+1 survivors for any b-prime prefix (b<=j). Under a hypothetical strong
induction h(j)<=C*j^2 for j<k, at length C*k^2 this supplies at least k-b
survivors after retaining b primes. By itself this does not prevent the remaining
k-b classes from covering those survivors. Ordinary subdivision gives still
weaker count information in this regime. No valid cardinality-saving recurrence
was found.

The fixed-set LargestPrimeIncrement hypothesis is still unproved. Its modular
separation formulation, the two-survivor test when p exceeds an appropriate gap
bound, and the exact parity-doubling lemma are reductions, not estimates proving
the hypothesis. Existing adjacent-gap scans should not be repeated without a
new reason. Arbitrary deletion doubling remains false as recorded earlier.

A proposed bound for higher consecutive gap sums of the shape
  j_s(P) <= j_1(P) + O(s*log(|P|))
would give useful near-mean survivor counts, but cannot simply be assumed.
In particular a global-in-length discrepancy claim is much stronger than the
short-interval information needed here. No such gap-sum theorem was established.
The older research notes already identify this issue; this round found no way
around it. No new Lean theorem or numerical certificate is claimed.

Spec audit remains: one import at line1, original theorem at line2175, sole
sorry at line2177. No submit_proof call or ongoing computational worker.

# Quantitative lattice-patch gain (new verified local estimate)

NEW FILE: ContinuousIntervalPatchGain.lean. It compiles, its olean is built, and
printed axioms are only propext, Classical.choice, Quot.sound. No sorry/admit or
native_decide occurs in it. Spec.lean remains UNSOLVED and unchanged.

Definitions/results:
* UpperLip D U: U(y)-U(x) <= D*(y-x) for 0<=x<=y.
* Regular.lower_chord_gain: chord L a x <= L(x)+d/4.
* Regular.density_le_upperLip: d<=D.
* Regular.upper_chord_gain: U(x)-(D-d)/4 <= chord U a x for a,x>=0.
* chordPatches_lower_le, le_chordPatches_upper: static-chord bounds survive
  arbitrary finite patch lists, using preservation of the natural endpoints.
* Regular.chordPatches_gain: for a WHOLE SINGLE BATCH of patches, at x>=0,
    0 <= L_patched(x)-L(x) <= d/4,
    0 <= U(x)-U_patched(x) <= (D-d)/4.
  There is no factor for the number of patched cells.
* UpperLip.patch, UpperLip.chordPatches, UpperLip.step.
* patchedEnvelope_upperLip: every upper envelope generated by the patched
  recursion has slope at most1 (for reference marginals in [0,1]).

The quarter comes from t*(1-t)<=1/4. The proof combines endpoint monotonicity
and one-sided slope inequalities; no heuristic numerical estimate is involved.
IMPORTANT: this bounds one interpolation batch. Improvements can propagate and
interact through later recursive stages. NO global bound on the total gain, NO
asymptotic failure theorem for the patched recursion, and NO fixed quadratic
positive certificate was proved. Do not overstate this local result.

The accompanying local cover-replacement investigation produced no new saving.
Deleting one retained class and replacing it by another does not yield a useful
constraint for an empty-survivor core. Deleting two classes and covering all
newly exposed positions with one fresh class would contradict optimality, but
no reason that such a replacement must exist at quadratic length was found.
The existing two-private-points condition remains insufficient, as already
shown by the verified finite cover in PrivateCoverExample.lean.

Final audit: Spec retains import FormalConjecturesUtil, the unchanged erdos_970
statement at line2175, and its sole sorry at line2177. No submit_proof call.

# Exact fixed-prefix seed transfer (new verified development)

The old seed-transfer gap is now CLOSED. The asymptotic positivity gap is NOT.
Spec.lean is still unchanged and erdos_970 remains UNSOLVED.

Four new files compile and have built oleans; all printed axioms are only
propext, Classical.choice, Quot.sound. No sorry/admit/native_decide in them.

## ContinuousIntervalSeeded.lean

Definitions seedRun, seedDensity, seedScale. seedRun starts with any regular
certificate for b ACTUAL prefix moduli and runs t further stages, including
optional lattice chord patches. seedScale normalizes only the tail.
Verified:
  seedRun_regular;
  seedScale_nonneg;
  seedRun_normalized_bound;
  survivor_of_positive_seedRun.
The seed must bound the actual prefix for every residue choice. Tail moduli may
be arbitrary larger coprime moduli satisfying the stated marginal bounds.

## ContinuousIntervalSeedForcing.lean

Verified:
  sorted_prime_prefix_eq: if a sorted prime set contains the first b primes,
    those primes are exactly its first b entries;
  IntervalBounds.congr_prefix;
  isJacobsthalBound_of_seedRun;
  jacobsthalFunction_le_of_seedRun.
To handle any original set of at most k primes, adjoin the first b primes and
pad to b+k primes. The actual prefix then equals the verified seed prefix.
The k tail entries dominate reference primes indexed b through b+k-1, so
seedRun with b prefix primes and k TAIL stages gives a uniform bound for the
original k-prime problem. This pays the b additional primes explicitly; it does
not replace arbitrary actual primes by a wheel without justification.
Positivity at the desired length is still an explicit hypothesis.

## ContinuousIntervalAffineSeed.lean

Defines
  affineLower d E x = max(0,d*x-E),
  affineUpper d E x = min(x,d*x+E).
affineSeed_regular proves Regular d for 0<=d<=1 and E>=0.
No bound on E for growing wheel size is asserted.

## ContinuousIntervalWheelThirty.lean

A kernel-checked finite computation over all residue choices modulo 2,3,5 and
lengths 0 through30 proves
  4*m <=15*count+24 and 15*count<=4*m+24,
  count at length30 =8.
An exact period recurrence count(m+30)=count(m)+8 extends these inequalities to
EVERY natural interval length. The explicit moduli are then identified with the
first three primes via Nat.nth_count and kernel-checked primality/counting.
Verified:
  wheelThirty_regular;
  wheelThirty_bounds;
  isJacobsthalBound_of_wheelThirty.
The seed has density4/15 and absolute discrepancy8/5. The last theorem is a
UNIFORM arbitrary-prime-set criterion when its seeded positive-run hypothesis
is supplied. It is not a claimed uniform asymptotic bound or a new finite
h(k) numerical bound. No seedRun positivity computation was added this round.

Remaining obstacle: no uniformly effective growing-seed estimate, nor a proof
of positivity at D*k^2 for one fixed D and all k. Earlier wheel-seed floating
outputs remain diagnostics (not kernel certificates), and their use for an
original k-prime set must now account for the b extra prefix stages as above.
Do not reuse an old total-k wheel diagnostic as a uniform h(k) bound unchanged.

Spec audit: one original import at line1, original theorem at line2175, sole
sorry at line2177. No proof submission or ongoing computational worker.

# Fixed-seed dilation robustness (new verified development)

Spec.lean remains unchanged; erdos_970 is still UNSOLVED.

Two new files, 338 lines total, compile and have built oleans:
  ContinuousIntervalDilation.lean           155 lines
  ContinuousIntervalSeedRobustness.lean     183 lines
All printed axioms are only propext, Classical.choice, Quot.sound.
Neither new file contains sorry, admit, or native_decide.

## ContinuousIntervalDilation.lean

Defines the deliberately coarse real error budget
  E_0=0, E_{k+1}=2*E_k+1.
Verified:
  coarseError_nonneg;
  density_le_one;
  envelope_affine_bound:
    L_k(x) >= density(q,k)*x - E_k for every real x,
    U_k(x) <= density(q,k)*x + E_k for x>=0;
  envelope_upper_le_input;
  envelope_lower_antitone (in stage number, for fixed x>=0);
  Dominates.trans;
  Regular.dilation_step;
  seedRun_dilation_dominates.

The one-stage dilation theorem uses c>=1 and 0<=q<=1:
  A_q(c*x) <= c*A_q(x),
  c*B_q(x) <= B_q(c*x).
Consequently the dilation of an ordinary step dominates the ordinary step of
its dilated input functions. Prefix dominance propagates through all later
UNPATCHED stages.

## ContinuousIntervalSeedRobustness.lean

Verified unavoidable small-length constraints for any actual prefix certificate:
  IntervalBounds.lower_at_card: L(b)<=0
    (choose forbidden indexed residues r_i=i);
  IntervalBounds.one_le_upper_one: U(1)>=1 if all p_i>1
    (choose forbidden residues r_i=1, so position0 survives).

Regularity then implies
  L(x) <= d*max(0,x-b),
  min(x,d*x+1-d) <= U(x) for x>=0.

Verified regularSeed_dilation_exists. If b>0, 0<d=density(q,b)<1,
Regular d L U, L(b)<=0, U(1)>=1, then a single finite c>=1 satisfies
  L(x) <= L_original(b,c*x)/c,
  U_original(b,c*x)/c <= U(x) for x>=0.
The explicit choice is
  c=max(1, max(E_b/(d*b), E_b/(1-d))).

Verified fixedSeed_dilation: if the seed is a valid actual b-prime certificate,
the same constant c works at EVERY unpatched tail stage t:
  L_seedRun(t,x) <= L_original(b+t,c*x)/c,
  U_original(b+t,c*x)/c <= U_seedRun(t,x) for x>=0.

Verified quadratic_positive_of_fixedSeed: if such a fixed seed yields positivity
at D*t^2 for every positive tail length t and one D>0, then the ordinary original
recurrence yields positivity at C*k^2 for every k>0 and one C>0. Finitely many
prefix indices are absorbed explicitly using the positive value of the original
stage-b lower envelope at M=(E_b+1)/d and stage antitonicity.

IMPORTANT LIMITS:
* This is a comparison/reduction, NOT a proof of either positivity hypothesis.
* It does NOT prove that the original recurrence fails at every quadratic scale.
* It does NOT prove or disprove erdos_970.
* It applies only to cells := fun _ => [] in the TAIL. An arbitrary finite amount
  of earlier valid seed refinement is permitted, but later repeated chord patches
  are not covered. Scaling changes the lattice, so a naive patched extension is
  invalid.
* The constant c depends on b and is not controlled uniformly for growing seeds.

A subsequent structural reconsideration (no new formal claim) did not establish
LargestPrimeIncrement or a quadratic optimal-core budget lower bound. No new
finite gap scans, floating positivity scans, or counterexample searches were run.

Final audit: Spec compiles with the original sorry warning at theorem2175;
sole import remains FormalConjecturesUtil and sole sorry remains line2177.
No proof submission was made; no ongoing computational worker is known.

# Simultaneous coupled row rescaling (new verified development)

The conjecture remains UNSOLVED; Spec.lean was not modified.

New file IntervalCoupledRescaling.lean compiles, with its olean built. All printed
axioms are propext, Classical.choice, Quot.sound. No sorry/admit/native_decide.

Definitions:
  shiftedCount p s k a m: count in the translated interval a+[0,m);
  rowCount p r k d m a: old survivors below m lying in residue a modulo d.

Verified:
  exists_common_inverse: if d is coprime to each positive old modulus, choose a
    SINGLE v with d*v=1 modulo every old modulus (using their product). Pairwise
    coprimality between the old moduli is not needed for this lemma.
  affine_modEq_iff_common_inverse:
    a+d*t = r mod q iff v*a+t = v*r mod q.
  rowCount_rescale_common:
    rowCount(p,r,k,d,m,a)
      = shiftedCount(p, (j -> v*r(j)), k, v*a, progressionLength(m,d,a)).
    The transformed residue vector is independent of a; all rows are translates
    of ONE common configuration, rather than arbitrary independent configurations.
  count_succ_zero_iff_rows_zero;
  count_succ_zero_iff_coupled_rows_zero:
    a full cover after adjoining the kth class is equivalent to vanishing of the
    corresponding shifted count in EVERY row except its forbidden row, with the
    common transformed residue vector retained.

No uniform estimate for these correlated simultaneous zero conditions was proved.
In particular, the identities do not establish LargestPrimeIncrement, a quadratic
optimal-core budget lower bound, or positivity at C*k^2.

The structural investigation found no valid shortcut from pairwise intersections,
private witnesses, or generic concentration. Treating nonintersecting events as
independent/LLL-nondependent would be invalid: conditioning on avoidance of a
disjoint event increases the probability of the first event. No such inference
was used in any proof. No repeated large gap scans were run.

A tiny diagnostic evaluation of the ALREADY VERIFIED raw integer recurrence at
known small primorial gap lengths gave:
  (k,m,lower)=(1,2,1),(2,4,1),(3,6,1),(4,10,1),
              (5,14,0),(6,22,0),(7,26,0),(8,34,0).
This was a Python check, not a new kernel certificate or uniform bound. No new
finite bound was claimed from it.

Spec audit: original import at1, unchanged erdos_970 at2175, sole sorry at2177.
No submit_proof call and no ongoing computational worker.

# Integer-threshold (quantum) refinement (new verified development)

The conjecture is still UNSOLVED; Spec.lean was not changed.

Four new Lean files compile with built oleans; all printed axioms are only
propext, Classical.choice, Quot.sound. No sorry/admit/native_decide in them:
  ContinuousIntervalQuantum.lean
  ContinuousIntervalQuantumIteration.lean
  ContinuousIntervalQuantumReference.lean
  ContinuousIntervalQuantumExample.lean

## Safe use of count integrality

The normalized count alpha*N is generally NOT integral. No integer rounding of
alpha*N is performed. The new proved lemma density_le_normalization gives
  d_reference <= alpha.
If L(g)>0, then the actual integer count N(g)>=1 for every residue choice.
Monotonicity gives alpha*N(m)>=d_reference for every natural m>=g.

Suppose an old affine support is
  ell(x)=s*(x-(g-1))+a,  a<=0,  0<=s<=d,
and ell(n)<=L(n) at every natural n. Set
  eta=d/(d-a),
  newLine(x)=eta*s*(x-(g-1)).
For n>=g this is the convex combination
  eta*ell(n)+(1-eta)*d,
so it is still below the normalized count. For natural n<g it is nonpositive.
Taking max(L,newLine) preserves all Regular d properties. This is a genuine
integer-threshold strengthening, not merely a lattice chord interpolation.

Verified in ContinuousIntervalQuantum:
  density_le_normalization;
  Regular.max_affine;
  quantumFactor_bounds, quantumFactor_identity;
  Regular.quantumPatch;
  IntervalBounds.normalized_ge_density_of_positive;
  IntervalBounds.quantumPatch;
  Regular.quantumSlope_bounds;
  quantum_support_nat;
  Regular.quantumIntercept_nonpos;
  quantum_cell_certificate.

The concrete support uses the chord on [g,g+1]:
  s=L(g+1)-L(g), a=L(g)-s.
If L(g-1)=0, convexity ensures a<=0. Chords lie below L at ALL natural lengths
outside their open unit cell, so this is a legitimate natural-length support
even without previously patching that cell.

## Repeated transfer and reference primes

ContinuousIntervalQuantumIteration defines quantumRefine with the explicit guard
  d>0, g>0, L(g-1)=0, L(g)>0.
If the guard fails, it leaves L unchanged.

quantumEnvelope runs an ordinary sieve step, any finite list of chord patches,
and then one guarded quantumRefine, at every stage. Verified:
  Regular.quantumRefine;
  IntervalBounds.quantumRefine;
  quantumRefine_dominates;
  quantumEnvelope_regular;
  quantumEnvelope_dominates (the original unpatched envelope);
  quantumEnvelope_normalized_bound;
  survivor_of_positive_quantumEnvelope.

ContinuousIntervalQuantumReference verifies arbitrary-prime-set uniform transfer,
with padding to exactly k primes as before:
  survivor_of_quantumReferencePositive;
  isJacobsthalBound_of_quantumReferencePositive;
  jacobsthalFunction_le_of_quantumReferencePositive.
The final positive-envelope premise remains explicit and unproved in general.

## Exact strict improvement

ContinuousIntervalQuantumExample uses q=(1/2,1/3,1/5). The original lower values
at natural lengths9,10,11 are 0,1/10,1/3. Thus s=7/30, a=-2/15, d=4/15.
The quantum patch at g=10 raises the value at the INTEGER length10 to7/45,
a strict gain of1/18. This is verified exactly, as are regularity and normalized
soundness for EVERY larger pairwise coprime triple satisfying the marginal bounds.
No new h(k) numerical bound was asserted from this example.

## Diagnostic only: automatic triggers through k=1000

Files /tmp/quantum_interval_sieve.cpp, its binary, and
/tmp/quantum_interval_1000.log implement a long-double run WITHOUT chord patches.
Each stage searches for its first positive natural length, then installs the
corresponding quantum line. Root pruning and floating trigger tests have NOT
been proved equivalent to Lean evaluation; the output is NOT a kernel certificate.

Selected diagnostic first-positive lengths:
  k100: 22882       ratio2.2882
  k200: 105843      ratio2.646075
  k500: 808794      ratio3.235176
  k1000:3726765     ratio3.726765
Ratios are length/k^2. A targeted comparison with the old unpatched floating
program gave zero at ratio3.726765 for k1000 and positive at ratio4, confirming a
modest diagnostic improvement. This was NOT an asymptotic test or proof.
The quantum first-positive integers for stages1 through20 coincided with the
old continuous ones; improvements in interior/endpoint values affect later
recursive subproblems. The k1000 run finished; no worker is still running.

Still missing: a uniform positive certificate at C*k^2, or actual residue covers
with unbounded length/k^2. The new refinement does not by itself establish either.
The earlier fixed-seed robustness theorem does not apply automatically to quantum
refinements inserted at every later stage.

Final audit: original sole import and conjecture statement in Spec unchanged;
sole sorry remains line2177. No submit_proof call.

# Quantitative Selberg re-examination (no new result)

Re-read SelbergLowerCriterion, SelbergDefect, FirstHitSelberg, the finite
orthogonal sieve construction, and Mathlib's SelbergSieve/Chebyshev APIs.
No new quantitative inequality proving positivity at C*k^2 was found.
Mathlib's SelbergSieve file supplies upper-sieve infrastructure, not the missing
uniform lower bound. The existing boundary-defect and first-hit criteria still
require their explicit main-term-versus-remainder inequalities.

No assertion was proved that ALL possible Selberg supports or coefficients fail;
the investigation only failed to produce a uniformly successful choice. In
particular, heuristic support-cutoff estimates and parity considerations were
not promoted to theorems or used to infer a disproof of the conjecture.
No new finite support optimization or repeated gap/recurrence scan was run.

No Lean file was changed in this pass. Spec still has its unchanged statement
and sole original sorry. No submit_proof call was made.

# Quantum correction localization and natural-length gain

New verified file: ContinuousIntervalQuantumGain.lean.
This is a one-step quantitative estimate, NOT an accumulated-gain estimate or
uniform quadratic proof. Spec is unchanged and still contains the original sorry.

For l=L(g), s=L(g+1)-L(g), L(g-1)=0, and density d>0, put
  b = d*s/(d+s-l).
Regularity gives 0<=l<=s<=d. The new lower support is b*(x-g+1).
Verified algebraically:
  l<=b<=s and b-l<=d/2.

Regular.quantumPatch_nat_gain proves, for EVERY NATURAL n,
  0 <= patchedL(n)-L(n) <= patchedL(g)-L(g) = b-l <= d/2.
Thus the natural-length gain is largest at g. The theorem does NOT state a
real-argument d/2 bound (that stronger claim is false in general).

quantumPatch_eq_left_of_le proves no change for real x<=g-1.
Regular.quantumPatch_eq_of_chord_ge proves no change when both
  x>=g+1 and chord(L,g,x)>=d.
If s>0 this includes x>=max(g+1,g+(d-l)/s). The explicit divided cutoff is a
mathematical restatement; the Lean theorem uses the chord inequality.

The new file compiles; printed axioms for both Regular theorems are exactly
propext, Classical.choice, Quot.sound. No claim about the uniform accumulation
of these gains through later stages has been proved. No submit_proof call.

# Structural re-examination after quantum gain bounds

Re-read IncrementReduction, TwoSurvivorReduction, ModularReduction,
GapReduction, OptimalCoverCore, PrivateCoverExample, and IntervalRecursiveSieve.
No new quantitative theorem was obtained, and no finite gap scan was repeated.

LargestPrimeIncrement still explicitly assumes the bound g+2*|P|. Its exact
modular and sufficiently-large-prime/two-survivor reformulations do not supply
that estimate. Private-position bounds do not imply nonempty survivors.
The raw integer interval recurrence remains sound for the actual prime sequence,
but no first-prime transfer was established for it in this pass.

Also considered (without claiming a theorem) a concentration/large-sieve route
for the remaining prime classes after a small-prime sieve. No uniform variance,
tail, or entropy estimate strong enough to exclude every full cover was proved.
Standard upper bounds alone do not furnish the required survivor.

No Lean file was changed in this pass; Spec retains its original statement and
sole sorry. No proof/disproof and no submit_proof call.

# Real-argument quantum correction bound

New verified file: ContinuousIntervalQuantumRealGain.lean (built olean).
Theorem Regular.quantumPatch_real_gain proves for all REAL x:
  0 <= patchedL(x)-L(x) <= (4-2*sqrt(3))*d < 9*d/16.
The constant comparison is quantum_gain_constant_bounds. No optimality claim
is formalized here, and this is NOT an accumulated or uniform quadratic bound.

Proof ingredients:
* Outside the open cell (g,g+1), the old chord supports L. Its convex-combination
  identity with the density threshold bounds the gain by d/2.
* Inside that cell put l=L(g), s=L(g+1)-L(g), t=x-g, b=d*s/(d+s-l).
  Two lower supports are l*(1+t) and l+s-d+d*t. They bound the gain by
    (s-l)*(2*d-s-l)/(d+s-l).
  The square ((s-l)-(sqrt(3)-1)*d)^2 and l>=0 bound this by
    (4-2*sqrt(3))*d.
* The d=l degenerate case is treated separately without dividing by zero.

Axioms printed for Regular.quantumPatch_real_gain:
  propext, Classical.choice, Quot.sound.

Propagation analysis (not a new formalized theorem in this file): a uniform
lower error A and upper error B can each become A+B after a sieve step;
the new lower correction is then added. The crude scalar bound therefore
doubles from stage to stage and is not sufficient for quadratic positivity.
No localization-sensitive accumulated estimate was proved.

Also noted: a per-patch dilation cost of order 1/(g-1) looks possible via chord
supports at g+1; it has not been formalized or used. Uniform boundedness of
its product is NOT established by the existing eventual k*log(k) lower bound.
Known stronger prime-gap lower-bound ideas would require additional estimates
on smooth numbers not present in ConstructiveCover's fixed-set argument.
No summability of 1/h(k) was asserted or proved in this pass.

Spec unchanged; original sole sorry remains. No proof/disproof or submit_proof.

# Multiplicative control of repeated quantum refinements

New files, compiled with built oleans and permitted axioms only:
  ContinuousIntervalQuantumDilation.lean
  ContinuousIntervalQuantumBudget.lean

This is a new accumulated comparison, NOT a proof of quadratic Jacobsthal growth.
It applies to quantumEnvelope with cells := fun _ => []; later chord patches
are not included in this dilation comparison.

## Single-patch and product comparisons

Regular.dilation_self proves that (L(c*x)/c,U(c*x)/c) dominates (L,U) for c>=1.
Dominates.dilate propagates an existing comparison under a common dilation.

Regular.quantumPatch_dilation proves that the quantum patch at g is dominated
by a dilation c whenever c>=1 and c*(g-1)>=g+1. The lower affine support is
compared with the old chord at c*x>=g+1; the upper part follows from concavity.

Define f(g)=(g+1)/(g-1) for natural g>1.
Regular.quantumRefine_dilation works whether or not the guard succeeds.
quantumDilationBudget(trigger,k) = product_{i<k} f(trigger(i)).
quantumEnvelope_dilation_budget proves:
  ordinary_L(k,D_k*x)/D_k >= quantum_L(k,x),
  ordinary_U(k,D_k*x)/D_k <= quantum_U(k,x)  (x>=0 for upper).
This theorem assumes trigger(i)>1 but NO correctness/positivity of the triggers.

Verified quantitative bounds:
  quantumDilationBudget_le_exp:
    D_k <= exp(sum_{i<k} 2/(trigger(i)-1)).
  quantumDilationBudget_le_polynomial:
    if trigger(i)>=i+2 then D_k <= (k+1)*(k+2)/2.
  envelope_positive_of_quantum_positive transfers a given positive quantum
    value to the ordinary envelope at D_k*x; it does not establish positivity.

## Arbitrary guarded schedules, without a trigger hypothesis

Regular.quantumRefine_zero_nat: every zero at a natural length remains zero.
Regular.stepLower_zero_succ: L(n)=0 implies stepLower(q,L,U)(n+1)=0 (q>=0).
quantumEnvelope_zero_at_stage: stage k has lower value zero at natural k.

A successful trigger after stage i+1 must therefore be >=i+2. Failed smaller
triggers leave the lower function unchanged, and any c>=1 suffices for them.
Regular.quantumRefine_safe_dilation makes this distinction rigorously.

Define Dsafe_k = product_{i<k} f(max(trigger(i),i+2)).
The ACTUAL quantum recurrence still uses the original, unclamped trigger schedule.
Only the dilation BUDGET uses the maximum. This does not claim that clamping the
trigger schedule leaves the recurrence unchanged (that would be false in general).

safeQuantumDilationBudget_bounds proves
  1 <= Dsafe_k <= (k+1)*(k+2)/2.
quantumEnvelope_safe_dilation_budget proves the same pointwise ordinary-vs-quantum
comparison using Dsafe_k, for arbitrary trigger schedules and 0<=Q_i<=1.

## Remaining limitation

The displayed quadratic polynomial bounds a MULTIPLICATIVE LENGTH FACTOR,
not the Jacobsthal function. It does not prove the original conjecture.
No stage-independent bound on D_k or Dsafe_k has been established. No uniform
quadratic positive-envelope estimate has been established. Existing eventual
k*log(k) lower bounds do not imply convergence of reciprocal-trigger sums.
No stronger lower-bound or Mertens-product argument was formalized in this pass.

Spec is unchanged; sole original sorry remains line2177. No submit_proof call.

# Exact-count monotone / partition closure diagnostic

A new diagnostic, not a kernel-verified theorem and not a conjecture resolution:
  /tmp/interval_closed.cpp
  /tmp/interval_closed

The program uses the first k primes and the exact period-30 base for {2,3,5}.
The raw step is
  newL(m)=max(0,L(m)-U(ceil(m/p))),
  newU(m)=U(m)-L(floor(m/p)).
Mode0 is the old raw interval recurrence. A cross-check at k100,m10000 gives
lower55 in BOTH the old memoized program and this dense-array implementation.

Mode1 enforces natural-length monotonicity and change-by-at-most-one bounds:
  forward: L(m)>=L(m-1), U(m)<=U(m-1)+1;
  backward: L(m)>=L(m+1)-1, U(m)<=U(m+1).
Mode2 additionally applies selected block partition and mixed inequalities:
  L(m)>=L(m-t)+L(t), U(m)<=U(m-t)+U(t);
  L(m)>=L(m+t)-U(t), U(m)<=U(m+t)-L(t).
Blocks are selected at extrema of L(t)/t and U(t)/t in dyadic length bins,
plus the first positive length and its successor. This is NOT exhaustive
knapsack closure, and no equivalence with a Lean definition was proved.
All computations are finite-length, with upper length cap M.

Diagnostic first positive lengths:
  k100,M80000: raw7934, mode1 7750, mode2 7750.
  k200,M320000: mode2 37116 (ratio0.9279).
  k400,M1280000: mode1 and mode2 174630 (ratio1.0914375).
  k1000,M4000000: mode1 1308570 (ratio1.30857).
Instrumented mode2 through k200 made ZERO partition-bound updates after mode1.
This is observed for the selected blocks only, not a general preservation theorem.

Logs:
  /tmp/interval_closed_100_mode0.log, _mode1.log, _mode2.log
  /tmp/interval_closed_200_mode2.log
  /tmp/interval_closed_400_mode1.log, _mode2.log
  /tmp/interval_closed_1000_mode1.log
The largest run finished in about34 seconds; no worker remains running.

No kernel-certified finite h(k) bound was added. These concern a SPECIFIED
prime set, and the arbitrary-prime transfer is still absent. Increasing finite
ratios neither prove divergence nor rule out eventual boundedness. No uniform
quadratic estimate was obtained. No new Lean file or Spec change in this pass.
Original sole sorry remains; no submit_proof call.

# Structural explanation for partition closure

New verified files (compiled, oleans built, only permitted axioms):
  IntervalHullCompatibility.lean
  IntervalHullStep.lean
Namespace Erdos970.IntervalRescaling.IntegerHull.

Compatible(l,u), for real-valued functions of NATURAL lengths, includes:
  l(0)=u(0)=0, u>=0;
  l(n)<=l(m+n)-l(m)<=u(n);
  l(n)<=u(m+n)-u(m)<=u(n).
The signed lower function may be negative before closure.

Define lowerHull(l,n) as the finite prefix supremum over j<=n, and upperHull(u,n)
as the infimum over ALL j>=n. The upper infimum set is proved nonempty and
bounded below. Compatible.hulls proves the resulting pair is compatible;
its lower hull is nonnegative. In particular, it satisfies ALL four inequalities:
  L(m)+L(n)<=L(m+n), U(m+n)<=U(m)+U(n),
  L(m+n)<=L(m)+U(n), U(m)+L(n)<=U(m+n).
This is not limited to a selected block list.

IntervalHullStep verifies exact quotient increment bounds:
  floor(n/p) <= floor((a+n)/p)-floor(a/p) <= ceil(n/p),
  floor(n/p) <= ceil((m+n)/p)-ceil(m/p) <= ceil(n/p),
for positive p, with the existing ceilQuotient definition.

Compatible.raw_step proves that for a compatible input pair with l>=0,
  rawL(n)=l(n)-u(ceil(n/p)), rawU(n)=u(n)-l(floor(n/p))
is again a compatible SIGNED pair. Its upper function is nonnegative.
Compatible.closed_step then proves compatibility and lower nonnegativity after
monotone hulls. Thus an additional partition closure adds no information to this
INFINITE-DOMAIN compatible recurrence.

Limits: the finite-cap C++ program has not been proved equivalent to these
infinite-domain hulls. Its exact wheel base has not been connected here to this
new interface. These files do not establish arbitrary-prime reference transfer,
any uniform positive-envelope estimate, or the original quadratic conjecture.
The structural result does not prove that the monotone recurrence itself fails.

Spec unchanged, original sole sorry at2177, no submit_proof call.

# Kanold constant-coefficient recurrence obstruction

New development file, compiled and olean built:
  Submission/KanoldRecurrenceOrder.lean (213 lines)
Imports only FormalConjecturesUtil. All checked axioms are propext,
Classical.choice, Quot.sound. No dependence on the original sorry.

Namespace Erdos970.KanoldRecurrence:
* coefficients_zero: distinct geometric sequences are linearly independent.
* orderOf_prod: products of primitive roots with distinct prime orders have
  order equal to the product of those primes.
* prod_injective_on_powerset: all subset-product frequencies are distinct.
* recurrence_roots and card_le_recurrence_order: a constant-coefficient linear
  recurrence for a finite sum of distinct, nonzero-weighted geometric sequences
  has order at least the number of frequencies.
* two_pow_le_order_of_product_solution:
  For prime P, primitive z_p of order p, and c_p != 0, ANY LinearRecurrence E
  satisfied by n |-> product_{p in P}(z_p^n-c_p) has E.order >= 2^|P|.
* two_pow_le_order_of_residue_product specializes c_p=z_p^{r_p}, so the result
  holds even for each fixed forbidden-residue vector.

This rules out shortening the existing Kanold argument merely by finding a
lower-order CONSTANT-COEFFICIENT recurrence for the SAME product sequence.
It does NOT establish a lower bound on the sequence's longest zero run, does
NOT disprove the quadratic conjecture, and does NOT rule out other algebraic
arguments or modified constructions. No new quadratic positivity or prime
increment estimate was proved. Spec unchanged; original sorry remains.

# Finite windows, soundness, and stabilization of the closed integer recurrence

New files, compiled with oleans and only permitted axioms:
  Submission/IntervalHullWindow.lean     172 lines
  Submission/IntervalHullSoundness.lean  120 lines
  Submission/IntervalHullStability.lean   71 lines
Namespace Erdos970.IntervalRescaling.IntegerHull.

## Exact finite window

For Compatible(l,u), l>=0, and p>=2, the infinite infimum defining
upperHull(rawUpper p l u,n) equals the finite minimum for
  n <= m <= n + floor(n/(p-1)).
Only n and the multiples of p in that window need to be checked:
  Compatible.upperHull_eq_window
  Compatible.upperHull_eq_candidates.
Key estimate: for m >= n+floor(n/(p-1)),
  rawUpper(m) >= u(n) >= rawUpper(n).
This follows from the compatible upper increment inequality and
  m-floor(m/p) >= n.

For monotone l and p>0, lowerHull(rawLower p l u,n) equals the finite
maximum over n and multiples of p in [0,n]: lowerHull_eq_candidates.
This is an exact reduction, not a finite truncation justified by a heuristic.

## Actual-count soundness

Bounds p k l u means l(m)<=count(p,r,k,m)<=u(m) for every m and r.
Bounds.hulls, Bounds.raw_step, Bounds.closed_step are proved.
closedEnvelope p b lo hi k starts from a verified b-coordinate seed and
performs k closed steps; its actual stage is b+k.
closedEnvelope_sound applies to arbitrary positive pairwise-coprime actual
moduli. closedEnvelope_compatible propagates the shape and l>=0.
survivor_of_closedEnvelope_pos transfers a GIVEN positive lower value to
a survivor. bounds_zero and compatible_length supply the exact empty seed.

## Stabilization

window_div: (n+floor(n/(p-1)))/p = floor(n/(p-1)) for p>=2.
Compatible.upperHull_eq_of_lower_zero: if l(floor(n/(p-1)))=0, the closed
upper update at length n is exactly the old u(n).
count_diagonal_zero: r(i)=i covers the first k positions, for any moduli.
Bounds.lower_zero_under_card: a sound nonnegative l has l(m)=0 for m<=k.
Bounds.upper_step_eq: consequently a sound compatible closed upper step is
unchanged whenever n < (k+1)*(p(k)-1), with p(k)>=2.

## Limits

No uniform quadratic positivity has been proved. There is still no transfer
of a first-prime integer computation to arbitrary prime sets. The old finite-cap
C++ implementation has NOT yet been proved equal to this infinite-domain
recurrence; the new window formula provides a way to choose sufficient
lookahead caps, but no complete evaluator-equivalence theorem was added.
The exact wheel seed has not been connected to this new interface.
Spec unchanged (SHA256 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9),
original sole sorry at2177. No conjecture proof or disproof and no submission.

# Integer hull ordering is NOT pointwise optimized by increasing primes

New compiled files, with oleans and only permitted axioms:
  Submission/IntervalHullFinite.lean
  Submission/IntervalHullWheelThirty.lean
  Submission/IntervalHullOrderingExample.lean

IntervalHullFinite:
* finiteStep works over integers or any linearly ordered type with subtraction;
  uses the exact sparse lower/upper candidate sets from IntervalHullWindow.
* finiteStep_eq_closed identifies the finite real step with the infinite hulls
  for Compatible input with nonnegative lower and modulus >=2.
* cast_finiteStep_eq_closed and cast_finiteStep_twice transfer kernel integer
  evaluation to one or two infinite real steps.
* cast_finiteStep_shape preserves compatibility and lower nonnegativity.

IntervalHullWheelThirty:
* Gives the explicit integer lower/upper tables for residue conditions 2,3,5,
  extended by count(n+30)=count(n)+8.
* compatible proves all four inequalities at every length. A generic affine
  periodic-defect identity reduces this to kernel-checked cases modulo30.
* bounds proves soundness for EVERY residue vector and EVERY length.
* attained proves each bound is attained by some residue vector at every
  length: this really is the exact extremal seed, not just an arbitrary pair.

IntervalHullOrderingExample:
Starting from this exact seed, kernel-checked integer finiteStep values are:
  at n483: order 7,11 has upper105; order 11,7 has upper104.
  at n744: order 7,11 has lower150; order 11,7 has lower151.
upper_order_failure and lower_order_failure prove the strict inequalities for
THE INFINITE-DOMAIN REAL CLOSED STEPS, using the verified finite-step comparison.
Thus the old continuous ordering theorem does NOT extend pointwise to this
integer hull recurrence. This does NOT contradict the continuous theorem.
It is NOT a counterexample to Erdős970 and proves no asymptotic gain.

Diagnostic scripts (not themselves kernel checked):
  /tmp/hull_order_test.py: finds the above example using the exact lookahead
    caps supplied by the new window formula. No bad ordering was found for
    seeds with periods1,2,6 before the period30 example.
  /tmp/hull_order_threshold.py: all tail permutations from the period30 seed
    for total k6,7,8 had identical first positives22,30,48 respectively.
  /tmp/hull_order_local.py: adjacent swaps and20 deterministic random tail
    permutations for k15,30,50,100 found NO better first positive than the
    increasing order (148,564,1848,7750). Some early adjacent swaps worsened it.
These diagnostics do not prove that increasing order optimizes first positivity.
They do not establish arbitrary-prime reference transfer or a uniform bound.
No worker remains running. Spec unchanged; sole sorry remains2177. No submission.

# Cardinality-injection diagnostic and verified terminal redundancy

The original conjecture is STILL UNSOLVED. Spec.lean is unchanged, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9,
with the sole original sorry at2177. No submission was made.

New compiled file and olean:
  Submission/CardinalityBootstrap.lean (120 lines)
Namespace Erdos970.CardinalityBootstrap. All printed axioms are permitted.

Verified facts:
* bound_lt_budget: an IsJacobsthalBound j m forces
    j < |P| + |survivors(P,r,m)|
  for ANY finite prime set P; no p<m restriction is needed.
* count_lower_of_bound and count_lower_of_smaller_quadratic: smaller-cardinality
  bounds give the single-block survivor profile j+1-|P|. The terminal cardinality
  bound is NOT assumed.
* upper_one_le: any residue-uniform upper bound at positive interval length is
  at least1, because r(p)=1 lets position0 survive for every prime p.
* forcedRun_terminal_eq: for the scalar recurrence
    F(0)=v, F(i+1)=max(F(i)-u(i),b(i+1))
  in natural numbers, if u(i)>=1 and b(i)<=K-i, then
    F(K)=v-sum_{i<K}u(i).
  Thus inserting bounds no larger than the remaining singleton budget makes
  NO change to the terminal result when the subtraction costs are HELD FIXED.
  This does NOT say that recursively computed child upper bounds are unchanged.
  It also does not apply automatically to repeated-block injections or to
  subsequent hull/partition closure. Reindex K-b for a nonzero initial stage b.

Purposeful numerical diagnostic of a hypothetical quadratic induction:
  /tmp/interval_bootstrap.cpp and binary
  /tmp/interval_bootstrap_sparse.cpp and binary
  /tmp/interval_bootstrap_sparse_1000000.log
These are diagnostic C++ computations, NOT kernel proofs.

Dense version: period30 seed, first-prime moduli; at intermediate stage i<K,
inject max(0,min(floor(sqrt(m/C)),K-1)+1-i), plus valid repeated-block counts
for three selected smaller cardinalities. Apply finite-cap monotone closures.
At the terminal stage K no smaller-cardinality injection is added.
C=1 results, with and without injections:
  K100: first positive7750, at m10000 lower65 upper1524; no injections.
  K200: first positive37116, at m40000 lower65 upper5491; no injections.
  K400: no positive at or below160000, terminal lower0 upper20017.
        The injected run had673064 raised entries, maximum increase15,
        but the terminal result did not improve.
The program's finite caps are just valid restricted closures; no assertion
that they equal the infinite-domain hull recurrence is made.

Sparse version: raw first-hit recurrence, period30 seed, only single-block
cardinality injections in recursive lower children (not repeated blocks).
The terminal redundancy theorem justifies omitting direct root injections
for this fixed-cost scalar part. At K400,C1 and K1000,C1 the terminal lower
was0 and NO recursive lower child was raised. At K1,000,000,C4, m4e12,
the terminal lower was again0 and NO recursive lower child was raised:
  Lstates37911577, Ustates5342219, approximately165 seconds.
This neither proves failure for every C nor an asymptotic impossibility theorem.
First-prime diagnostics do not by themselves transfer to arbitrary prime sets.
The worker finished (PID43150 is a completed zombie, not an active job).

The coupled-row and largest-prime restrictions were revisited, but no new
quantitative estimate using them was proved. No actual superquadratic cover
family or uniform quadratic positivity/budget estimate was obtained.

# Exact nonoptimality example for the first-hit envelope; parity-box limitation

Still NO proof or disproof of erdos_970. Spec.lean unchanged, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9,
sole original sorry at2177. No submission and no running workers.

New compiled files and oleans, all printed axioms permitted:
  Submission/FirstHitOptimalityExample.lean (144 lines)
  Submission/ParityBoxObstruction.lean (111 lines)

## FirstHitOptimalityExample

Namespace Erdos970.FirstHitOptimalityExample.
Reference marginals are
  1/3, 5/16, 10/37, 2/9, 1/9, 2/23, 1/14, 1/20.
THESE ARE NOT THE FIRST-PRIME MARGINALS.
Let H=X0+X1+X2+X3. The explicit lower polynomial is
  prod_{i<4}(1-Xi) - X4*(H-2)*(H-3)/6
    - (X5+X6+X7)*(1-X0)*(1-X1).
Its 39 terms are explicitly defined, including the constant term.
The quadratic middle factor is nonnegative at integer hit counts (although
not everywhere on the real line).

Kernel-checked:
* pointwise: polynomial<=0 on every nonempty Boolean hit pattern.
* mean_cost: mean83359379/694824480, FULL L1 cost101/3.
* positive_margin: at mass281 the FULL-error margin is positive
  (31561339/694824480); the constant coefficient's error is charged.
* rational_recurrence_zero: the existing linearEnvelope at exactly these
  marginals and mass281 returns lower0.
* real_recurrence_zero transfers that evaluation to the real recurrence.
* survivor_by_polynomial: the new polynomial forces a survivor for281 points
  satisfying the same uniform unit-error intersection assumptions.

Thus the raw first-hit envelope is NOT universally optimal over arbitrary
marginal vectors. This does NOT prove nonoptimality at the first primes,
a uniform quadratic family, or any new uniform Jacobsthal bound.

The example came from a full floating-point moment LP and was then independently
kernel checked with explicit rational coefficients. Diagnostic files:
  /tmp/moment_robustness.py
  /tmp/recursive_robustness.py
  /tmp/robust_specific_rat.py
  /tmp/exact_fraction_certificate.py
  /tmp/robust_random_check*.py
  /tmp/upper_moment_check.py

For first-prime marginals, the full numerical LP and raw first-hit threshold
matched at k3,4,5,6,8,10,12 (exact-mass convention: no constant-term error).
At k12 the common numerical threshold was523.81131347424. They also matched
for marginals1/2,1/3,...,1/(k+1) at these sizes. This is only finite evidence.
For first-prime upper bounds through prefix8,80 tested masses per prefix
also matched the full LP. Again NOT an optimality theorem. Random rational
vectors did exhibit improvements, which led to the exact example above.
A possible role for spacing between reciprocal denominators was noticed but
NOT proved. Do not infer any general optimality from these tests.

## ParityBoxObstruction

Namespace Erdos970.ParityBoxObstruction.
The contemplated positive-box ansatz was
  nu(B)=mu(B)-(-1)^|B| sum_{T superset B} c(T), c(T)>=0,
with c(empty)=0, sum c=mu(empty), and c(T)<=epsilon. Even B impose the
capacity sum_{T superset B}c(T)<=mu(B). No general construction was obtained.

An exact four-coordinate obstruction is now proved:
* total_mass_le: nonnegative c with c(empty)=0 and c(T)<=epsilon satisfies
    sum c <=7*epsilon + upperMass(c,{1,2})
                        + upperMass(c,{1,3}) + upperMass(c,{2,3}).
  Every other nonempty pattern contains one of those three pairs.
* no_positive_boxes_at_forty_two: with marginals1/2,1/3,1/5,1/7, total required
  correction8/35 and the corresponding pair capacities1/35,2/105,1/105,
  epsilon1/42 is impossible. In fact the displayed inequality needs
  epsilon>=6/245, which exceeds1/42.
* synthetic_population: nevertheless an explicit unrestricted rational
  population on the16 Boolean patterns has nonnegative masses, total mass1,
  empty-atom mass0, and ALL intersection moment errors<=17/735<1/42.
* scaled_unit_error: multiplying that population by42 gives total mass42 and
  every intersection error<=1, still with zero empty atom.

This separates the restrictive positive-box ansatz from the full synthetic
moment feasibility problem. It is NOT a residue-class cover of42 integers,
and NOT a disproof of the original conjecture. The generic parity-box formula
and its moment inversion have not yet been formalized in this file; the exact
capacity obstruction and explicit feasible population are the proved statements.

Diagnostics, subsequently replaced by the explicit kernel-checked finite data:
  /tmp/positive_parity_dual.py
  /tmp/positive_parity_dual_inspect.py
  /tmp/moment_robustness_4_prime.npz

No uniform asymptotic obstruction for ALL absolute-error sieve certificates
was established. No quadratic positivity family was established either.

# Triangle packing update

The original conjecture is STILL UNSOLVED. Spec.lean is unchanged, with the sole
original sorry at2177, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No submission has been made.

## New compiled files (all oleans built; printed axioms permitted)

* TrianglePacking.lean
  - commonProduct A B = product(A intersect B).
  - AdmitsTriangle m A B C means positive u,v with u+v<m and divisibilities
    commonAB|u, commonBC|v, commonAC|(u+v).
  - NoTriangle quantifies ALL three patterns, INCLUDING repeated patterns.
  - patternCount_le_two_iff_noTriangle: for prime patterns, the universal
    positional budget2 is EQUIVALENT to NoTriangle.
  - The construction direction places positions0,u,u+v and chooses one common
    residue vector. It requires no primality, only the three divisibilities.
* TrianglePackingExample.lean
  - m12, primes{5,7,11}, family{{5,7},{5,11},{7,11}}.
  - Universal actual count<=2, attained by r11=7, all other residues0.
  - Synthetic population: nine empty atoms and one of each family pattern.
  - It obeys ALL separate rounded CRT moments and EVERY common-product spacing
    inequality for EVERY pattern family on these three primes, yet gives3.
  - Therefore those earlier inequalities do not completely characterize
    realizable positional populations. This is NOT a covered population and
    NOT a counterexample to the conjecture.
* TriangleMultipliers.lean
  - AdmitsMultiplierTriangle is the exact finite test using positive a,b with
    commonAB*a+commonBC*b<m and divisibility by commonAC.
  - Multiplier ranges are Fin(m/commonAB+1), Fin(m/commonBC+1).
  - admitsTriangle_iff_multipliers, with positive common products.
  - patternCount_le_two_of_multiplier_checks.
* TrianglePackingLarge.lean
  - Kernel-checked universal budget2 at length25000 for the families:
      core{211}, tails7,23,103;
      core{47}, tails29,41,397.
    Each family consists of the core plus each pair of tails.
  - Common products are1477,4853,21733 and1363,1927,18659 respectively.
* TrianglePolynomial.lean
  - sharedCore_indicator and sharedCore_sum_eq prove the exact four-monomial
    formula for hitting D and at least two of p,q,s:
      hit(D+p+q)+hit(D+p+s)+hit(D+q+s)-2hit(D+p+q+s).
  - sharedCore_sum_le_two under NoTriangle.
  - No bound without that positional hypothesis and no arbitrary-prime transfer
    is claimed. Parentheses around the entire summand are IMPORTANT: without
    them Lean's layout parsed only the first term under the sum, leaving an
    autoImplicit i. This was detected, repaired, and compiled.
* TriangleTransferObstruction.lean
  - m14, family of pairs of{3,7,11}: universal count<=2.
  - Increasing11 to13 yields three hits: positions0,6,13, with r7=6 and others0.
  - prime_replacement explicitly verifies coordinatewise increase and primality.
  - Thus exact triangle incompatibility does NOT generally transfer on merely
    increasing prime values. This is distinct from spacing-only bounds.

## Diagnostics and strengthened relaxation

/tmp/triangle_packing_shared_general.py searches cores of product<=1000 and
common products in(m/20,m), with each pattern product>=m. The positive-multiple
compatibility test is integer-exact; tested population masses are floating point.
The restricted earlier scans (disjoint two-prime blocks in(m/3,m/2], or one shared
core and tails in that range excluding3-term APs) found NO violations.

General shared-core cuts found in earlier k100,m25000 populations:
- bounded8:174 cuts, largest mass2.7121293884764754 at core47,tails29,41,397.
- generalpacking:5 cuts, largest mass2.2003001033636314 at core211,tails7,23,103.
  Others: core107,tails19,47,89 (2.136420995627476);
  core43,tails61,67,101 (2.0376752086662324);
  core71,tails19,43,317 (2.037196599891544);
  core61,tails23,29,211 (2.000409352797362).
- balanced:106 cuts, largest2.3928317071639156, core47,tails37,43,491.

/tmp/sieve_glpk_cg_triangles.py incorporated these cuts and reoptimized using
GLPK with local/full mixed-integer column pricing as in previous scripts.
The first restricted master timed out at positive objective, so its local dual
pricing was only a diagnostic for generating columns, not a global certificate.
At iteration17 it produced a NUMERICALLY FEASIBLE synthetic covered population:
  5318 positive atoms, drawn from5902 columns;
  32673 explicitly constrained CRT moment rows;
  1391 all-but-one/common-product packing cuts;
  301 shared-core triangle cuts;
  mass25000.000000000004, zero empty-atom mass.
  max triangle excess2.1538326677728037e-13.
No further cuts were found by the SPECIFIED LOCAL common-product search and
bounded-core triangle search. This is NOT a global packing separation result,
NOT a Lean-certified rational population, and NOT an actual residue cover.

Files:
  /tmp/sieve_trianglepacking_100_25000_{feasible,state,current_dual}.json
  /tmp/triangle-lp.log
  /tmp/triangle-feasibility-audit.log
  /tmp/triangle-packing-large.log
  /tmp/triangle-polynomial.log
  /tmp/triangle-transfer-obstruction.log

A broader diagnostic /tmp/triangle_packing_allcore.py was launched to remove
these search restrictions (core product<=m/2, no lower common-product cutoff).
Its results are not yet included in this entry; see /tmp/triangle-allcore.log.

No uniform quadratic estimate, nor superquadratic family of ACTUAL residue
covers, has been obtained. The finite packing improvements do not settle970.

The first triangle population audit found:
  CRT lower excess<=5.9117155615240335e-12;
  CRT upper excess<=3.2741809263825417e-11;
  packing excess<=8.246736626915663e-13.
All numbers are numerical residuals, not exact rational checks.

The broader all-core triangle audit DID find8 additional violated cuts in the
first triangle population, with largest mass2.118365800686179 at core367,
tails3,47,61. Hence do not describe that first population as satisfying all
shared-core triangle constraints. Other displayed violations:
  core29, tails5,443,499:2.1073507767550383;
  core137,tails5,97,151:2.0893837350718303;
  core43,tails3,499,521:2.0567720796869016;
  core29,tails11,443,499:2.03624158623398;
  core89,tails5,227,229:2.0250621073184463;
  core61,tails11,67,271:2.0212839452857505.
The larger scan took3.57s, with1468 eligible cores and1708 heavy candidates.
A reoptimization with this larger separator was launched:
  /tmp/sieve_glpk_cg_triangles_allcore.py
  /tmp/triangle-lp-allcore.log
  output prefix /tmp/sieve_trianglepacking_allcore_100_25000.
Check its status before continuation.

Submission/Spec.lean was recompiled successfully apart from the original
unsolved conjecture warning. It still has the same hash and sole sorry.

Additional compiled file and olean: TriangleRepeated.lean.
  commonProduct_dvd_self;
  admits_repeated_triangle: if0<commonAB<commonAA<m, positions0,commonAB,
    commonAA realize A,B,A;
  length_le_patternProduct_of_noTriangle: consequently NoTriangle plus a
    genuinely smaller positive common product forces m<=productA.
All printed axioms are permitted. This is a necessary structural restriction
on the packing cuts, not a Jacobsthal bound. It explains the rarity requirement
in the shared-core scans; no claim about all general pattern families follows.

The broader reoptimization finished at iteration15 (about268s), still with a
NUMERICALLY FEASIBLE synthetic covered population:5356 positive atoms from5997
columns,1463 spacing cuts,321 triangle cuts. No new cuts were found by the
specified all-core shared-singleton-tail separator or LOCAL spacing separator.
This does not assert global separation over arbitrary pattern families.
Maximum triangle excess was -2.0650148258027912e-13.
Audit log /tmp/triangle-allcore-feasibility-audit.log:
/tmp/sieve_trianglepacking_allcore_100_25000 atoms 5356 rows 32673 mass error -1.964508555829525e-10
lower violation 7.275957614183426e-12 upper violation 2.7284841053187847e-11
packing cuts 1463 max violation 3.197442310920451e-13
degree8 population max violation of these cuts -2.7677860003905153e-13

All five latest theorem files were recompiled with only permitted axioms:
TriangleMultipliers, TrianglePackingLarge, TrianglePolynomial,
TriangleTransferObstruction, TriangleRepeated. See /tmp/triangle-final-check.log.
No computational workers remain from these runs. Spec.lean remains unchanged
and unsolved. No proof was submitted.

# Optimal-core exchange update

The original conjecture REMAINS UNSOLVED. Spec.lean is unchanged, with the sole
original sorry at2177 and hash
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No proof was submitted.

## General new verified theorems (oleans built, permitted axioms only)

1. OptimalCoreExchange.lean
   - budget_lt_of_smaller_core: secondary minimization means any smaller retained
     core has STRICTLY larger total budget.
   - survivors_replacement: exact filtering under a block replacement.
   - replacement_hit_card_le / replacement_hit_card_lt. If E is erased and R is
     inserted, with retained residues unchanged and R disjoint from retained P,
     write S=old survivors, U=survivors after just erasing E, H=points of U hit
     by R. Then |S|+|E|+|H| <= |U|+|R|; the inequality is strict when |R|<|E|.
     These are NECESSARY optimality conditions, not estimates for m.

2. SinglePrimeExchange.lean
   - privatePositions_disjoint for different retained primes.
   - private_new_prime_hit_card_le_one: for distinct primes p,q with p*q>=m,
     a q-class hits at most one private point of p.
   - exists_private_missed_by_new_prime if p has at least two private points.
   - removed_card_le_replacement_survivors: one missed private point per erased
     prime gives distinct new survivors.
   - budget_lt_single_prime_replacement: for a FULL cover, if every erased prime
     has a private point missed by the new class, the new budget is strictly
     larger. No global optimality hypothesis is used.
   - budget_lt_single_large_prime_replacement applies this when all erased
     primes have >=2 private points and all products p*q>=m.
   This is a genuine LIMITATION of the one-new-prime approach in the large-prime
   regime, rather than a new lower bound on optimal cover budget.

3. MultiPrimeExchange.lean
   - fullyReplaced records erased primes ALL of whose private points are hit by R.
   - private_witness_card_le: missed private witnesses inject into new survivors.
   - exchange_budget_inequality for full covers:
       oldBudget + |R| <= newBudget + |fullyReplaced|.
   - new_card_lt_fullyReplaced_of_improvement: a budget-improving replacement
     with r new classes must fully replace at least r+1 old private classes.
   - private_card_le_new_card_of_fully_replaced: when all p*q>=m for old/new
     primes, fully replacing an old prime with r new primes requires its private
     count to be at most r.
   - many_small_private_classes_of_improvement: consequently at least r+1 erased
     primes must have private counts <=r.
   These conditions do NOT assert existence of an improving exchange.

## Exact finite audit and numerical tail optimizer

/tmp/private_two_prime_exchange.py audited the existing101-class full cover of
1500 positions from PrivateCoverExample.lean using exact integer arithmetic.
The smallest unused prime is269. Private counts for2,3,5 are166,86,49.
Every other retained prime p>=7 has p*269>1500. Every unused-prime class contains
at most6 interval points. Thus every one-new-prime exchange misses a private
point of EACH erased prime, even if arbitrarily many old primes are erased.

For two-new-prime STRICT budget improvements, the multi-prime condition requires
fully replacing at least3 old classes. The only candidates are old classes with
exactly2 private positions: all other old p>=7 have too many private positions
for two separated new classes, and the private counts for2,3,5 exceed12.
The exact audit found NO unused-prime residue class containing3 of those critical
private points ("eligible first classes0"), hence no such two-fresh-prime strict
improvement. This last finite audit has NOT been formalized in Lean. It concerns
fresh primes and fixed retained residues; it does NOT cover reassigning residues
of old retained primes or arbitrary global rearrangements.
Logs/data:
  /tmp/private-two-prime-exchange.log
  /tmp/private_two_prime_exchange.json

A global tail reoptimization fixed the first12 primes through37 at their original
residues and optimized the other classes/singletons. The MILP had228 remaining
positions and4354 columns. HiGHS timed out after120s with objective77 tail classes,
reported lower bound73. It found a FULL89-prime cover, no singleton leftovers.
No claim of optimality follows from the timeout or numerical objective.
  /tmp/cover_fixed_prefix_milp.py
  /tmp/cover-fixed-prefix-milp.log
  /tmp/cover_fixed_prefix_milp.json

## New kernel-checked finite examples

4. ReoptimizedPrivateCoverExample.lean
   Explicit89 tuples of prime, residue, and two private witnesses.
   Kernel check verifies primality, unique primes, coverage of ALL1500 positions,
   and two private points for every class. This does not trust the solver.
   - exists_empty_survivor_core_with_two_private (89 classes, length1500).
   - exists_nonoptimal_private_core: the old101-class cover cannot be optimal,
     despite its two-private-point property.
   A finite lower bound h(89)>1500 is being added/recompiled; check the latest
   /tmp/reoptimized-private-cover.log before relying on that additional theorem.

5. LocallyStableCoverExample.lean (compiled, olean built)
   Defines the old101-class cover explicitly and proves in the kernel:
   - prime_members, prime_card, full_cover, two_private;
   - small_private (>=7 for2,3,5);
   - unused_prime_large (q>=269 for every unused prime);
   - private_new_class_le_six;
   - each_private_missed;
   - single_new_prime_stable: erasing ANY E subset of the old primes and inserting
     ONE UNUSED prime with arbitrary new residue STRICTLY increases total budget,
     provided the other old residues stay fixed;
   - not_optimal, using the independently verified89-class full cover.
   This is an explicit separation between that one-new-prime local stability and
   global optimality. It is NOT a counterexample to Erdős970.

Technical note: directly kernel-evaluating finite propositions involving the
whole private-position Finset and repeated residue lookups exhausted memory
(exit137). The final proof instead checks finite raw witness data over Lists,
then uses symbolic lemmas to transfer those checks to actual private positions.
The repaired file compiles in about49s and prints only permitted axioms.
  /tmp/locally-stable-cover.log
  /tmp/optimal-core-exchange.log
  /tmp/single-prime-exchange.log
  /tmp/multi-prime-exchange.log

No uniform quadratic budget lower bound, and no superquadratic family of actual
covers, has been obtained. All work above is in DEVELOPMENT files, not Spec.lean.

Final checks for this update:
- ReoptimizedPrivateCoverExample.not_bound_1500 and
  ReoptimizedPrivateCoverExample.jacobsthalFunction_eighty_nine_gt both compile;
  the latter proves1500<jacobsthalFunction89. Printed axioms are permitted only.
  This finite lower bound is NOT the negation of the uniform quadratic conjecture.
- LocallyStableCoverExample is being recompiled against the updated89-cover olean;
  its previous successful compilation already verified single_new_prime_stable
  and not_optimal with permitted axioms only. Latest log is
  /tmp/locally-stable-cover.log.
- No further optimizers are running. The timed-out120s MILP's chosen89-class
  witness was independently kernel checked; its reported dual bound was not used.
- The original conjecture and import in Spec.lean are still unchanged.

The final LocallyStableCoverExample recompile succeeded against the updated
89-cover olean; both printed axiom lists contain only the permitted axioms.
No proof of the original conjecture was submitted.

# Compatible-window realization and merged-order update

The original conjecture is STILL UNSOLVED. Spec.lean has not been changed;
its import and statement are intact, with the original sorry at2177 and SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No proof was submitted.

## New compiled theorem files (all oleans built; permitted axioms only)

1. IntervalWordRealization.lean
   Namespace Erdos970.IntervalRescaling.IntegerHull.
   For integer profiles l,u whose real casts are Compatible, with l(1)>=0 and
   u(1)<=1, both profiles have binary increments. The word stepWord(l) records
   each unit upward step, and its count in[a,a+n) is EXACTLY l(a+n)-l(a).
   Thus it obeys all translated window bounds and simultaneously attains l(n)
   at every initial window. The analogous word from u attains every upper bound.
   - wordCount_stepWord
   - Compatible.lower_word_realizes / upper_word_realizes
   - Compatible.window_lower_iff / window_upper_iff
   - Compatible.exists_empty_window_iff: a zero lower bound really is realized
     by a zero initial window of a binary word satisfying all these constraints.
   The realizing words need NOT come from prime residue configurations.

2. IntervalTwoSidedWord.lean
   The preceding realization also holds for ALL INTEGER starting points, not
   merely nonnegative ones. Define cumulative F(a)=l(a) for a>=0 and
   F(-a)=-u(a) for a>=0. The two mixed compatibility inequalities give exactly
   the bounds for windows that cross zero. Unit increments then define a
   bi-infinite binary word with counts F(a+n)-F(a).
   - Compatible.twoSided_increments
   - intWordCount_intStepWord
   - Compatible.twoSided_lower_word
   - Compatible.int_window_lower_iff
   Consequently, binary-word realizability and all translated window-count
   constraints cannot strengthen a SINGLE compatible integral bound pair.
   This is not an impossibility theorem for the original sieve problem, since
   the words need not satisfy the prime-class or coupled-progression structure.

3. IntervalMergeExample.lean
   An exact warning against assuming arbitrary max-lower/min-upper merges are
   compatible. Two period12, density1/2 pairs have tables:
     L0=[0,0,0,1,1,1,2,2,2,3,4,5]
     U0=[0,1,2,3,4,4,4,5,5,5,6,6]
     L1=[0,0,0,0,1,2,3,3,3,3,4,5]
     U1=[0,1,2,3,3,3,3,4,5,6,6,6].
   Their extensions each satisfy Compatible, proved using finite shape checks
   and the existing exact period-defect formula.
   The pointwise merge has L(3)=1,L(6)=3,L(9)=3, so it is NOT compatible.
   Nevertheless a common alternating bi-infinite word satisfies both pairs and
   their merge. Thus the issue is NOT inconsistency of the merged constraints.
   Every word satisfying the merge has count>=4 at length9, by partition3+6,
   strictly stronger than the merged lower3.
   - compatible, merge_not_compatible, common_word_exists, improved_nine_count.
   This example is NOT claimed to arise from prime-order recurrences.

## Merging prime-order diagnostics

/tmp/interval_merge_closure.py, /tmp/interval-merge-closure.log:
- exact-integer array computations with sufficient lookahead for each STATIC
  ordered closed recurrence, using period30 seed;
- all permutations for k5,6,7, and increasing order plus every adjacent swap
  for k10,20,50;
- merged max-lower/min-upper arrays passed ALL four compatibility inequalities
  for m+n<=M in the tested finite domains;
- no additional partition closure update was triggered.
  k5,M2500,2 orders, first positive14;
  k6,M2500,6 orders, first positive22;
  k7,M2500,24 orders, first positive30;
  k10,M4000,7 orders, first positive66;
  k20,M8000,17 orders, first positive240;
  k50,M15000,47 orders, first positive1848.

/tmp/interval_subset_orders.py, /tmp/interval-subset-orders.log:
- dynamic subset recurrence through the first11 primes, with fixed period30
  prefix and256 tail-subset states, cap3000;
- each state takes the best lower and upper result over all choices of LAST
  prime, so its child branches may themselves choose different orders by length;
- monotone finite-cap closure, and a check of all finite-domain compatibility
  inequalities, with exhaustive partition closure if needed;
- NO state required an additional partition closure;
- first positive78, the SAME as increasing order;
- some nonzero counts improved by1 (32 lower entries,300 upper entries).
  First lower improvement at744:87->88; first upper at483:99->98.
- data /tmp/interval_subset_orders_11_3000.npz.
These are finite diagnostics, NOT kernel certificates or asymptotic results.
The subset implementation uses finite caps; no equivalence with infinite-domain
hulls is asserted. There is still no arbitrary-prime transfer for these integer
computations, and no uniform positivity estimate.

## Repeated-block bootstrap formalization and recursive-child test

4. CardinalityBlockBootstrap.lean
   Namespace Erdos970.CardinalityBootstrap.
   - modEq_shift_iff and survivor_count_add give an exact translated partition.
   - count_lower_repeated_blocks and count_lower_floor_blocks:
       IsJacobsthalBound j g implies
       |survivors(m,P,r)| >= floor(m/g)*(j+1-|P|).
   - count_lower_repeated_smaller_quadratic states the conditional induction form,
     with the terminal cardinality K explicitly excluded.
   - block_profit_efficiency:
       4*(i-1)*(j+1-i) <= j^2 for i>=1.
   - block_profit_budget: ANY finite mixture of blocks costing C*j² and gaining
     j+1-i, with total cost<=m, has
       4*C*(i-1)*totalGain <= m.
     This is an upper bound on that block construction's profit, NOT an upper
     bound on the actual survivor count and NOT a general sieve limitation.

A new sparse diagnostic did test recursive child changes, rather than assuming
all costs fixed as in forcedRun_terminal_eq:
  /tmp/interval_bootstrap_compare.cpp and executable
  /tmp/interval-bootstrap-compare.log.
At K=1,000,000, m=K²=10^12, period30 seed, first-prime raw interval recurrence:
- mode0, no injections: lower0, signed terminal margin -5869381245;
- mode1, smaller-cardinality single-block injections:
    lower0, margin -5869340121,6208 raised lower-child values, max gain25;
- mode2, additionally repeated blocks at the THREE selected cardinalities
    i,2i-2,floor(sqrt(n)) (when allowed): SAME terminal result and gain counts.
The root margin improved by41124, but remained very negative.
Each run used16034346 lower states,2482517 upper states, about50 seconds.
No worker remains running.

IMPORTANT qualifications:
- Unlike the earlier C4 run, recursive lower children DO change in this C1 test.
  Therefore do not promote the fixed-cost redundancy theorem to a recursive
  redundancy claim.
- C1 cannot hold at j1 since h(1)=2. The injector here only uses cardinalities
  j>=i>=4 after the exact three-prime seed; the hypothetical smaller-quadratic
  assumptions are only relevant at those used cardinalities. It does not inject
  the false j1 bound, nor the unproved terminal K bound.
- Only three repeated-block cardinalities were sampled; this is NOT an exhaustive
  knapsack optimization or a proof of repeated-block redundancy.
- These are diagnostics under hypothetical induction bounds, not a completed
  induction, an actual cover, or a kernel-certified global bound.
- No asymptotic obstruction to every recursive bootstrap has been proved.

All four new theorem files print only propext, Classical.choice, Quot.sound.
No uniform quadratic estimate or superquadratic actual-cover family was obtained.

## Propagated repeated-block bootstrap diagnostic

/tmp/interval_bootstrap_propagated.cpp and executable;
/tmp/interval-bootstrap-propagated.log.
First400 primes, period30 seed, cap160000=400², no terminal-cardinality
assumption. New constraints g=j², b=j+1-i for i<=j<400 and i>=4.
Each injection propagates
  U(n) <- min(U(n),U(n+g)-b), descending;
  L(n) <- max(L(n),b-U(g-n)), n<g;
  L(n) <- max(L(n),L(n-g)+b), ascending n>=g.
Mode0: no injections, time0.44s.
Mode3: ascending j, only currently improving constraints:987 constraints,
  3782915 lower updates,0 upper updates,time0.73s.
Mode4: descending j, only currently improving constraints:987 constraints,
  686978 lower updates,0 upper updates,time0.73s.
Mode5: ascending j, ALL78606 candidates including already-satisfied bounds:
  3782915 lower updates,0 upper updates,time11.73s.
All modes: no positive lower count at or below160000; terminal L=0,U=20017.
At stages100,200,300 the root lower counts were8404,4057,1537 respectively
in all modes. These equal summaries DO NOT establish full array equality or
order-independence. Arrays were not saved/compared.
These finite update rules are sound window consequences, but no theorem yet
identifies this finite implementation with a complete infinite-domain closure.
They do not prove arbitrary-prime transfer or asymptotic positivity.

## Exact signed-distance window closure (new verified development)

Four new theorem files compile and have oleans. Printed axioms are only
propext, Classical.choice, Quot.sound. Spec.lean is unchanged and UNSOLVED.
Namespace Erdos970.WindowConstraintClosure (with TruncationExample subnamespace).

1. WindowConstraintClosure.lean
   - Admissible d F: every signed increment F(a+z)-F(a) <= d(z).
   - LowerBlock F g b: every g-increment >=b.
   - IsDistance d: d(0)=0 and d is subadditive on Z.
   - addLower d g b z = inf_{t:N} [d(z+t*g)-t*b].
   - An explicit common consistency witness F bounds all candidate sets below;
     Int.csInf_mem gives an attained integer minimum.
   - addLower is normalized subadditive, <=d, and has value at -g <=-b.
   - addLower_greatest: greatest normalized subadditive minorant of d with
     this added negative-distance bound.
   - addLower_eq_self: already-implied constraints do nothing.
   - addLower_comm: exact closures commute under an explicit common witness.
     This does NOT assert order-independence of finite truncated update rules.

2. WindowClosureRealization.lean
   - signedDistance l u z = -twoSidedCumulative l u (-z).
   - Compatible integral profiles give IsDistance; d(n)=u(n), d(-n)=-l(n).
   - wordCumulative gives an indefinite signed count for arbitrary bi-infinite
     binary words, with exact translated telescoping counts.
   - Normalized subadditive d with d(-1)<=0,d(1)<=1 admits binary realizations
     attaining all initial upper counts d(n), or all lower counts -d(-n).
   - wordModel_iff_closed: old constraints plus the new lower block bound are
     EXACTLY equivalent to the closed signed-distance constraints.
   - window_lower_iff and window_upper_iff: no stronger counts follow from these
     constraints on binary words, even with all integer translates enforced.
   - empty_window_iff: an empty initial n-window is possible exactly when
     addLower d g b (-n)=0. NOT a prime-residue cover construction.

3. WindowClosurePeriodic.lean
   Hypothesis: Q>0, d(z+Q)=d(z)+R for all integer z.
   - IsDistance.periodic_slope_le: z*R <= Q*d(z).
   - balanced Q R a = floor(a*R/Q) is admissible.
   - periodic_consistent_iff: a new lower bound (g,b), g:N, is consistent
     exactly when b*Q <= g*R.
   - periodic_attained_below: a minimizing t may be chosen <Q.
   - periodic_addLower_eq_finset_min: exact finite evaluation over t=0,...,Q-1.
   - periodic_addLower: closure preserves period Q and increment R.
   - periodic_lower_certificate_iff: every strengthened lower bound has a
     certificate with fewer than Q repetitions.
   A sieve period such as a primorial can be enormous; this theorem does NOT
   justify the much shorter numerical caps used in earlier experiments.

4. WindowClosureTruncationExample.lean
   Kernel-checked diagnostic example:
     d(z)=6*floor(z/12)+min(z mod12,6), period12, increment6.
     Add the lower constraint: every length4 window has >=2 ones.
   Exact closure has upper count2 at length3.
   However, the word 1110 repeated bi-infinitely satisfies EVERY translated old
   constraint of length<=7, and the new length4 lower bound, while its first
   length3 window has3 ones. Thus the truncated information cannot force the
   improvement, although the full profile does.
   Theorems finite_window_information_insufficient and
   full_window_information_sufficient distinguish these cases rigorously.
   This is NOT asserted to be a profile arising from a prime-order recurrence.

Essential gap unchanged: none of these binary-word theorems establishes the
needed uniform quadratic positivity for actual prime residue sets, nor a
superquadratic family of actual covers. No proof was submitted.

## Mixed hit/avoidance rescaling and a verified finite joint-count gain

The conjecture is STILL UNSOLVED. Spec.lean remains unchanged with its original
sorry. No proof was submitted. Four new theorem files compile and have oleans:

1. MixedPatternRescaling.lean (namespace Erdos970.MixedPattern)
   - positions / mixedCount retain hits on A AND avoidance on B.
   - mixedCount_rescale_exact: for disjoint prime sets A,B, the mixed pattern
     is a sieve of B on one CRT progression with length c. Crucially,
       c = mixedCount m A empty r,
       floor(m/prod A) <= c <= ceil(m/prod A).
   - mixedCount_rescale, mixedCount_bounds: weaker floor/ceiling enclosures.
   - interpolate_adjacent: exact affine identity for any integer-valued function
     evaluated at an integer between adjacent endpoints.
   - mixedCount_bounds_interpolated: linear upper/lower constraints retaining
     the actual required-hit count c instead of using an independent worst
     endpoint. Their validity uses integrality of c, not a fractional assumption.

2. MixedPatternMomentExample.lean
   A kernel-checked six-point SYNTHETIC population on primes{2,3,5} has patterns
     {2},{2},{3},{2,3},{5},{5}.
   It has no empty pattern and satisfies EVERY rounded CRT intersection moment.
   But its mixed count (hit5,avoid2) is2. For an actual interval of length6,
   actual_mixed_le_one proves this count<=1 by exact progression rescaling.
   synthetic_not_realizable proves the distinction. The population is NOT a
   residue cover and is not a quadratic counterexample.

3. WheelFiniteCheck.lean
   Raw Boolean List-based checks for three finite wheels at length69:
     {3,11,17}: minimum>=38;
     {3,5,17}:  minimum>=33;
     {3,5,11}:  minimum>=32;
     {3}:       maximum<=46.
   fast_check_verified uses decide +kernel and prints NO axioms.
   Direct all-shift checks with Finset.card or Nat.count exhausted the10GB
   cgroup memory limit twice. The repaired raw List.filter/Bool.all certificate
   compiles; no native_decide or numerical solver is trusted.

4. MixedPatternJointExample.lean
   - survivors_eq_wheelCount and bounds_of_wheel_check transfer finite wheel
     checks to EVERY residue vector for the fixed prime set via CRT translation.
   - fastWheel_eq transfers the raw Boolean count to the semantic count.
   - three_pair_avoidance_le: with base S and three added moduli p,q,t,
       count(S+p+q)+count(S+p+t)+count(S+q+t)
         <= count(S)+2*count(S+p+q+t).
     No primality is needed for this combinatorial inequality.
   - four_prime_survivors_ge_twenty_nine:
       count(69,{3,5,11,17},r)>=29 for EVERY r.
     Inputs give2*count >=32+33+38-46=57; integrality gives29.
   - Small kernel checks give upper count6 for{3,5} at length10 and upper count4
     for{3} at length6. Exact rescaling then proves
     five_prime_survivors_ge_twenty_three for{3,5,7,11,17}, length69;
     six_prime_survivors_ge_nineteen for{3,5,7,11,13,17}, length69.
   All printed theorem axioms are only propext, Classical.choice, Quot.sound.
   These are fixed-prime-set count bounds, NOT uniform h(k) estimates.

### Diagnostic LP comparisons (not kernel proofs)

/tmp/exact_atom_diagnostic.py:
For first3 through6 primes at a fixed list of lengths, compared maxima of exact
atoms under all rounded positive intersection moments with actual/proved
progression upper bounds. Found violations, including the six-point synthetic
example independently verified above. No actual cover was found or claimed.

/tmp/mixed_pattern_interval_lp.py and log /tmp/mixed-pattern-interval-lp.log:
Memoized recursive LP over all Boolean atoms and ALL disjoint mixed boxes A,B.
A nonempty required set rescales to lower/upper bounds for B at floor/ceil(m/prod A).
Proper avoided-subset counts at the parent length are included. Actual integer
count bounds are rounded up/down from floating LP optima (diagnostics ONLY).
For the listed first-prime cases k3..8, no gain over raw first-hit was observed.

/tmp/mixed_pattern_interval_seeded.py, /tmp/mixed-pattern-interval-seeded.log:
Same LP with EXACT periodic bounds for ALL sets of at most3 primes as seeds,
not merely the fixed{2,3,5} prefix. Some gains over fixed-order first-hit occur.
/tmp/mixed_pattern_order_compare.py, /tmp/mixed-pattern-order-compare.log:
At those selected lengths, all gains were matched by a dynamic best-single-prime
last-deletion recurrence using the SAME exact three-prime seeds.
No monotone hulls are applied in these comparisons.

/tmp/mixed_pattern_interval_interpolated.py and corresponding .log:
Stronger rows using the actual required-hit moment and adjacent-endpoint affine
bounds. At the initially selected lengths, results agreed with the ordinary LP.

/tmp/mixed_pattern_comparison_scan.py, /tmp/mixed-pattern-comparison-scan.log,
/tmp/mixed_pattern_comparison_scan.json:
Exhaustive LENGTH diagnostics for these three fixed prime sets:
- first6 primes, n=1..100: one difference at n97;
  subset=(13,25), ordinary mixed=(13,25), interpolated=(13,24).
  The improved upper24 is also available from parity rescaling to the odd-prime
  problem at length49; do not claim this as an unprecedented mathematical bound.
- first7 primes, n=1..60: no differences among these methods.
- odd6 primes{3,5,7,11,13,17}, n=1..100:
  n69: subset=(18,32), ordinary mixed=(19,32), interpolated=(19,32);
  n76: subset=(20,35), ordinary mixed=(20,35), interpolated=(20,34).
No universal redundancy or ordering theorem follows from these finite scans.

Dual inspection for n69:
/tmp/mixed_extract_dual.py and variants _5.py,_4.py;
/tmp/mixed_dual_odd6_69.json, _odd5_69.json, _odd4_69.json.
The root gains propagate from the four-prime set{3,5,11,17} at length69,
whose LP optimum is28.5 (rounded lower29), versus28 for the compared deletion
recurrence. The dual has exactly the three pair-lower rows with weight1/2 and
the parent-upper row with weight-1/2. This guided, but is NOT trusted by, the
independent kernel proof of the displayed finite bounds.

All diagnostic workers finished. Some defunct child processes may remain, but
no active worker is known. Uniform asymptotic positivity and arbitrary-prime
transfer for the finite diagnostics remain unproved. No quadratic bound or
superquadratic actual-cover family was obtained.

## General joint deletion bound and systematic small-block test

Spec.lean is still unchanged and UNSOLVED. New compiled file and olean:
  JointDeletionBound.lean
Namespace Erdos970.MixedPattern. All printed axioms are permitted.

Verified for arbitrary moduli, not just primes:
- sum_deleted_survivors_le, for nonempty D:
    sum_{p in D} count(S union (D erase p))
      <= count(S)+(D.card-1)*count(S union D).
  A point failing the full added sieve can survive after deleting at most one
  added condition; a full survivor contributes D.card on the left.
- joint_count_bound combines any valid deletion lower bounds with a core upper.
- joint_rounded_lower, for |D|>=2:
    ceil((sum deletionLower-coreUpper)/(|D|-1)) <= full survivor count,
  with natural truncated subtraction. Integer rounding is proved, not inferred
  from a floating-point LP.

Purposeful finite-array diagnostic:
  /tmp/joint_block_interval.cpp and executable;
  /tmp/joint-block-interval.log.
First K primes, period30 seed, cap M=K²; consecutive blocks of b=3,4,5 primes.
At each block compute every subset state by the best choice of last deletion.
Mode1 additionally applies the above joint inequality for EVERY core subset E
of the current block mask D with |D\E|>=2, followed by finite-cap monotone and
unit-increment closures. Mode0 uses the same subset states/closures without
joint inequalities. This is NOT asserted to equal an infinite-domain closure.

Results for K100,200,400 and all b3,4,5:
- ZERO joint updates in every mode1 run, including all intermediate block states.
- K100: first positive7750, root L65,U1524 in all cases.
- K200: first positive37116, root L66,U5491 in all cases.
  (The extra1 relative to an earlier fixed-order root65 comes from order choices,
   not from joint inequalities.)
- K400: no positive lower value at/below160000; root L0.
  b3 rootU20017; b4/b5 rootU20016, in both modes.
- Largest run b5,K400 with joints took12.7s. All workers finished.

Interpretation: the previously verified gain from distinct exact three-prime
seeds did NOT reproduce in this experiment when all subset profiles were derived
from one common period30 seed. This finite observation does NOT prove a general
redundancy theorem or rule out stronger/more global coupled information.

No growing-k estimate was obtained. A recheck of Mathlib found no pre-existing
Jacobsthal/Iwaniec/Kanold interval theorem supplying the missing result. No proof
or disproof of the original quadratic statement has been submitted.

## Re-examination of shared phases and collision information

No new theorem was claimed in this pass. Spec.lean remains unchanged and UNSOLVED.
Re-read the common-inverse row rescaling and large-prime/two-survivor reductions.
The condition that all old survivors lie in one residue modulo the new prime is
exact, but does not give a quantitative count or distribution estimate.

Considered a collision-energy formulation: if S is the old survivor set, a
one-residue concentration has sum_a |S intersect(a mod p)|² = |S|². A strict
upper bound would exclude a full cover after insertion. No sufficiently strong
uniform energy bound, or positive lower bound on |S| at C*k² for the old set,
was proved. This is an unimplemented possible reformulation, not a new result.

Also considered pairwise intersections among large-prime classes over a
small-prime survivor set. Separate CRT intersection upper bounds have unit
errors, which accumulate at the scale of the square of the number of classes.
Concentrated multiple hits prevent treating these errors as independent or
claiming a uniform average-density factor. No such independence assumption was
used in Lean, and no new concentration or incidence bound was established.

No numerical counterexample search or new background worker was started.
No proof/disproof was submitted; the sole original sorry remains in Spec.lean.

## Binary CRT cubes: exact exponential minimal noncoverable families

New compiled file and olean: CRTCube.lean.
Namespace Erdos970.CRTCube. The three main results print only permitted axioms.

For any finite prime set P, define the canonical representatives
  points P = {x < product(P) : every residue x mod p is 0 or 1}.
Proved:
- exists_pattern: every prescribed binary pattern has a representative;
- eq_of_residues: canonical representatives are unique;
- card_points: exactly 2^P.card points;
- not_covers: no choice of one residue class per prime covers all these points;
- proper_subset_coverable: every proper subset can be covered.
The last proof chooses a missing point x and takes the complementary binary
residue 1-(x mod p) at each prime. Every different point differs in a coordinate.

These positions are NOT consecutive. This supplies an exponential minimal
obstruction for arbitrary-position local-consistency arguments, not an interval
cover or a bound/disproof of the Jacobsthal conjecture. Spec.lean is unchanged,
and its original sorry remains. No proof was submitted.

## Matching arbitrary-position Helly upper bound

New compiled file and olean: ResidueHelly.lean.
Namespace Erdos970.ResidueHelly; printed dependency axioms are permitted.

- separated_card_le: if coordinate patterns a_i and deletion witnesses b_i obey
  a_i(j) != b_i(j) for all j, while each off-diagonal pair a_i,b_i' agrees at
  some coordinate, then |I| <= 2^|J|. Uses rational matrices: the matrix
    product_j (a_i(j)-b_i'(j))
  is nonsingular diagonal and factors through the 2^|J| subset coordinates.
- minimal_noncoverable_card_le: every minimal noncoverable finite position set
  has <=2^P.card points. Valid for arbitrary natural moduli, without primality.
- exists_small_obstruction and coverable_iff_small_subsets: an exact finite
  Helly statement at threshold2^P.card.
- sharpness: the binary CRT cube attains this threshold for every prime set.

This completes the arbitrary-position local-witness question in both directions.
It is not an upper bound on the length of a covered consecutive interval. In
particular it supplies no improvement over the exponential scale without a new
use of consecutiveness. The original quadratic conjecture remains UNSOLVED.

## Relative concentration with additive constant fails on long intervals

New compiled file and olean: LongIntervalConcentration.lean.
All printed axioms are permitted. Spec.lean is unchanged and UNSOLVED.

- totient_prime_product and zero_survivors_scaled_le give the periodic bound
    N * S(m,P,0) <= product(p-1) * (m+N), N=product(p).
- many_removed: if every old prime q satisfies T<q<p, the new zero class modulo p
  removes at least T old survivors in length (T+1)*p, namely p,2p,...,T*p.
- unbounded_additive_concentration: for ANY natural A,B,C,M, there are a prime
  set P, a new prime p larger than all its members, and m>=M and m>=C*(|P|+1)^2,
  with
    B*S + A*p < p*R,
  where S is the old zero-residue survivor count and R the number removed by p.
- not_uniform_relative_estimate: hence no real constants A,B can universally
  bound R <= B*S/p + A on all intervals m>=C*(|P|+1)^2.

Construction: take T=A+2, then a finite prime tail P beyond T with sufficiently
small Euler-product density; take p prime sufficiently large compared with its
fixed period and the requested length threshold. All T displayed multiples
survive P, while the whole-interval count has B*S<=p.

This is NOT a disproof of the largest-prime increment or Erdős 970. It excludes
one proposed uniform counting strengthening. As currently proved, m can be much
larger than |P|^2; a restriction to a bounded quadratic-scale window is not yet
covered by the theorem. No numerical search was used.

## Strengthening: concentration obstruction at EXACT quadratic scale

New compiled file and olean: QuadraticScaleConcentration.lean.
All printed dependency axioms are permitted. This strengthens the preceding
result and removes its caveat about excessively long intervals.

- exists_nth_prime_small D N: there is n>=N with D*p_n<n^2. If not, the prime
  reciprocal series would be dominated eventually by D/n^2, contradicting
  Euler's divergence. No prime number theorem or Chebyshev lower bound used.
- exists_large_prime_tail: any fixed finite prime tail beyond T can be enlarged
  to arbitrarily large P satisfying L*q<|P|^2 for every q in P.
- unbounded_at_exact_quadratic_scale A B C K (C>0): there are P,p,m with
  |P|>=K, all q in P prime and q<p, p prime, and EXACTLY
      m=C*(|P|+1)^2,
  yet B*S + A*p < p*R for zero-residue survivor count S and new-p removals R.
- not_uniform_relative_estimate_exact C K (C>0): the corresponding real-constant
  estimate R <= B*S/p + A fails at this exact scale, even after discarding any
  finite initial range of cardinalities.

Proof uses a small-density fixed core P0 beyond T=A+2, then pads it by primes
beyond T while retaining a quadratic upper bound on its largest prime. With
L=2*(T+1), Bertrand selects p between floor(m/L) and twice that number. Thus
(T+1)*p<=m<L*p, all p,2p,...,T*p survive P, and the old fixed core bounds B*S<=p.

This is NOT a cover of the interval: there are other old survivors. It does NOT
negate LargestPrimeIncrement or erdos_970. It rules out a specific overly strong
uniform relative-plus-constant estimate as a proof route. Spec.lean remains
unchanged and UNSOLVED; the original sorry is still present. No proof submitted.

## Further positive-sieve audit: divisor-cutoff boundary defect

Spec.lean is unchanged and UNSOLVED. Re-read SelbergLowerCriterion,
SelbergDefect, SelbergNormalizer, and the reference transfer. No new theorem
establishing the required uniform main-term/remainder inequality was obtained.

A targeted diagnostic evaluated the exact boundary-defect FORMULA using floating
arithmetic for P={primes<=z}, D={squarefree divisors<=z}:
  G=sum_{d<=z} mu(d)^2/phi(d),
  H=sum_{d<=z} mu(d)^2*omega(d)/phi(d),
  Gamma=(1-sum_{p<=z}1/p)*G+H.
Files: /tmp/selberg_defect_scale.cpp and executable.
Results (z, Gamma, Gamma/G^2):
  10          2.77063492063   .206080283353
  100         2.84352342804   .0813957782273
  1000        3.00560082856   .0442661819506
  10000       3.05452046697   .0274780837380
  100000      3.08260261381   .0186816223243
  1000000     3.09863870140   .0135037841902
  10000000    3.10802924374   .0102061153196

These numbers are NOT proof certificates or a proved asymptotic. In particular,
positive Gamma alone is insufficient: the implemented lower criterion still
requires m*Gamma/G^2 > (k+1)*D.card^2. No sharper uniform remainder estimate or
support choice was proved here. No assertion that ALL possible lower weights
fail was made. No quadratic upper bound or actual superquadratic cover family
was obtained. No proof was submitted.

## Elementary prime-counting lower bound formalized

New compiled file and olean: PrimeCountingLower.lean.
Namespace Erdos970.PrimeCountingLower. Printed axioms are permitted.

Verified:
- two_pow_le_centralBinom n;
- centralBinom_le_primeCounting_pow: binom(2n,n) <= (2n)^pi(2n), using the
  prime-factorization exponent bound already in Mathlib;
- even_log_bound: n*log2 <= pi(2n)*log(2n);
- log_bound for n>=2: (log2)*n <= 4*pi(n)*log n;
- lower_bound: pi(n) >= (log2)*n/(4*log n);
- nth_prime_quadratic: p_k <= 256*(k+1)^2;
- nth_prime_mul_log: p_k <= 80*(k+1)*log(k+2).
The preliminary quadratic estimate concerns the k-th PRIME, NOT Jacobsthal's
function. None of these results is a proof of erdos_970.

Investigated the further intermediate assertion Gamma>=1 for the divisor-cutoff
Selberg support at a cutoff containing the sieving primes. It is NOT PROVED.
The finite diagnostics from the previous section are not substitutes for it.
A possible analysis would require uniform comparisons of the truncated
mu^2/phi sums after removing one prime; the available harmonic lower bound alone
loses a constant times the growing reciprocal-prime sum and does not suffice.
No such comparison, or improved Jacobsthal exponent, was claimed or added.

Spec.lean remains unchanged and UNSOLVED, with the sole original sorry. No proof
or disproof of the quadratic conjecture has been submitted.

## Elementary Mertens estimates formalized

New compiled files and built oleans:
- WeightedMertens.lean
- ReciprocalMertens.lean (imports WeightedMertens)
Namespace Erdos970.WeightedMertens. Printed final axioms are permitted.

Verified, with absolute positive constant B=boundConstant:
- abs_primeSum_sub_log: |sum_{p<=n} log(p)/p - log n| <= B (n>0).
  Proof: factorization of n!, Legendre lower floor(n/p) bound and upper
  n/(p-1) bound; Chebyshev theta <= n log4; Stirling lower bound. The error
  sum log(p)/(p(p-1)) is dominated by the summable 4*p^(-3/2).
- abs_realPrimeSum_sub_log: corresponding real cutoff estimate, error B+1.
- abel_reciprocal: exact Abel-summation identity for sum_{a<p<=b}1/p.
- abs_reciprocalInterval_sub_loglog: for 2<=a<=b,
    |sum_{a<p<=b} 1/p - (log(log b)-log(log a))| <= 2*(B+1)/log a.
  The coefficient of the log-log increment is exactly 1, and the error is
  uniform in b. Uses integrability and FTC, not an unproved asymptotic.

This completes the intermediate analytic plan, NOT the quadratic Jacobsthal
bound. No uniform Selberg boundary-defect comparison or sufficient remainder
estimate has been derived from it yet. Spec.lean is unchanged and UNSOLVED;
the original sorry remains. No proof/disproof submitted.

## Arbitrary-prime-set Mertens consequences formalized

New compiled file/olean: PrimeSetMertens.lean, importing ReciprocalMertens.
Namespace Erdos970.WeightedMertens; final axioms permitted.

Verified:
- prime_set_tail: for any finite prime set P and 2<=a<=b,
    sum_{p in P, a<p} 1/p <= log log b-log log a + 2*(B+1)/log a + |P|/b.
- prime_set_reciprocal_le: if |P|<=k,
    sum_{p in P} 1/p <= log log(k+2) + reciprocalConstant.
- reciprocal_correction_le_one: sum_{p in P}1/(p(p-1))<=1 for P contained in [2,infty),
  via an exact finite telescoping identity.
- prime_set_density_lower: if |P|<=k,
    exp(-reciprocalConstant-1)/log(k+2) <= product_{p in P}(1-1/p).
  The logarithmic factor has power 1, not a weakened power from exp(-2 sum1/p).

This is a density estimate, NOT a short-interval survivor lower bound. The
Selberg lower criterion still has its unsolved main-term-versus-error issue.
Spec.lean remains unchanged with the original sorry. No settlement submitted.

## General Selberg lower-kernel energy formalized

New compiled file/olean: SelbergEnergy.lean (imports SelbergDefect).
Namespace Erdos970.FiniteSelberg. Printed final axioms permitted.

Verified:
- linearKernel_hit_average for arbitrary orthogonal coefficients c(Q):
  E[hit_i F^2] = q_i sum_{Q not containing i}
    variance(Q)*(c(Q)-(1-q_i)/q_i*c(Q+i))^2.
- lowerKernel_average: E[(1-number_of_hits) F^2] = kernelEnergy(q,c).
- kernelEnergy_weighted, in coordinates c(Q)=weight(Q)*f(Q):
  kernelEnergy = sum_Q weight(Q)*f(Q)^2
    - sum_i q_i sum_{Q not containing i} weight(Q)*(f(Q)-f(Q+i))^2.
This is an exact finite Dirichlet-form identity, not restricted to the previous
hard-cutoff reproducing kernel. No assertion of positive mean or adequate
interval remainder at quadratic length has been made.

A targeted FLOATING quadrature diagnostic for a continuum, log-product-profile
ansatz found smallest energy quotients approximately .71137, .71156, .71161
at 100,300,1000 bins. The inferred cutoff exponent .7495 is NOT a theorem,
not a uniform optimization result, and not a Lean certificate. It only tests
this one continuum approximation, not arbitrary multivariate kernels.
Spec.lean remains unchanged and UNSOLVED. No proof/disproof submitted.

## Arbitrary-kernel interval criterion formalized

New compiled file: SelbergEnergyCriterion.lean (imports SelbergEnergy).
Namespace Erdos970.FiniteSelberg; final printed axioms permitted.

Verified:
- linearKernel_expansion and ordinaryCoefficient, the full transform from
  orthogonal coefficients to ordinary hit-monomial coefficients;
- arbitrary_square_hit_error: error <= kernelCost^2, where kernelCost is the
  sum of absolute ordinary coefficients;
- arbitrary_lowerKernel_error: error <= (k+1)*kernelCost^2;
- survivor_of_kernelEnergy: a survivor follows if
    (k+1)*kernelCost(q,c)^2 < m*kernelEnergy(q,c).

This removes the previous restriction to the canonical hard-cutoff kernel
and its coarse cardinality-based cost. It is still a CONDITIONAL criterion.
No family c has been shown to satisfy it uniformly at m=C*k^2, and no claim
has been proved that all such families fail. The original conjecture remains
UNSOLVED and Spec.lean unchanged. No completed proof/disproof was submitted.

## Exact kernel costs and sharper Selberg upper remainder formalized

New compiled files/oleans:
- SelbergCost.lean (imports SelbergEnergyCriterion and PrimeSetMertens)
- SelbergSharpUpper.lean (imports SelbergCost)
Namespace Erdos970.FiniteSelberg; printed final axioms permitted.

Verified:
- kernelCost_of_nonneg: for c(Q)>=0,
    kernelCost(q,c) = sum_Q c(Q) product_{i in Q}(1+1/q_i).
- kernelCost_weighted: for f(Q)>=0, c(Q)=weight(Q)*f(Q),
    kernelCost = sum_Q f(Q) product_{i in Q}(1+q_i)/(1-q_i).
- superset_divisorSupport_card_le: number of supported Q containing T is at
  most floor(R/product_{i in T} p_i), by injectivity of the cofactor map.
- divisor_cost_sum_le_product: a general multiplicative divisor-sum bound.
- divisor_cost_sum_le:
    sum_{d<=R,squarefree,prime support in P} product_{p|d}(p+1)/(p-1) <= exp(2)*R.
  Uses the exact reciprocal-correction sum <=1, not a numerical Euler product.
- kernelCost_canonical and prime_canonical_cost_le: the normalized canonical
  kernel has L1 cost at most exp(2)*R/G(R).
- prime_survivors_le_sharp_cutoff:
    survivors <= m/G(R) + (exp(2)*R/G(R))^2.
- prime_survivors_le_sharp_log (when all primes <=R are available):
    survivors <= m/log(R+1) + (exp(2)*R/log(R+1))^2.
This saves log^2(R) in the earlier R^2 upper-sieve remainder. It is an UPPER
bound on surviving positions, not a lower bound guaranteeing one survivor.
No uniform quadratic main-term-versus-error condition was established.
Spec.lean is unchanged with the original sorry. Conjecture UNSOLVED; no
completed proof/disproof submitted.

## First-hit criterion with exact costs checked

New compiled file/olean: FirstHitSharpCost.lean. The theorem
survivor_of_first_hit_cost replaces each support-cardinality-square remainder
by kernelCost(q, canonicalOrthogonal(q,D_i))^2. It is conditional, and its final
axioms are permitted.

Targeted FLOATING diagnostics (not proof certificates):
/tmp/first_hit_exact_cost.py uses canonical supports ordered by product(p+1),
with a finite search cap, and the exact L1-cost formula. Threshold estimates:
  k100:  m/k^2=25.9272, m/p_k^2=.88585
  k1000: m/k^2=59.8371, m/p_k^2=.95418.
/tmp/first_hit_soft_cost.py instead uses the positive profile
  c_Q proportional to (1-t*product(p+1))_+/variance(Q),
where t is the stationary point for the diagonal-mean-plus-rank-one-cost
objective on the selected support. This optimization formula is not yet a
Lean theorem. Estimated thresholds:
  k100:   m/k^2=20.59198, m/p_k^2=.70356
  k1000:  m/k^2=45.33496, m/p_k^2=.72292
  k10000: m/k^2=88.75916, m/p_k^2=.80924.
Outputs /tmp/first_hit_{exact,soft}_cost_<k>.json contain choices.
These do NOT prove an asymptotic obstruction, global optimality, or failure
of all signed kernels. They do not supply a uniform quadratic bound.
Spec.lean unchanged and UNSOLVED; original sorry remains.

## Signed orthogonal coefficient improvement: exact finite example

New compiled file/olean: SelbergSignedExample.lean.
Namespace Erdos970.SelbergSignedExample. All three printed theorems have only
permitted axioms. No changes to Spec.lean.

At the first six primes 2,3,5,7,11,13, define for Q:
  v_Q = product_{i in Q}(p_i-1), a_Q = product_{i in Q}(p_i+1),
  b_Q = (24192-a_Q)_+ / v_Q,
  c_Q = b_Q - (1000/30030)*(-1)^|Q|.
The ordinary-coefficient transform is the same as the general kernel transform.
For X=32668496/5, exact_example kernel-checks:
- all b_Q >=0;
- sum c_Q = sum b_Q >0 (positivity proved separately);
- c_full <0;
- ordinary(c)_T = ordinary(b)_T except full T, where it decreases by1000;
- cost(b)=X and cost(c)=cost(b)+1000;
- X*meanSquare(c)+cost(c)^2 < X*meanSquare(b)+cost(b)^2.
real_objective_improves transfers the comparison to the actual real
FiniteSelberg.average and kernelCost definitions. both_upper proves that both
squares, normalized by their common positive value at the empty pattern,
are valid upper weights on EVERY Boolean pattern.

This proves improvement over this positive cutoff profile. It is NOT a uniform
quadratic bound, a global signed-kernel optimum, or a formally proved optimum
over the entire nonnegative cone. Do not conflate those claims.

Diagnostic scripts (FLOATING, not certificates):
- /tmp/selberg_signed_qp.py: convex ordinary-coefficient L1-penalized square
  optimization, implemented with split nonnegative variables and L-BFGS-B.
  Samples n4,8,12 at X100,10000,1000000 were stationary at the positive profile.
- /tmp/selberg_kkt_scan.py found inactive-coordinate KKT violations for positive
  profiles at much larger cutoffs: n6 aroundL24915, and larger n. This led to the
  exact rational example above, using L24192, not a floating cutoff.
For n6 the exact alternating truncated-product sum is34482, whereas the product
of the six primes is30030; their ratio821/715>1 gives a signed improving direction.

Lean caution: parenthesize the height summand `(prime i + 1)` in the product.
Without parentheses, `prod i in Q, prime i + 1` parses as `(prod prime)+1`.
The verified file uses the correct parenthesized definition.

The original conjecture remains UNSOLVED with its sole sorry at Spec.lean2177.
No completed proof/disproof has been submitted.

## Global positive and signed kernel optimization certified

New compiled files/oleans, all printed theorem axioms permitted:
- SelbergPositiveOptimum.lean
- SelbergSignedOptimum.lean
- SelbergExactSignedOptimum.lean
- FirstHitSigned.lean

No changes to Spec.lean. Its original conjecture is STILL UNSOLVED.

SelbergPositiveOptimum:
- gap_identity: exact quadratic objective difference, under a fixed coefficient
  sum and complementary slackness.
- minimizes_nonnegative: a sufficient KKT certificate for global minimization
  of X*sum(v_i*c_i^2)+(sum(a_i*c_i))^2 over nonnegative coefficients.
- cutoff_minimizes: the profile (L-a_i)_+/v_i is globally optimal when
  X=sum(a_i*(L-a_i)_+/v_i), not merely stationary on a selected support.
- In the six-prime example, base_minimizes_all_nonnegative proves optimality
  of the old L=24192 profile over ALL REAL nonnegative orthogonal coefficients
  with its fixed empty-pattern value.
- signed_beats_all_nonnegative upgrades the old finite signed improvement to
  strict separation from that entire nonnegative cone (same normalization).

SelbergSignedOptimum:
- A general linear transform A, coefficient cost sum_t |(A*c)_t|, and diagonal
  mean are used to formulate a signed primal-dual certificate.
- cost_subgradient and minimizes_all prove global optimality among ALL REAL
  signed c of a prescribed sum if |s_t|<=1, s_t*(A*b)_t=|(A*b)_t|, and
    X*v_i*b_i + cost(A,b)*(A^T*s)_i = alpha for every i.
- No numerical convergence or convex-optimizer assertion is an assumption.

SelbergExactSignedOptimum, namespace Erdos970.SelbergSignedExample:
- Exact unrestricted optimum for first six primes, X=32668496/5, sum(c)=1.
- Let L=84045836/3477, S=524479326553/4172400, t=(L-19740)/14400.
  Before division by S, the coefficients are (L-height(Q))/variance(Q),
  except at full-minus-{0} and full-minus-{1}, where they are t, and full,
  where the coefficient is -t.
- The dual signs are (-1)^|T| except at full (=-1), full-minus-{1}
  (=-11304661/12430275), and full-minus-{0} (=-4270223/12430275).
- optimum_certificate checks the rational primal-dual equations with
  `decide +kernel`.
- matrix_image, matrix_cost, matrix_adjoint, matrix_objective transfer this
  certificate to the actual real FiniteSelberg mean and kernelCost.
- optimum_minimizes_all proves global optimality over ALL REAL signed
  orthogonal coefficients with sum1.
- Exact optimum objective: 94136607674833920/74925618079.
- Ratio (optimal nonnegative objective)/(optimal signed objective) is exactly
  4045983376266/4045981553225 = approximately1.0000004505806506.
- optimum_gain formally proves strict improvement but less than1 part per
  million in this finite example. No asymptotic obstruction or improvement
  is inferred.

Diagnostic antecedents (not proof certificates):
- /tmp/selberg_signed_qp.py 6 6533699.2 found a floating stationary point.
- /tmp/selberg_exact_optimum.py derives/checks the exact rational formulas
  using Fraction; /tmp/selberg_exact_optimum.json records them. These outputs
  are NOT trusted by Lean: optimum_certificate independently checks all
  required identities and inequalities.

FirstHitSigned, namespace Erdos970.FiniteSelberg:
- linearKernel_eq_sum_of_avoids_support.
- linearKernel_hit_average_of_not_mem, independent of coefficient signs.
- first_hit_signed_sum_ge_one for normalized prior-supported kernels.
- survivor_of_first_hit_signed: a survivor follows if
    sum_i [m*q_i*sum_Q(c_i(Q)^2*variance(Q)) + kernelCost(c_i)^2] < m,
  provided each c_i is supported on coordinates preceding i and sums to1.
  This extends the earlier canonical-only first-hit criterion. The displayed
  uniform inequality at m=C*k^2 remains UNPROVED.

Lean caution: parenthesize an entire additive summand of a big sum too,
not just big products. The final first-hit quantitative hypothesis uses
`sum i, (meanTerm i + costTerm i)` with explicit parentheses, preventing an
accidental free implicit i outside the binder. The final file compiles.

The six-prime gain is finite and tiny; it does not remove a logarithmic loss.
No family of signed kernels, nor any positional argument, has been established
uniformly at quadratic length. No proof/disproof was submitted.

## Actual parity-discrepancy energy over complete periods

The original conjecture is STILL UNSOLVED. Spec.lean has not changed.
The interval/increment and optimal-core reductions were re-examined; no uniform
largest-prime increment or quadratic cover-budget inequality was proved.
No old adjacent-gap scans or cover optimizers were restarted.

New compiled files/oleans (all printed theorem axioms permitted):
- ParityDiscrepancyCovariance.lean
- ParityDiscrepancyEnergy.lean
- ParityDiscrepancyInterval.lean
- ParityDiscrepancyUnbounded.lean
Namespace Erdos970.ParityDiscrepancy.

Definitions:
- residueSign d a = (-1)^(a mod d), rational-valued.
- primeProduct P = product of the natural primes in P.
- profile P a = sum_{Q subset P} (-1)^|Q| * residueSign(product Q,a).
- survivorIndicator P a = 1 if no p in P divides a, otherwise0.
- alternatingCount P a m = sum_{j<m} (-1)^j * survivorIndicator P (a+j).
  This is the difference between counts on even and odd OFFSETS. Its absolute
  value is also the absolute difference between actual integer parities.

Exact verified identities:
- covariance_joint_period: for odd g,d,e with gcd(d,e)=1,
    sum_{a<g*d*e} residueSign(g*d,a)*residueSign(g*e,a) = g.
  Proof groups by the common remainder modg and uses CRT for d,e. The sign
  sums over any odd modulus equal1. covariance_multiple extends to multiples.
- covariance_subsets: over N=product(P), Q,R subsetP,
    sum sign(productQ,a)*sign(productR,a)
      = N*(product(Q intersection R))^2/(productQ*productR).
- covarianceKernel_sum: the signed double subset sum factors as
    product_{p in P}(2-2/p).
- profile_energy: sum_{a<N} profile(P,a)^2 = N*product(2-2/p).
- profile_succ: profile(P,a)+profile(P,a+1)=2*survivorIndicator(P,a+1).
- profile_period.
- alternatingCount_odd_period: for every ODD t,
    alternatingCount(P,a+1,N*t)=profile(P,a).
  This is a telescoping identity, so the following results concern actual
  interval survivors, not synthetic moment populations.
- alternatingCount_energy: same energy formula for these actual counts.
- alternatingCount_eq_card_difference: explicit equality with the difference
  of the two natural cardinalities (cast to rationals).
- energy_product_lower: product(2-2/p)>=(4/3)^|P| for odd prime sets.
- exists_large_alternatingCount: if B^2<(4/3)^|P|, some start a+1 with a<N
  has absolute discrepancy>B for every prescribed odd period multiple.
- unbounded_parity_discrepancy: for ANY natural A,C,M,K there are an odd-prime
  set P, an interval start a, and lengthm such that |P|>=K, |P|>0, m>=M,
  m>=C*|P|^2, and |alternatingCount(P,a,m)|>A*|P|.
  The proof uses an elementary cubic Bernoulli inequality, a finite set of
  arbitrarily many odd primes, and an odd multiple of the complete period.

IMPORTANT LIMITATIONS:
- m is an odd multiple of product(P), and can be enormous compared with |P|^2.
- This does NOT prove failure of an O(k) parity estimate at EXACT quadratic
  length. It only disproves such an estimate uniformly on ALL long intervals.
- The construction is NOT an interval cover and NOT a disproof of Erdős970.
- It does NOT disprove LargestPrimeIncrement: the parity modulus2 is smaller,
  not larger, than the old primes.
- No uniform short-interval survivor lower bound was obtained.

A possible strengthening, NOT FORMALIZED OR CLAIMED PROVED:
One may be able to exclude O(k) parity balance even at exact k^2 lengths by
using zero-residue sieving by all odd primes<=sqrt(m), then padding with primes
>m (which hit none of [1,m]). For m<=y^2, odd survivors of the y-sieve are1
and primes>y, and even survivors correspond under division by2. Differences
of two parity discrepancies therefore control pi(m)-2*pi(floor(m/2)), up to
O(pi(y)+1). A hypothetical O(sqrt(m)) parity bound would force that dyadic
prime-count discrepancy to be O(sqrt(m)), which together with pi(x)/x->0
would imply pi(x)=O(sqrt(x)), contradicting Euler divergence (or the verified
prime-count lower bounds). Extending exact-square bounds to nearby lengths
costs O(sqrt(m)). This requires careful floor, cutoff, cardinality-padding,
and dyadic-telescoping arguments; none have been added or used as a theorem.
Even a successful strengthening would remain an obstruction to a counting
shortcut, not a proof/disproof of the quadratic Jacobsthal conjecture.

Spec.lean retains its sole original sorry at line2177. No proof was submitted.

## Exact quadratic parity obstruction, including every fixed scale

The original conjecture remains UNSOLVED; Spec.lean is unchanged.
The previously proposed parity strengthening is now proved in the following
compiled development files (their oleans are built, final axioms permitted):
- PrimeCountingDyadicDiscrepancy.lean
- ParityRoughCounts.lean
- ParitySquarePadding.lean
- ParityExactQuadratic.lean
- ParityScaledSquarePadding.lean
- ParityExactScaledQuadratic.lean

PrimeCountingDyadicDiscrepancy proves pi(n)/n -> 0 using the elementary
Chebyshev upper bound. Combining the verified logarithmic lower bound with a
four-adic telescoping recurrence proves that
  |pi(4^(n+1))-4*pi(4^n)| / 2^n
is unbounded, even after any finite prefix is discarded. No PNT is assumed.

ParityRoughCounts proves that odd survivors in [1,m] after excluding all odd
primes <=y are exactly 1 and the primes >y, for y<=m<=y^2. Thus their count is
pi(m)-pi(y)+1. Doubling identities for the alternating survivor count D yield,
for P=oddPrimes(2s),
  D_P(4s^2)+D_P(2s^2)-2D_P(s^2)
    = pi(4s^2)-4*pi(s^2)+3*pi(2s)-3.

Padding adds primes above the interval endpoint, so these added classes are
inactive. Endpoint changes between squares cost only O(sqrt(m)). A hypothetical
uniform bound |D_P(C*|P|^2)| <= A*|P| at any fixed natural C>0 would therefore
force the forbidden four-adic prime-count estimate. pi(n)/n -> 0 provides the
small-core cardinality condition needed for arbitrary C.

Final theorems, namespace Erdos970.ParityDiscrepancy:
- unbounded_parity_at_exact_quadratic A C K (C>0): there is an odd-prime set P
  with |P|>=K, |P|>0 and |D_P(C*|P|^2)| > A*|P|.
- unbounded_parity_with_survivor: same, with survivorIndicator P 1=1 explicitly.
- no_real_uniform_parity_estimate C K (C>0): no real constant A bounds this
  absolute discrepancy by A*|P| for all |P|>=K.

CRITICAL LIMITATIONS: These are not interval covers; 1 survives. Padding uses
inactive primes, so no failure is proved for optimal or all-active prime cores.
The parity prime 2 is smaller than the old odd primes, so this does not refute
LargestPrimeIncrement. Neither a quadratic Jacobsthal bound nor a superquadratic
cover construction follows. No proof/disproof of erdos_970 has been submitted.

## Boolean-reduced first-hit coefficient costs

The original conjecture remains UNSOLVED. Spec.lean is unchanged (same SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9).

New compiled files/oleans; all printed final axioms permitted:
- FirstHitBooleanCost.lean
- FirstHitDisjointCost.lean
- FirstHitBooleanExample.lean
Namespace Erdos970.FiniteSelberg (BooleanExample for the finite example).

Define booleanSquareCoefficient(a,T) = sum_{Q union R=T} a(Q)*a(R).
This merges ordinary coefficients using the Boolean identity X_i^2=X_i.
booleanSquareCost(a) is the L1 norm of this merged list.
Verified:
- booleanSquare_expansion: exact polynomial identity on every Boolean pattern.
- booleanSquareCost_le: this cost is <= (sum_T |a(T)|)^2.
- arbitrary_square_hit_boolean_error: the improved moment-error bound.
- survivor_of_first_hit_boolean_cost: the signed prior-supported first-hit
  criterion with each kernelCost^2 replaced by booleanSquareCost of the kernel's
  ordinary coefficients. Still CONDITIONAL on the displayed total being <m.
- ordinaryCoefficient_prior and booleanSquareCoefficient_prior.
- hitShift_expansion, hitShift_cost, hitShift_max, hitShift_disjoint.
- firstHit_boolean_merged_cost: different first-hit indices have disjoint
  monomial supports (each monomial's largest index is its first-hit index).
  Therefore merging across indices gives EXACTLY the sum of the individual
  Boolean-reduced costs, with no further cross-index coefficient cancellation.

Exact finite example: two marginals1/2,1/3, first kernel1 and second kernel
1-X_0. At m12 the old mean-plus-cost total is13, while the Boolean-reduced total
is11. normalized, prior, exact_objectives, strict_improvement, survivor compile.
This proves a strict improvement to this criterion, not a new asymptotic bound
or global optimization result.

FLOATING diagnostics (not Lean certificates):
/tmp/first_hit_boolean_data.py writes the same positive soft cutoff kernels
used before; /tmp/first_hit_boolean.cpp merges their squared coefficients by
lcm of squarefree divisor indices. New cost / old cost is about0.51--0.52.
Tested (k, m/k^2, new criterion score):
  100,12 ->1.0004463; 100,13 ->.9983574;
  1000,25 ->1.0009092; 1000,30 ->.9987130;
  10000,50 ->1.0005242; 10000,60 ->.9992372.
A score<1 means these floating coefficients pass the tested sufficient formula,
not that a Lean certificate or uniform family has been constructed.
At k1000,target ratio25, using a soft profile originally optimized for ratio50
improves the score to .9989685; this is a targeted rescaling, not a global optimum.
No asymptotic failure theorem is inferred from these increasing finite ratios.
No proof/disproof of erdos_970 has been submitted.
The additional /tmp/first_hit_boolean_signs.cpp diagnostic found no coefficient
with sign opposite to (-1)^|T| among the tested k100,ratio13 and k1000,profile50
squared kernels (tolerance1e-10). This is NOT a theorem for this family and does
not rule out cancellation between kernels built using different prime orders.
All diagnostics from this round have finished; no worker remains running.

## Universality and dual certificates for Boolean-reduced kernels

Original conjecture STILL UNSOLVED. Spec.lean unchanged, sole original sorry
still at line2177. No proof/disproof has been submitted.

Four new compiled files/oleans (all printed final axioms permitted):
- BooleanKernelUniversal.lean
- BooleanKernelDuality.lean
- BooleanKernelUpperWeights.lean
- BooleanKernelExactOptimum.lean
Namespace Erdos970.FiniteSelberg; BooleanOptimum for the exact example.

BooleanKernelUniversal:
- full_reproducing_factorization and full_reproducing_delta: the complete
  orthogonal kernel is a delta after multiplying by the Bernoulli atom mass.
- fourierCoefficient and linearKernel_fourierCoefficient: explicit inversion
  for every real-valued function on the finite Boolean cube, for0<q_i<1.
- exists_square_kernel, exists_normalized_square_kernel: every nonnegative
  Boolean function is a squared signed orthogonal kernel. Normalization f(0)=1
  can be realized with sum(c)=1. This alone says nothing about coefficient cost.

BooleanKernelDuality:
- booleanValue, booleanObjective (X*mean + L1 of ordinary coefficients).
- BooleanDualFeasible q X w: w>=0 and EVERY intersection moment is within1 of
  X*product(q_i), INCLUDING the empty moment (total mass may be X+/-1).
- weighted_boolean_error, booleanObjective_dual_bound: a normalized nonnegative
  upper polynomial has objective at least w(empty) for every such population.
- booleanObjective_minimizes: a matching candidate certifies global optimality.
- booleanKernelObjective, booleanValue_square, booleanObjective_square,
  booleanKernelObjective_dual_bound: transfer to arbitrary signed kernels with
  the exact Boolean-reduced cost. No optimizer assumptions or coefficient-sign
  restrictions occur in these theorems.

BooleanKernelUpperWeights:
- booleanValue_at_subset and booleanValue_injective: uniqueness of multilinear
  coefficients on the full Boolean cube.
- upperWeight_is_normalized_square: every normalized nonnegative upper weight
  has EXACTLY the ordinary coefficients of a normalized squared kernel.
- upperWeight_objective_attained: therefore the representation preserves the
  objective exactly. With full support and exact Boolean costs, unrestricted
  signed kernels do not exclude any nonnegative upper polynomial on that cube.
  This is a representation theorem, not a bound on the optimum as k grows.

BooleanKernelExactOptimum:
- First six marginals1/2,1/3,1/5,1/7,1/11,1/13; X=1000.
- rational_certificate independently kernel-checks rational primal feasibility,
  dual nonnegativity and ALL64 intersection errors, empty normalization, and
  matching objective54668/231. Uses decide +kernel, not native_decide.
- The primal has28 coefficients, all +/-1; the dual has45 nonzero atom weights.
  The primal ignores the sixth coordinate. Equivalently it is
    (1-X0)*(1-X1) *
      [1-X2-X3-X4 + X2*X3+X2*X4+X3*X4],
  which is an upper weight allowing either zero or three hits on coordinates2,3,4.
  This displayed formula is explanatory; the compiled certificate checks the
  explicit coefficient table, not an asserted formula or external computation.
- exact_objective, dual_feasible, global_upper_weight_optimum,
  global_kernel_optimum: global optimum over ALL real normalized nonnegative
  Boolean upper weights, and hence over ALL real signed normalized orthogonal
  kernels on this six-coordinate cube. Attainment follows from universality.

Diagnostic antecedent, NOT trusted by Lean:
/tmp/boolean_kernel_lp.py uses SciPy linprog for primal and dual, then checks
rational reconstructions with Fraction. n6,X100,300,1000 reconstructions passed;
only the X1000 certificate was formalized. n8,X1000 rationalized dual failed
its exact error test by a tiny amount, so it is NOT a certificate or theorem.
The relevant verified input table is /tmp/boolean_kernel_lp_6_1000.json, but
Lean checks the copied rational table independently.

Scope: Dual populations are abstract nonnegative weighted cube populations,
not necessarily interval prime-class populations. This finite optimum does not
prove an asymptotic obstruction, a uniform quadratic survivor bound, or a cover.
The required uniform quantitative inequality remains unproved.

Lean cautions encountered: parenthesize the entire summand a(Q)-b(Q), even in
an already-parenthesized sum expression. Reduce lambda applications before rw.
For large rational objective identities, congrArg Rat.cast followed by push_cast
was more reliable than exact_mod_cast with reducible real definitions.
No worker from this round remains running.

## Lossless rare-coordinate reduction for the exact first-hit class

Original conjecture STILL UNSOLVED. Spec.lean unchanged; original sorry at2177.
Two new files compile and have built oleans; all printed final axioms permitted:
- BooleanKernelTailReduction.lean
- BooleanKernelRestriction.lean
Namespace Erdos970.FiniteSelberg.

BooleanKernelTailReduction:
- restrictBooleanPattern S sets every coordinate outside S to false.
- restrictBooleanCoefficient S deletes exactly monomials not contained in S.
- hitMonomial_restrict and booleanValue_restrict identify these operations.
- booleanObjective_eq_sum writes the exact objective as a sum of terms
    X*product(q_i)*a_T + |a_T|.
- expected_monomial_le_one: if0<=q_i<=1, X>=0, and X*q_i<=1 outside S, then
  every discarded monomial has expected mass at most1.
- coefficient_term_nonneg and booleanObjective_restrict_le: each discarded term
  contributes nonnegatively, so restriction does not increase the objective.
- admissible_upper_restrict preserves nonnegativity and empty normalization.
- exists_upper_below_iff_restricted: exact equivalence at EVERY objective
  threshold B, with or without the support restriction. No strong-duality or
  existence-of-minimizer assumption is needed.
- booleanActiveCore q X = {i: X*q_i>1}.
- prime_upper_below_iff_active: at prime marginals, only primes STRICTLY BELOW X
  need occur in a normalized nonnegative upper polynomial. The equality case
  p=X is also removable.

BooleanKernelRestriction:
- restrictOrthogonal S c(R) = sum_{Q intersection S=R} c(Q).
  This is an explicit linear coefficient operator; it does not need a square
  root, optimization, or existence-only choice of a new kernel.
- basis_restrictPattern and linearKernel_restrictOrthogonal identify it with
  restricting the original kernel to the subcube.
- restrictOrthogonal_sum preserves sum(c), restrictOrthogonal_nonzero and
  restrictOrthogonal_supported describe its support.
- booleanSquare_restrictOrthogonal: the squared ordinary coefficient lists
  agree EXACTLY with the corresponding Boolean polynomial restriction.
- booleanKernelObjective_restrict_le: exact objective nonincrease.
- reduceFirstHitKernels uses activeCore(q,m*q_i) at first-hit index i.
- reduceFirstHitKernels_normalized and reduceFirstHitKernels_support preserve
  normalization and prior support, and ensure every remaining coordinate j has
    j<i and (m*q_i)*q_j>1.
- reduceFirstHitKernels_objective_le: sum of all objectives does not increase.
- reduceFirstHitKernels_prime_support: for prime marginals every remaining
  coordinate satisfies j<i and p_i*p_j<m.
- firstHit_candidate_iff_reduced and prime_firstHit_candidate_iff_reduced:
  the entire existential successful first-hit Boolean-cost criterion is
  equivalent to its restricted form. No successful candidate of THIS type is
  lost by forbidding pairs with p_i*p_j>=m.

Scope: this is a normal-form/search-space reduction for an upper-weight/first-hit
method, not a survivor estimate or a theorem about all possible sieve methods.
No uniform family satisfying the reduced criterion at m=C*k^2 has been found.
The reduction does not prove that any such family must fail, and does not
construct an actual interval cover. No proof/disproof was submitted.
No numerical optimizer or background worker was started in this round.

## Coupled global coverage weights versus all first-hit kernels

Original conjecture STILL UNSOLVED. Spec.lean unchanged; original sorry at2177.
New compiled files, with oleans built and printed axioms only propext,
Classical.choice, Quot.sound:
- BooleanCoupledDuality.lean
- BooleanCoupledExample.lean
- BooleanSymmetric.lean
- BooleanCoupledSurvivorExample.lean

BooleanCoupledDuality (namespace Erdos970.FiniteSelberg):
- weighted_boolean_error_supported: only moments for nonzero monomials need
  error bounds. booleanObjective_supported_dual_bound is the associated dual.
- FirstHitDualFeasible q m w constrains the nonnegative population w_i only on
  subsets strictly preceding i; its moment target is m*q_i*product(q_j).
- firstHit_objective_dual_bound bounds EVERY signed normalized prior-supported
  kernel family by the sum of the feasible duals' empty-atom masses.
- IsCoverageMajorant a means a(empty)=0 and value(a)>=1 on all nonempty patterns.
  Such a polynomial need not have nonnegative first-hit increments.
- survivor_of_coverage_majorant: objective(q,m,a)<m guarantees a survivor for
  every interval-indexed population with all unit-error intersection moments.
- coverageObjective_dual_bound: a nonnegative population with empty atom0 and
  nonempty moments within1 of m*product(q) lower-bounds every coverage objective
  by its total mass. IMPORTANT: total mass is NOT constrained in this dual.

BooleanCoupledExample (namespace ...CoupledExample):
- Six equal marginals1/3, m100. These are NOT distinct-prime marginals.
- Explicit coverage polynomial with coefficients by subset size:
    size1:1, size2:-5/6, size3:1/2, otherwise0.
- Rational prefix_certificate, global_certificate, primal_certificate checked
  independently with decide +kernel, then cast to reals.
- Exact global optimum6839/54 versus lower bound385/3 for ALL first-hit families.
- strict_method_gap: global objective+91/54 <= every first-hit objective.
- Both exceed100. This is an objective gap, not a survivor-detection gap.

BooleanSymmetric (namespace ...BooleanSymmetric):
- patternEquivFinset identifies Boolean patterns and finite subsets.
- sum_card_powerset, sum_card reduce cardinality-only sums to binomial sums.
- fixed_subset_sum and symmetric_moment: for T subset S, the moment of a
  weight f(|omega|) supported on S equals
    sum_{t=0}^{|S|-|T|} choose(|S|-|T|,t)*f(|T|+t).
- symmetric_value similarly reduces a cardinality-only polynomial's value.
- These are general algebraic proofs, not finite unchecked computations.

BooleanCoupledSurvivorExample (namespace ...CoupledSurvivorExample):
- Eight equal marginals1/4, m1700. Again NOT distinct-prime marginals.
- Explicit coefficients by subset size:
    1:1, 2:-199/224, 3:149/224, 4:-37/112, 6:15/112, otherwise0.
- Global optimum6928287/4096=1691.476318359375<1700.
- Every normalized signed prior-supported first-hit objective is at least
    6998085/4096=1708.516845703125>1700.
- prefix_reduced, global_reduced, primal_reduced independently check the
  rational binomial sums with decide +kernel. The generic symmetry lemmas
  transfer them to ALL cube moments and values. Then casts transfer to reals.
- global_optimal proves exact optimality over all real coverage majorants.
- global_survivor proves survivor existence for any population with the stated
  unit-error moment bounds at m1700.
- no_successful_firstHit excludes ALL signed normalized prior-supported
  first-hit kernel families meeting their exact merged-cost criterion.
- strict_method_gap is the objective gap34899/2048.
- The original direct whole-cube decision attempt exceeded the10GiB memory
  limit (exit137). It was replaced, not trusted or bypassed, by the generic
  cardinality reduction. The final file compiles successfully.

Certificate-generation diagnostics, not trusted by Lean:
  /tmp/coupled_survivor_certificate.py
  /tmp/coupled_survivor_certificate.json
Both Python Fraction reconstruction and the subsequent independent Lean checks
succeeded. The formalized tables are entirely present in the Lean file.
Compilation log: /tmp/coupled_survivor_lean.log.

Other numerical diagnostics from the preceding round:
  /tmp/global_vs_firsthit.py, /tmp/global_vs_firsthit_q.py,
  /tmp/global_firsthit_roots.py, /tmp/global_firsthit_symmetric_certificate.py.
Global and first-hit LP values matched at sampled masses for first6,8,10 primes,
for clusters101..127 and5..19, and for harmonic reciprocal denominators2..9 and
3..10. This is NOT a theorem of equality for prime marginals. Synthetic output
filenames indexed only by n,m may have been overwritten across marginal lists;
use the dedicated certificate JSON, not those ambiguous diagnostic outputs.
For equal q1/4,n8 the numerical thresholds differed, motivating m1700.

Scope and current obstacle:
The new survivor-detection separation establishes that the unrestricted global
polynomial class can genuinely outperform all first-hit kernels in some models.
It does NOT establish a gain for distinct-prime marginals, an asymptotic family,
a uniform quadratic survivor bound, or a superquadratic interval cover.
Virtual-hit domination only transfers a successful sufficient bound in the
appropriate direction; it cannot transfer the first-hit failure to smaller
prime marginals. No such invalid inference has been used.
The dimension-one sieve threshold and the previously unproved largest-prime
increment route were reconsidered; no new quantitative estimate resolving them
was obtained. No proof/disproof of erdos_970 has been submitted.

## All-active concentration obstruction at exact quadratic scale

Original conjecture STILL UNSOLVED. Spec.lean unchanged, original sorry at2177.
Three new development files compile, with built oleans. Printed axiom lists
contain only propext, Classical.choice, Quot.sound:
- ActivePrimePadding.lean (namespace Erdos970.ActivePrimePadding)
- ActivePrimeSupply.lean (same namespace)
- ActiveQuadraticConcentration.lean (same namespace)

This round revisited the actual interval/critical-cover and largest-prime routes,
not the abstract equal-marginal polynomial examples. No quantitative estimate
proving the largest-prime increment was found. Local references supplied no new
result; erdosproblems.com remained inaccessible (DNS resolution failure).
Old adjacent-gap or cover-optimization scans were NOT repeated.

A genuinely new construction removes the INACTIVE-PADDING caveat from the
previous relative-concentration obstruction. It is entirely an actual finite
prime-class interval construction, not a moment relaxation.

ActivePrimePadding:
- residue_card_le: any q-class in [0,m) has at most floor(m/q)+1 points.
- exists_safe_pair: if S subset [0,m), each q-class has at most d points, and
    q + |Z|*d < |S|,
  then two distinct candidates of S lie in a common q-class avoiding ALL protected
  points Z. Uses a union bound on protected residue classes and pigeonhole.
- HasWitnesses m P r W stores two private witnesses in W per old class.
- private_preserved, new_private, survivor_loss give the exact insertion facts.
- pad_active: for a disjoint supply R of positive moduli, all <=H and with class
  counts <=d, if
    H + (3*|R| + |W| + |Z|)*d < old survivor count,
  one can assign ALL R residues, preserving the old residues, avoiding Z, and
  keeping at least two private positions for EVERY class in P union R.
  This lemma does not require primality. The proof inserts one modulus at a time;
  each insertion loses at most d survivors and adds at most two protected witnesses.

ActivePrimeSupply:
- exists_prime_supply D L K: there exist k>=K, k>0, H and exactly k primes R with
    D*k < q < H for all q in R, and L*H < k^2.
  This is a SUBSEQUENCE assertion, not a prime-number asymptotic. It follows from
  the previously proved exists_nth_prime_small (Euler divergence), taking
  k=floor(n/(D+2)), discarding primes <=D*k, then selecting exactly k primes.
- zero_survivors_lower: for a fixed zero-residue core of product N,
    floor(m/N) <= survivor count,
  using the progression1 mod N.
- coreWitnesses P = P union {p^2:p in P}; card <=2*|P|. For m>p^2 each core
  prime p has private witnesses p and p^2 under zero residues.
- padding_budget: elementary integer arithmetic supplying pad_active's room
  condition at quadratic lengths, with d=floor(k/(8N))+1 and k>=64N.

ActiveQuadraticConcentration:
- unbounded_active_exact A B C K (C>0) constructs P,r,p,m such that:
    K <= |P|,
    m = C*(|P|+1)^2,
    every q in P is prime and q<p, and p is prime,
    EVERY q in P has at least TWO private positions before insertion,
    EVERY q in insert p P has at least TWO private positions after inserting
      the zero residue class for p,
    1 survives the old classes, and
    B*oldSurvivorCount + A*p < p*removedCount.
  Here removedCount counts the old survivors congruent to0 mod p.
- not_uniform_active_relative_estimate C K (C>0): arbitrary real constants A,B
  cannot give removed <= B*oldSurvivors/p + A uniformly at this exact scale,
  even imposing the two-private-point conditions BOTH before and after insertion.
- one_survives_insert explicitly shows that survivor1 also survives the inserted
  prime class. Thus these counterexamples are NOT interval covers.

Construction details:
Take T=A+2, L=2(T+1), and a fixed zero-residue prime core P0 with all primes>T
and sufficiently small totient density. Let N=product(P0), F=product(q-1).
Select k new primes in (D*k,H), D=32*C*N, with (8N+L)*H<k^2, using the new
prime supply lemma. Take m=C*(|P0|+k+1)^2 and use Bertrand to choose p between
floor(m/L) and twice that number; all supply primes and core primes are below p.
Protect core witnesses p0,p0^2, point1, and ALL multiples j*p with j<L.
The greedy lemma assigns the new residues while preserving the protected points
and two private witnesses per class. The room bound follows from floor(m/N)
initial candidates and d=floor(k/(8N))+1 per supply-prime class.
The old survivor count stays bounded ABOVE by the fixed core's count, giving
B*S<=p, while p,2p,...,T*p remain survivors, giving removed>=T=A+2.
Protecting all multiples of p ensures every newly added class's private witnesses
also survive insertion of p. Core witnesses are prime powers of primes below p,
so survive that insertion as well. The inserted class itself has private witnesses
p and2p, and point1 remains uncovered.

IMPORTANT SCOPE:
- These examples have genuinely active classes, not padding by primes with zero
  or one private position. This closes that particular caveat in the earlier
  QuadraticScaleConcentration theorem.
- Residues of the new padding classes are chosen, so the old residue vector r
  is NOT identically zero. The fixed core alone retains zero residues.
- No GLOBAL OPTIMALITY property is asserted. All-active is weaker than optimal,
  and a concentration estimate restricted to globally optimal/critical covers
  is NOT refuted here.
- LargestPrimeIncrement remains unproved and is NOT negated by this result.
- Neither a quadratic Jacobsthal upper bound nor a superquadratic interval-cover
  family was obtained. No proof/disproof of erdos_970 has been submitted.

Build logs:
  /tmp/active_padding_lean.log
  /tmp/active_supply_lean.log
  /tmp/active_quadratic_lean.log
No numerical solver was used in this construction. No background worker remains.

## Positive soft-kernel bound: exponent six verified

Original quadratic conjecture STILL UNSOLVED. Spec.lean unchanged, original sorry2177.
This round returned to a positive sieve estimate rather than another obstruction.
Four new files compile with built oleans; all printed final axioms permitted:
- SelbergSoftEnergy.lean
- PrimeLogMoments.lean
- SelbergSoftPrimeBound.lean
- SixthPowerBound.lean

The new unconditional conclusion is
  jacobsthalFunction k <= 2^50 * (k+1)^6,
and consequently an existential O(k^6) bound. This improves the previously
formalized exponent633, but is NOT the original O(k^2) conjecture.

SelbergSoftEnergy (namespace Erdos970.FiniteSelberg):
softProfile u L Q = max(L - sum_{i in Q} u_i, 0).
- Coordinate differences are at most u_i for u_i>=0.
- weighted_additive_sum computes the mean additive profile exactly under weights
  weight(q,Q)=product q_i/(1-q_i).
- weighted_square_sum is weighted Cauchy-Schwarz.
- softProfile_energy_lower: if sum q_i*u_i<=M, sum q_i*u_i^2<=V and M<=L, then
    W*((L-M)^2-V) <= kernelEnergy(q, weight*softProfile),
  where W=sum_Q weight(q,Q). Uses the existing exact Dirichlet-form identity.
- softProfile_energy_pos specializes to moment bounds65/64*M and65/64*M^2,
  L=5/2*M, and gives energy>=M^2, using W>=1.

PrimeLogMoments (namespace Erdos970.WeightedMertens):
- log(x)/x is decreasing for x>=z when log z>=1.
- log(x)^2/x is decreasing for x>=z when log z>=2, proved by applying
  log(y)<=y-1 to y=sqrt(x/z), not by assuming a prime asymptotic.
- For any finite prime set P, z>=64 and64*|P|<=z:
    sum_P log p/p <=65/64*(log z+log4),
    sum_P (log p)^2/p <=65/64*(log z+log4)^2.
  Small primes use the existing elementary weighted Mertens upper bound.
  Arbitrarily large primes are handled by monotonicity and the cardinality budget.

SelbergSoftPrimeBound:
- For u_i=log p_i, the profile vanishes outside product p_i<=floor(exp L).
- prime_soft_cost_le gives kernelCost <= L*exp2*exp L, using the already proved
  divisor_cost_sum_le and injectivity of squarefree prime-subset products.
- softBoundConstant=(25/4)*exp4*256^5.
- With z=64*(k+1), M=log z+log4, L=5/2*M, positive energy and cost estimates give
    (card(iota)+1)*kernelCost^2
      <= softBoundConstant*(k+1)^6*kernelEnergy.
- exists_soft_prime_kernel and prime_survivor_soft are unconditional for every
  injective prime list of at most k members. No largest-prime restriction, virtual
  transfer, numerical optimization, or unverified asymptotic is needed.

SixthPowerBound (namespace Erdos970):
- sixthPowerConstant=ceil(softBoundConstant)+1.
- isJacobsthalBound_sixth, jacobsthalFunction_le_sixth,
  exists_sixth_power_bound.
- sixthPowerConstant_le proves sixthPowerConstant<=2^50 using exp1<3.
- jacobsthalFunction_le_explicit_sixth proves the displayed explicit bound.

Logs: /tmp/soft_energy_lean.log, /tmp/prime_logmoments_lean.log,
/tmp/soft_primebound_lean.log, /tmp/sixth_power_lean.log.
Only development files changed; original Spec.lean still has its sole sorry.
No proof/disproof of erdos_970 has been submitted.

## Second logarithmic moment improved; fifth-power transfer pending

PrimeSecondLogMoment.lean compiles, and its olean is built. All printed axioms
are permitted. In namespace WeightedMertens, set
  b = logMomentOffset = 1 + errorConstant + 2*log4 > 0.
The square-root split proves
  sum_{prime p<=z} (log p)^2/p <= (3/4)*(log z)^2 + b*log z.
For any finite prime set P with z>=64 and64*|P|<=z,
  sum_P log p/p <=(65/64)*(log z+b),
  sum_P (log p)^2/p <=(49/64)*(log z+b)^2.
No bound on the largest selected prime is assumed.
The forthcoming soft-profile specialization L=2*(log z+b), z=64*(k+1),
has energy >=(log z+b)^2/8 because (2-65/64)^2-49/64=833/4096>1/8.
This is sufficient for an O(k^5) bound; that transfer is not yet checked.
Original quadratic conjecture remains UNSOLVED, and Spec.lean is unchanged.

## Fifth-power bound verified

SelbergSoftFifthBound.lean and FifthPowerBound.lean both compile, with built
oleans. All printed axiom lists are exactly the permitted three.
In FiniteSelberg:
- softProfile_energy_fifth: under the improved logarithmic moment bounds,
  the profile at L=2*M has kernel energy >=M^2/8.
- fifthBoundConstant =32*exp(4+4*WeightedMertens.logMomentOffset)*64^4 >0.
- exists_soft_prime_kernel_fifth and prime_survivor_soft_fifth give the
  uniform prime-set survivor threshold fifthBoundConstant*(k+1)^5.
In Erdos970:
- fifthPowerConstant =ceil(fifthBoundConstant)+1.
- isJacobsthalBound_fifth k:
    IsJacobsthalBound k (fifthPowerConstant*(k+1)^5).
- jacobsthalFunction_le_fifth gives the corresponding natural bound.
- exists_fifth_power_bound gives the real O(k^5) bound for positive k.
Logs: /tmp/soft_fifth_lean.log and /tmp/fifth_power_lean.log.
These are DEVELOPMENT FILES only. Spec.lean remains unchanged.

This does not settle the original quadratic conjecture. The positive soft
kernel still loses powers in the support cutoff and in the outer cardinality
factor multiplying the squared coefficient cost. The earlier active-class
concentration counterexamples are not complete interval covers and do not
disprove the conjecture. No complete proof/disproof has been obtained.

## Gap-distribution route: exact pair moments and failed stronger count shapes

Original quadratic theorem remains UNSOLVED. Three new files compile with built
oleans and permitted printed axioms only:
- GapPairAverage.lean
- GapPhaseMoments.lean
- GapCountShapeExample.lean

GapPairAverage (namespace Erdos970.GapAverages):
  density(P)=product(1-1/p).
  pairKernel(P,h)=product(1-2/p+[p|h]/p).
The kernel has a nonnegative divisor expansion, including p=2. Exact floor
counts prove sum_{h=1}^n pairKernel(P,h)<=n*density(P)^2, and its triangular
analogue. This is not a pointwise independence assertion.

GapPhaseMoments defines actual independent uniform residue phases, point
indicators, intervalCount, and phaseMean. It proves the exact point and pair
means, followed by
  E S=m*rho,
  E S^2<=m*rho+m*(m-1)*rho^2,
  Var(S)<=m*rho*(1-rho).
The resulting coveredFraction bound is only
  m*rho*Pr(S=0)<=1-rho.
It is not the exponential tail needed for a uniform quadratic conclusion.

GapCountShapeExample kernel-checks P={2,3,5,7}, N=210:
- m38 frequencies at counts9,10,11 are100,20,4, violating ultra-log-concavity.
- m30 has24 phases with >=8 survivors;6 have a coprime left endpoint.
  Since phi(210)=48, endpoint conditioning fails stochastic domination.
Neither counterexample refutes the original conjecture or the proposed
geometric void-probability bound.

Targeted exact-period diagnostics (not Lean certificates):
/tmp/gap_tail_diagnostic.cpp and /tmp/gap_hazard_diagnostic.cpp.
No failure of Pr(S=0)<=(1-rho)^m was found in the specified small prime sets.
The diagnostic initially counted gaps equal to m in the hazard numerator;
this was corrected to count only gaps STRICTLY exceeding m. Corrected output
still showed no failure in those sets. These tests do not prove either bound.
/tmp/count_ulc_diagnostic.cpp and /tmp/endpoint_regression_diagnostic.cpp
produced the stronger-shape failures later certified in Lean.

A new targeted padding construction is being checked next:
For old primes{3,7,11}, N=231, m9, the minimum survivor count is3.
Exactly8 old phases attain this minimum;4 have a coprime left endpoint.
Add new primes101,103,107 (>10). Any full cover of the9 positions must assign
these3 new classes bijectively to the3 old survivors. Thus the predicted full
phase counts are48 covered phases,24 with a surviving left endpoint, while
the full product density exceeds1/2. This would DISPROVE the uniform endpoint
hazard bound, not the geometric void bound and not the original conjecture.
The padding transport and exact counts have NOT yet been Lean checked.

## Uniform endpoint hazard disproved for six genuine primes

GapHazardExample.lean compiles; olean built, all printed axioms permitted.
Namespace Erdos970.GapAverages.HazardExample.
The smaller core found by targeted minimum-count testing is {3,7,11}, period231.
In positions1..9 its minimum survivor count3 occurs at precisely the phases
  5,6,47,48,173,174,215,216;
only5,47,173,215 are themselves coprime to231.
Old_count_certificate kernel-checks this classification over all231 phases.

New primes101,103,107 each hit at most one of the9 positions. Covered_bounds
proves that every full cover must use all3 new residues on the3 old survivors,
so each new residue lies in1..9 and the old phase is one of the8 listed.
Explicit equivalences reduce the full covered phase spaces to finite small
phase spaces; small_count_certificate independently uses decide+kernel.
Full_cover_counts proves EXACTLY48 covered phases and24 with a surviving
left endpoint. The product density of {3,7,11,101,103,107} is
  129744000/257130951 >1/2.
Thus not_product_density_hazard disproves the proposed uniform lower bound
on endpoint hazard by the product density.

The phase space uses an old offset modulo231 and independent forbidden
residues for the3 new primes. It is a genuine residue-class model, not an
abstract Boolean moment population. An explicit equivalence to a single
full-product period is not yet formalized in this file.
This is NOT a disproof of the geometric void-probability inequality, and NOT
a disproof of Erdős970. These length-nine covers have only6 primes.

Independent C++ exact-period diagnostic, not trusted by Lean:
/tmp/gap_hazard_specific.cpp scans all257130951 positions. It agrees:
H=11, minimum hazard/product-density ratio0.990916539493 at m9;
no geometric void bound failure in this period. No workers remain.
Other new logs: /tmp/gap_pair_average_lean.log,
/tmp/gap_phase_moments_lean.log, /tmp/gap_count_shape_lean.log,
/tmp/gap_hazard_example_lean.log. Spec.lean remains unchanged and unsolved.

GapHazardExample now also verifies the exact cardinalities of the FULL phase
space and of its endpoint event, without enumerating the257-million period:
  full_phase_card =257130951;
  endpoint_card =129744000.
Endpoint_equiv factors the event into the120 old units and independent nonzero
new residues. endpoint_probability_decreases_after_cover proves the exact
cross-multiplied finite probability inequality is false. Thus the hazard
obstruction is not based solely on an asserted density interpretation.
All final axioms remain permitted. The explicit CRT equivalence with a single
integer period still has not been added; the model is the genuine independent
old-offset/new-residue phase model described above.

Current mathematical status after this continuation:
- Fifth-power bound is checked (earlier section).
- Actual phase variance <=binomial variance is checked.
- Ultra-log-concavity, endpoint stochastic domination, and the product-density
  endpoint hazard have specific checked counterexamples.
- No proof or counterexample to the GEOMETRIC VOID-PROBABILITY bound has been
  obtained. Finite tests alone give no uniform tail theorem.
- The variance estimate yields only a reciprocal tail and does not control
  the worst residue vector at quadratic interval length.
- The original erdos_970 remains UNSOLVED. No valid proof/disproof was submitted.

Spec.lean unchanged: SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9;
sole sorry at line2177. No active diagnostic or optimizer remains.

## Further exact-cover review (no new theorem)

Re-examined globally optimal cover exchange inequalities, the largest-prime
increment reduction, and exact parity reduction. No implication from the
verified local exchange conditions to a uniform quadratic budget bound was
found. In particular, having two private points per retained class and the
necessary multi-prime replacement inequalities does not assert that an
improving exchange exists.

Also re-examined whether the newly proved phase variance bound can rule out a
single exceptional cover. It cannot by itself: one exceptional residue vector
has probability as small as the reciprocal prime product, far smaller than
the reciprocal upper bound supplied by the second moment.
No new proof of the required worst-case bound was obtained. No Lean source
was changed in this review, and no proof/disproof of erdos_970 was submitted.
Spec.lean retains its original statement and sole sorry at2177.

## Pairwise-coprime extraction review (no new theorem)

Considered proving the quadratic target by extracting k+1 pairwise-coprime
integers from every interval of length C*k^2. Such an extraction would suffice
by pigeonholing prime divisors of the fixed modulus, but no such uniform
extraction theorem was established. The elementary graph/sieve approach does
not resolve the concentration of small-prime survivors into large-prime
classes; it cannot be treated as an independent proof of the target.

Rechecked the smaller-cardinality quadratic bootstrap, including its already
recorded repeated-block and recursively propagated diagnostics. No new
induction inequality closing at C*k^2 was obtained. In particular, the existing
conditional lower-count bounds must not be used at the terminal cardinality.
No Lean source was changed, and no new proof or disproof of erdos_970 was found.

## Arbitrarily isolated coprime integers: local companion shortcut fails

New compiled file and olean: SymmetricIsolation.lean.
Namespace Erdos970.SymmetricIsolation. All final printed axioms are only
propext, Classical.choice, Quot.sound. Log /tmp/symmetric_isolation_lean.log.
No sorry, admit, or native_decide appears in the file.

For every H>=1, use all primes <=H+1 with forbidden relative class H+1,
and a fresh prime q>2H+2 with forbidden class H+2. Among positions0,...,2H,
precisely H survives. There are pi(H+1)+1 primes. Every other position except
H+2 is covered by a prime divisor of its nonunit difference from H+1;
the fresh prime covers H+2. The centre avoids every class.

The elementary prime-density limit pi(x)/x ->0 makes H/(pi(H+1)+1)
unbounded, with the number of primes also arbitrarily large.
Main theorems:
- exists_isolated;
- eventually_small_budget;
- arbitrarily_isolated;
- no_linear_companion_bound.

CRT transport is fully proved, not left implicit:
- realize_residue_configuration realizes the entire avoidance predicate by
  coprimality to one positive integer with exactly the prescribed prime factors;
- arbitrarily_isolated_integer;
- arbitrarily_isolated_center: for arbitrary A,K, obtains n>0, c in Z, H,
  omega(n)>=K, A*omega(n)<H, and for every integer |t|<=H,
  gcd(|c+t|,n)=1 iff t=0;
- no_real_linear_companion_bound negates the proposed assertion that every
  coprime integer has a nonzero coprime translate of distance <=C*omega(n).

CRITICAL SCOPE: This is NOT a disproof of erdos_970 and does NOT disprove
LargestPrimeIncrement. The constructed central hole need not lie in an interval
longer than the largest old gap elsewhere in the period. In particular, an
argument for LargestPrimeIncrement cannot simply assert that each survivor has
a companion within O(k). No replacement global argument was proved.

Spec.lean remains unchanged (SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9), with
its sole original sorry at2177. No proof/disproof of the target was submitted.

## Exact-cover quadratic bound verified

New compiled file and olean: DisjointCoverBound.lean (167 lines).
Namespace Erdos970.DisjointCover. Log /tmp/disjoint_cover_lean.log.
Final printed axioms are only propext, Classical.choice, Quot.sound.
No sorry, admit, or native_decide occurs in the file.

For an interval [0,m) covered EXACTLY ONCE by k pairwise-coprime moduli >1,
proved m<=k^2. Main results:
- product_gt_of_exact: distinct selected moduli p,q satisfy m<p*q by CRT;
- other_hits_card_lt: another class has at most p-1 hits, by injection
  modulo p avoiding the selected p residue;
- length_le_of_member: m<=p*(k-1)+1 for each selected modulus p;
- exact_cover_quadratic and prime_exact_cover_quadratic.

If some p<=k+1, the member bound proves the result. Otherwise the ordinary
residue-class count with all moduli >=k+1 proves it.

CRITICAL SCOPE: Arbitrary covers in erdos_970 need not be exact. Assigning
each covered point to one selected class does not make the resulting sets
whole congruence classes and does not preserve the CRT step. No reduction
from arbitrary covers to exact covers has been proved. This result does not
settle the conjecture. Spec.lean is unchanged and retains its sole sorry.

## Lossless exact-cover conversion disproved

New compiled file and olean: ExactCoverBridgeObstruction.lean (68 lines).
It imports only the newly verified DisjointCoverBound.lean; there is no
transitive dependency on Spec.lean or its unresolved theorem.
Log /tmp/exact_cover_bridge_lean.log; final printed axioms all permitted.

Theorems:
- no_exact_cover_nine: no exact prime-class cover of [0,9) with <=4 primes;
- general_cover_nine: {2,3,5,7}, with r(p)=p-2, covers [0,9), corresponding
  to integers2,...,10;
- no_lossless_exactification: it is FALSE that every prime-class interval
  cover has an exact prime-class replacement with no larger prime count.
  This allows changing both primes and residues in the putative replacement.

Proof of impossibility: if2 is selected, the exact member bound gives m<=7.
Otherwise all primes are>=3. In nine positions,3 hits at most3 times,
5 and7 at most2 times each, and every other permitted prime at most once.
Consequently four classes hit at most4+2+1+1=8 positions.

This refutes the proposed bridge, NOT erdos_970. No unrestricted quadratic
bound or superquadratic covering family has been proved. Spec.lean remains
unchanged with its sole sorry at2177; no settlement has been submitted.

## Phase-tail counting route: exact conditional reduction verified

No settlement of erdos_970. Spec.lean unchanged with its sole sorry at2177.
Re-examined LargestPrimeIncrement and its global two-survivor consequence;
no new increment estimate was proved. Old adjacent-gap scans were not repeated.

Three new files (310 lines total) compile; oleans built, final printed axioms
only propext, Classical.choice, Quot.sound. No sorry/admit/native_decide.

1. GapTailCriterion.lean (93 lines), namespace Erdos970.GapAverages.
   - count_zero_of_cover;
   - reciprocal_le_coveredFraction: one zero-survivor phase implies
     coveredFraction >=1/product(p);
   - exponent_le_log_product_of_cover: if coveredFraction<=exp(-b) and a
     cover exists, then b<=sum(log p);
   - survivor_of_exponential_tail and _of_cap: an explicit tail estimate
     with exponent >sum(log p), or >k*log B for primes<=B, excludes every
     exceptional phase. The tail estimate remains a hypothesis.
   Log /tmp/gap_tail_criterion_lean.log.

2. BoundedPrimeCover.lean (82 lines), namespace Erdos970.BoundedPrimeCover.
   - normalize: every prime-class cover of [0,m) with <=k primes has a
     replacement with <=k primes all <=256*(m+k+1)^2.
   It keeps primes<m. Every prime>=m hits at most one position, and can be
   replaced by an explicitly enumerated fresh prime with index m+rank(p).
   The existing elementary nth-prime bound controls these replacements.
   This preserves arbitrary overlaps and is NOT exactification.
   Log /tmp/bounded_prime_cover_lean.log.

3. ExponentialVoidReduction.lean (135 lines), namespace Erdos970.GapAverages.
   - ExponentialVoidBound c is the explicit UNPROVED hypothesis
       forall prime sets P and lengths m,
       coveredFraction(P,m)<=exp(-c*m*density(P)).
   - eventually_quadratic_of_exponential_void: for c>0, this hypothesis
     implies h(k)<=k^2 for all sufficiently large k.
   - quadratic_bound_of_exponential_void: the same hypothesis implies
     the entire original real-valued quadratic proposition.
   - GeometricVoidBound is the UNPROVED stronger hypothesis
       coveredFraction(P,m)<=(1-density(P))^m.
   - exponential_void_of_geometric;
   - quadratic_bound_of_geometric_void.
   Log /tmp/exponential_void_reduction_lean.log.

Proof of the conditional reduction: at m=k^2 the normalized primes are
<=(k+2)^12, so a cover has phase entropy <=12*k*log(k+2). The verified
Mertens lower bound gives density>=d/log(k+2), d>0. An exponential tail
would force c*d*k^2/log(k+2)<=12*k*log(k+2), impossible for large k since
log(k+2)^2/k tends to zero. Monotonicity patches the finitely many small k.
These tail hypotheses are strong additional claims, NOT equivalent restatements
of erdos_970, and have not been derived from the verified variance bound.

A specific exact-integer diagnostic checked binomial factorial-moment domination
for both S and m-S, all moment orders2,...,m, for:
  N210, m<=210; N2310,30030,1155,15015,231,5005, m<=120;
  N105, m<=105.
All these finite checks passed. Script /tmp/gap_factorial_moment_check.py,
log /tmp/gap_factorial_moment_check.log. This is NOT a Lean-verified universal
moment theorem and does NOT establish any tail bound. No worker is active.
Do not infer exponential/geometric decay from these checks, from second
moments, or from endpoint hazard (which was previously refuted).

## Exact one-hit moment update; small-modulus generic induction obstructed

Original erdos_970 remains UNSOLVED. No change to Spec.lean and no submission.
Two new files (238 lines) compile with oleans; final axioms only permitted.
No sorry/admit/native_decide in either file.

1. OneHitMoments.lean (169 lines), namespace Erdos970.OneHitMoments.
   A general finite old sample space Omega carries survivor sets S(w) in [0,m).
   Adding a uniform forbidden residue modulo p>=m removes at most one point.
   - sum_erase_card gives the exact average of any function of the new size;
   - oneHit_choose_sum gives the exact covered-count factorial moments;
   - moment_update averages this over an arbitrary finite old sample space;
   - normalized_moment_update: if A_t is the normalized covered factorial
     moment (divide E[choose(T,t)] by choose(m,t)), then
       A'_(t+1)=(1-(t+1)/p)*A_(t+1)+((t+1)/p)*A_t.
   - avoidance_filter_eq_erase identifies actual modular avoidance with
     one-point deletion under p>=m;
   - preserves_binomial_moment: old moments at t,t+1 bounded by those of
     Binomial(m,q) imply the new (t+1)-moment is bounded by Binomial(m,q'),
     where q'=q+(1-q)/p, for t<m<=p.
   The convex coefficients and the elementary tangent inequality for powers
   give the preservation step. This does NOT cover insertions of small primes.
   Log /tmp/one_hit_moments_lean.log.

2. SmallPrimeMomentObstruction.lean (69 lines), namespace
   Erdos970.SmallPrimeMomentObstruction.
   A stationary periodic old process has survivor residues {0,3,6} modulo10,
   with the shift uniform on Fin10. Consider a length6 interval and add an
   independent forbidden class uniform modulo3 (coprime to10).
   All counts are verified with kernel decision, not native_decide.
   - marginal_certificate: old point survival3/10; new point survival1/5;
     also 3.Coprime10.
   - old_binomial_moment_bounds: all covered factorial moments0,...,6
     are bounded by Binomial(6,7/10).
   - new_low_moment_bounds: new moments0,...,5 are still bounded by
     Binomial(6,4/5), including the second-moment/variance implication.
   - new_void_certificate: exactly8 of30 joint phases have no survivor,
     and the sixth covered factorial-moment sum is8.
   - new_sixth_moment_fails and geometric_void_fails_for_periodic_word:
       8/30 = 4/15 > (4/5)^6.
   Old survivor count distribution: 1 occurs2/10, 2 occurs8/10.
   New survivor count distribution: 0 occurs8/30, 1 occurs8/30, 2 occurs14/30.
   The new variance52/75 is less than the matching binomial variance24/25
   (these two variance fractions were only arithmetically diagnosed, not
   separately stated in Lean; the kernel-checked low moments imply the bound).
   Log /tmp/small_prime_moment_obstruction_lean.log.

CRITICAL SCOPE: The old periodic word is NOT a genuine product of one forbidden
class per prime. This does NOT refute GeometricVoidBound, ExponentialVoidBound,
or erdos_970. It shows that stationarity, coprimality of the old period with
the new modulus, and all old count moments at the target interval length do
not suffice for the proposed small-prime moment-preservation step. Any valid
argument must retain additional prime-product/spatial structure.

No new proof of the required exponential decay or unrestricted quadratic bound
was obtained. No new superquadratic family was constructed. No numerical worker
is active. Spec.lean SHA256 remains
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9;
its sole original sorry is still at2177.

## Exact variance expansion and adjacent-block negative covariance

Original erdos_970 remains UNSOLVED. Spec.lean unchanged; sole sorry at2177.
New file GapVarianceSubadditive.lean (228 lines), olean built. Namespace
Erdos970.GapAverages. Log /tmp/gap_variance_subadditive_lean.log.
Final printed axioms only propext, Classical.choice, Quot.sound.
No sorry/admit/native_decide in the file.

Definitions/results:
- residueDefect D m = r-r^2/D, r=m mod D (natural remainder cast to reals);
- residueDefect_succ: exact one-step recurrence;
- residueDefect_subadd: defect(m+n)<=defect(m)+defect(n).
  If the two remainders sum below D, the difference is -2*r*s/D;
  otherwise it is -2*(D-r)*(D-s)/D.
- sum_pairWeight: sum_Q pairWeight(P,Q)=density(P);
- sum_pairKernel_exact: partial pair-kernel sum is the positive weighted
  sum of floor(m/product(Q));
- phaseMean_count_point_exact;
- countVariance and its exact second-moment/one-step formulas;
- countVariance_expansion:
    Var(S_m)=sum_(Q subset P) pairWeight(P,Q)*residueDefect(product(Q),m).
- countVariance_subadd: Var(S_(m+n))<=Var(S_m)+Var(S_n).
- blockCount, its mean, endpoint-pair mean, second moment, and variance
  are translation invariant in the expected senses;
- adjacent_count_covariance_nonpos: the two centered counts in any two
  adjacent intervals have nonpositive phase-averaged covariance.

CRITICAL SCOPE: These are linear/second-order spatial facts. They do NOT imply
negative association of zero events, factorial moments, or exponential tilts.
In particular they do not repair the previously refuted hard-cover endpoint
hazard and do not prove the needed exponential void bound.

Re-examined the existing unit/common-inverse row rescaling. It preserves each
progression-row marginal distribution but does not make the rows independent.
No stronger nonlinear coupling inequality was proved.

A newly considered, still UNPROVED, candidate is the softened endpoint bound
  E[Y_0 * (1/2)^S_m] >= density * E[(1/2)^S_m],
where S_m counts positions1,...,m and Y_0 is endpoint survival. If uniform,
iteration would give a Laplace/void bound with exponential rate density/2,
and hence settle the target by ExponentialVoidReduction. This candidate is
NOT asserted as a Lean theorem or assumed as an axiom.

Exact-integer diagnostics for this specific candidate:
1. /tmp/soft_endpoint_test.py, log /tmp/soft_endpoint_test.log:
   all m below the period for N210,231,2310,1155;
   m<=200 and reflected complementary lengths N-1-m for
   N30030,15015,5005,51051. All passed.
2. /tmp/soft_endpoint_middle.py, log /tmp/soft_endpoint_middle.log:
   528 selected middle-period lengths (near rational fractions of the period)
   for prime sets
     {2,3,5,7,11,13}, {3,5,7,11,13}, {3,7,11,13,17},
     {2,3,5,7,11,13,17}, {3,5,7,11,13,17},
     {2,3,5,7,11,13,17,19}.
   Largest period9699690. All passed. Comparisons used exact integer
   weighted count histograms, not floating probabilities; printed ratios
   would only have been diagnostics in case of failure. These finite tests
   are NOT kernel-checked certificates and establish no uniform inequality.
   Both processes finished; no numerical worker is active.

No unrestricted quadratic proof, no exponential-tail proof, and no genuine
superquadratic family was found in this round. No proof was submitted.
Spec.lean SHA256 remains
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.

## PGF log-concavity review: asymptotic obstruction, not formalized

No proof/disproof of erdos_970 obtained. No Lean source was changed this round.
Spec.lean remains unchanged, with its sole original sorry at2177.

Considered proving log-concavity of the survivor PGF F(z)=E[z^S] on (0,1].
Since F(1)=1 and F'(1)=mu=m*density, this would imply
  F(z)<=exp(-mu*(1-z)),
and thus an exponential void bound with constant1. The existing failure of
coefficient ultra-log-concavity did not by itself refute this different property.

Specific exact-integer diagnostic:
  /tmp/gap_pgf_logconcavity_test.py
  /tmp/gap_pgf_logconcavity_test.log
Checked F''F<=(F')^2 at z=0 where applicable, and z=1/16,1/4,1/2,3/4,15/16,1,
for lengths up to4 times the maximum gap of several genuine prime sets:
  {2,3,5,7}, {3,7,11}, {2,3,5,7,11}, {3,5,7,11},
  {2,3,5,7,11,13}, {3,7,11,13,17}, {5,7,11,13,17},
  {2,3,5,7,11,13,17}.
For {3,7,11}, also appended101,103,107 successively using the exact one-hit
histogram recurrence, not a full enumeration of the large phase space.
All these finite checks passed. They are diagnostics, not Lean certificates.
The process finished; no worker remains active.

IMPORTANT ANALYTIC OBSTRUCTION (standard asymptotics, NOT Lean-formalized here):
The proposed exact Poisson PGF bound is nevertheless FALSE uniformly.
Take P_y=all primes<=y, N_y=product(P_y), and m=y^2. In the phase representing
integers1,...,y^2, the survivor count is exactly
  s_y=1+pi(y^2)-pi(y).
Using PNT and the sharp Mertens product asymptotic, write
  mu_y=y^2*product_(p<=y)(1-1/p),
  s_y/mu_y -> alpha=e^gamma/2<1,
  log(N_y)=o(mu_y).
One phase gives F_y(z)>=z^(s_y)/N_y. At the fixed z=alpha,
  log(z^(s_y)/N_y)+mu_y*(1-z)
  =mu_y*((1-alpha)+alpha*log(alpha)+o(1))>0 eventually.
Thus F_y(z)>exp(-mu_y*(1-z)), contradicting exact Poisson domination and
hence the proposed uniform log-concavity of log F. Do NOT try to prove that
uniform property based on the finite checks above.

The same observation obstructs uniform binomial factorial-moment domination
of the covered count at ALL orders: such domination would imply
F(z)<=(1-density*(1-z))^m<=exp(-mu*(1-z)). Earlier finite moment tests did
not establish this universal claim.

There is also a mathematical thinning implication (NOT Lean-formalized here):
append finitely many fresh primes all tending to infinity, with their product
of avoidance factors tending to epsilon. Inclusion-exclusion on a fixed old
survivor set shows the new void probability tends to F_old(1-epsilon), while
the density tends to epsilon*density_old. Consequently a uniform
ExponentialVoidBound(c) would imply
  F_old(z)<=exp(-c*mu_old*(1-z))
for all old prime sets and z in(0,1). The rough-number phase above obstructs
c>e^gamma/2. In particular the candidate GeometricVoidBound and
ExponentialVoidBound(1) are mathematically too strong. This is NOT a kernel-
checked disproof theorem in the current development.

CRITICAL SCOPE: This does NOT obstruct every positive c (e.g. c=1/2 is not
excluded), does NOT refute the fixed half-tilted endpoint candidate, and does
NOT refute erdos_970. The conditional reduction from some c>0 remains valid.
No lower-tail estimate sufficient for the quadratic target was proved.

## Signed-kernel review, linear exact covers, and a thinning correction

Original conjecture STILL UNSOLVED. Spec.lean was not changed. Its sole original
sorry remains at2177. No proof or disproof of erdos_970 has been submitted.

The signed-kernel/global-majorant review supplied no uniform estimate at
m=C*k^2. In particular survivor_of_kernelEnergy still requires
  (k+1)*kernelCost^2 < m*kernelEnergy.
The earlier synthetic equal-marginal gain does not establish such an estimate
for distinct primes. The positive parity-box ansatz was reconsidered and found
to be the same previously obstructed ansatz; no new moment-feasibility theorem
or numerical optimization was claimed or run.

Two new files compile and have built oleans. Printed final axioms are only
propext, Classical.choice, Quot.sound:
- ExactCoverLinear.lean (namespace Erdos970.DisjointCover)
- ExactificationUnboundedCost.lean (same namespace)

ExactCoverLinear:
- hits_card_real_le and cover_length_real_le give the ordinary reciprocal
  counting bound m <= m*sum(1/p)+|P|.
- tail_power_bound applies the existing sharp-coefficient elementary Mertens
  estimate at cutoffs x^n,x^4, n=2 or3, for x>=12 and
  log x>=12*(WeightedMertens.boundConstant+1).
- separated_reciprocal_bound: if distinct p,q in P have p*q>x^4, then
    sum_{p in P}1/p <= 11/12 + |P|/x^4.
  Let p be the least selected prime. If p<=x, every other prime exceeds x^3;
  its reciprocal tail is <=log(4/3)+1/12+|P|/x^4, and 1/p<=1/2.
  Otherwise 1/p<=1/12 and all other primes exceed x^2; their tail is
  <=log2+1/12+|P|/x^4. Use log(4/3)<=1/3 and log2<=3/4.
- exact_cover_linear_of_root: when m=x^4 with those thresholds, exactness and
  CRT give the pair separation and hence m<=24*|P|.
- prime_exact_cover_linear: patches finitely many smaller interval lengths to
  yield an absolute C>0 with m<=C*|P| for EVERY exact prime-class cover.
  This is a genuinely LINEAR bound, not merely the earlier exact quadratic one.

ExactificationUnboundedCost:
- no_linear_cover_bound: uses Work.not_linear_bound and the exact cover
  reformulation to rule out a uniform linear bound for GENERAL covers.
- no_constant_factor_exactification: negates the existence of A>0 such that
  every general P-cover admits an exact Q-cover of the same interval with
    |Q| <= A*|P|.
  New primes and residues are freely allowed. A hypothetical conversion,
  combined with prime_exact_cover_linear, would force the impossible uniform
  linear bound for general covers.
This strengthens no_lossless_exactification: even a fixed budget factor is
insufficient. It is NOT a disproof of the quadratic Jacobsthal conjecture.

Logs:
  /tmp/exact_cover_linear_lean.log
  /tmp/exactification_unbounded_cost_lean.log
CheckExactLinear.lean is a scratch API-query file and intentionally contains
unknown-identifier errors; it is not imported by any verified result.

IMPORTANT CORRECTION TO THE PRECEDING PROBABILISTIC STATUS (analytic, NOT Lean-
formalized): the fixed half-tilted exact-density endpoint candidate is also
obstructed once the fresh-prime thinning argument is taken into account.
For an old phase model write
  F_m(z)=E[z^S_m], G_m(z)=E[Y_m*z^S_m], delta=E[Y_m].
Fix z0<1. Append fresh primes tending to infinity with product of avoidance
factors tending to epsilon. On any fixed finite set of positions, their
survival law converges to independent epsilon-thinning: for a set of t
positions its joint survival probability is product(1-t/p)->epsilon^t.
Inclusion-exclusion gives the entire finite joint law. Consequently
  F_new,m(z0) -> F_old,m(1-epsilon+epsilon*z0),
  G_new,m(z0) -> epsilon*G_old,m(1-epsilon+epsilon*z0),
  delta_new -> epsilon*delta_old.
Thus the UNIVERSAL assertion G_m(z0)>=delta*F_m(z0) would imply the same
exact-density endpoint inequality for every z in(z0,1). Iterating
  F_(m+1)(z)=F_m(z)-(1-z)*G_m(z)
would give F_m(z)<=(1-delta*(1-z))^m<=exp(-m*delta*(1-z)).
The rough-number phase from the preceding log section contradicts this at
any fixed z sufficiently close to1: with alpha=e^gamma/2<1,
  1-z+alpha*log z >0
on a nonempty interval immediately to the left of1. This contradicts the
hypothetical fixed-z0 endpoint inequality for EVERY z0<1, including1/2.
No exact-density soft-hazard candidate should therefore be pursued on the
basis of the earlier finite tests. A smaller positive hazard constant, or
ExponentialVoidBound(c) for sufficiently small c>0, is not excluded here.
This correction and its use of PNT/sharp Mertens remain an on-paper argument,
not a kernel-checked disproof theorem in the current files.

No numerical scan or background worker was launched in this round. The
quadratic target remains open in this development; these auxiliary results
must not be substituted for its proof or negation.

## Exact core-tail estimate and a restricted quadratic theorem

Original conjecture STILL UNSOLVED. Spec.lean unchanged, with original sorry
at2177. No proof/disproof of erdos_970 submitted.

Investigated a small-core/large-tail decomposition. The already verified
relative-concentration counterexamples DO impose that the inserted prime is
larger than every old prime; largest-prime ordering alone does not repair the
relative-plus-constant estimate. ActiveQuadraticConcentration additionally
keeps all classes active before/after insertion. These are not complete covers,
so no impossibility result for every aggregate core-tail argument follows.

No quantitative aggregate parent/children relation was obtained. Separate
large-sieve estimates and cardinality-only parent gap bounds retain the earlier
losses. No old numerical scan or optimizer was repeated.

Two NEW compiled files, with built oleans and printed axioms only propext,
Classical.choice, Quot.sound, in namespace Erdos970.CoreTailSieve:

CoreTailSieve.lean:
- siftSet Q T r m: positions in [0,m) avoiding every Q-class and hitting every
  T-class; siftCount is its real-valued cardinality.
- density Q = product_{q in Q}(1-1/q).
- siftCount_split: exact one-core-prime insertion identity.
- siftCount_error: for disjoint prime sets Q,T,
    |siftCount(Q,T)-m*density(Q)/product(T)| <= 2^|Q|.
  Proved inductively from the existing unit CRT intersection remainder; it is
  full exact inclusion-exclusion on Q, not an unproved relative bound.
- siftCount_le_tail: under coverage by Q union R, the surviving Q-population is
  at most the sum of its counts hit by each R-class.
- cover_core_tail_bound: for disjoint prime sets forming a cover,
    m*density(Q)*(1-sum_{p in R}1/p) <= 2^|Q|*(|R|+1).
- cover_length_le: if the tail reciprocal mass is <=1/2, then
    m <= 2*(|Q|+1)*2^|Q|*(|R|+1).
  Uses BrunCriterion.prime_product_bounds for density(Q)>=1/(|Q|+1).

SparseSmallPrimeQuadratic.lean:
- large_prime_tail_half: at most k primes all >2*k have reciprocal mass <=1/2.
- cover_length_quadratic_of_sparse_small: if |P|<=k, k>0, and
    s = |{p in P : p<=2*k}| satisfies (s+1)*2^s<=k,
  every P-cover has length m<=4*k^2.
- small_core_necessary: any cover with m>4*k^2 must satisfy
    k < (s+1)*2^s.
- survivor_of_sparse_small: every interval of length4*k^2+1 has a survivor
  for prime sets with the same explicit small-core restriction, for EVERY
  residue assignment.

These are unconditional estimates in their stated restricted classes, not a
uniform quadratic Jacobsthal theorem. The sparse-core hypothesis is FALSE for
many prime sets and cannot be silently dropped. Dense small-prime cores are
not handled by this argument. No actual superquadratic cover was constructed.

Logs:
  /tmp/core_tail_sieve_lean.log
  /tmp/sparse_small_prime_quadratic_lean.log
No background numerical worker was launched. Spec.lean retains its original
sole import, original conjecture statement, and original sorry.

## Coupled-row review and a verified quadratic double-cover bound

Original conjecture STILL UNSOLVED. Spec.lean was not changed; original sorry
at2177 remains. No proof/disproof submitted.

Reviewed IntervalCoupledRescaling and the largest-prime/two-survivor reductions.
No bound on simultaneous gaps in the coupled rows was obtained. The common
inverse identities retain correlations but do not themselves bound their gaps.
Further attempts involving gap merging, local residue reassignment, and a
maximum-hit anchor gave no uniform quadratic estimate. No numerical scans ran.

NEW compiled file and olean: DoubleCoverQuadratic.lean.
Namespace Erdos970.DoubleCover. Printed axioms only propext, Classical.choice,
Quot.sound. Compilation log /tmp/double_cover_quadratic_lean.log.

The file permits overlaps, but imposes the explicit restriction that no point
is hit by more than TWO selected classes.
- probe p: a finite sieve polynomial with tagged constant, singleton, and
  ordered-pair terms. If H is the number of hits, its value is
    1-(3/2)*H+(1/2)*H^2 = (H-1)*(H-2)/2.
- probe_mean: writing S=sum(1/p) and T=sum(1/p^2), the exact mean is
    1-S+(S^2-T)/2.
- probe_mean_lower: mean>=7/32. Every prime marginal q satisfies q<=1/2,
  so T<=S/2; completing the square gives
    1-(5/4)*S+S^2/2 >=7/32.
  This step uses no asymptotic prime estimate.
- probe_cost: the tagged absolute coefficient cost is
    1+(3/2)*k+(1/2)*k^2.
- total_probe_lower: a general lower bound for the total quadratic probe on
  an interval, valid without coverage or multiplicity assumptions:
    (7/32)*m - [1+(3/2)*k+(1/2)*k^2] <= sum_x (H_x-1)*(H_x-2)/2.
- cover_length_le_sixteen_square: an injective list of k prime classes covering
  an interval with all multiplicities<=2 has length<=16*k^2.
- prime_double_cover_quadratic: the corresponding Finset P theorem,
    m<=16*|P|^2.
The probe vanishes at all covered points under the double-cover restriction.
The unrestricted conjecture does NOT impose that restriction, and the theorem
is not a settlement of erdos_970.

Scratch API files CheckDoubleCover.lean and CheckDoubleCover2.lean may contain
unknown identifier errors; they are not imported by the verified file.

POSSIBLE STRONGER ANALYTIC FACT, NOT LEAN-FORMALIZED:
There is an argument that double covers themselves should have a UNIFORM
LINEAR length bound, so a constant-factor conversion to double covers should
NOT be presumed a viable bridge to the target. Details for future checking:
1. No triple hits implies p*q*r>m for three distinct selected primes, by CRT.
2. If a selected prime p is bounded by a fixed B, all other primes have pair
   products>m/p. Apply ExactCoverLinear.separated_reciprocal_bound at scale m/p
   to get sum_R 1/q<=11/12+p*|R|/m, once m/p is large. CoreTailSieve with Q={p}
   then gives m/24 <= 2*(|R|+1)+p*|R|, a linear bound for bounded p.
3. Otherwise take B=1000 and all primes>B. At most two primes are<=m^(1/3);
   their union contributes at most2*m/B+2 positions. Let T be the remaining
   primes, all>m^(1/3). Its multiplicities are still<=2.
4. Split T at powers m^(.4),m^(.49),m^(.59),m. Write a,b,c,d for the reciprocal
   masses in the first four blocks (the fourth includes the cardinality tail
   beyond m). Sharp-coefficient Mertens yields eventually
     a<=.183, b<=.203, c<=.186, d<=.528+|T|/m.
   All comparisons are strict against the exact log ratios:
     log(6/5), log(49/40), log(59/49), log(100/59).
5. Count the T-union as singles minus pairs, using multiplicity<=2. Keep just
   the negative pairs within the first two blocks and between blocks1 and3.
   Their products are <=m^(.98) and<=m^(.99), so their total unit errors are
   o(m); the reciprocal-square diagonal correction is also o(m). The main
   union bound is
     m*[a+b+c+d-(a+b)^2/2-a*c]+|T|+o(m).
   The bracket is coordinatewise increasing on the above box (ignoring the
   harmless |T|/m part), and at the rational caps equals .991464.
6. Adding the two small primes costs at most.002*m+2. Thus for sufficiently
   large m a cover would imply m <= c*m+2*|P|+2 with fixed c<1. Patch small m
   to obtain a linear bound.
This is an on-paper route, not yet a kernel-checked theorem. In particular do
not cite a formal linear double-cover bound or formal constant-factor
obstruction from this file. The VERIFIED result here is only16*k^2.

No unrestricted quadratic estimate or superquadratic cover family was found.

## Verified fixed-degree moment obstruction for distinct prime marginals

Original conjecture STILL UNSOLVED. Spec.lean unchanged with original sorry.

Three NEW compiled files, built oleans, and printed axioms only propext,
Classical.choice, Quot.sound:
- ProductMomentObstruction.lean: finite dependent product-space construction.
  For each block, distinguished atom a of probability at most1/2, define a
  zero-sum signed measure nu with nu(a)=mu(a), nu(x)=-mu(a)*mu(x)/(1-mu(a))
  off a. Then |nu|<=mu. The weight product(mu)-product(nu) is nonnegative,
  has mass1, and deletes the distinguished product atom. Every product test
  constant in one block retains exactly its independent expectation.
- BlockMomentObstruction.lean: Boolean blocks with independent marginals q.
  If each block's empty probability is<=1/2, the construction deletes the
  all-empty atom and retains all intersection moments of degree less than
  the number of blocks. Includes polynomial and arbitrary-mass formulations.
- PrimeBlockMomentObstruction.lean: Euler's divergent prime series supplies
  any number of disjoint finite prime blocks, beyond any threshold, each
  with avoidance probability<=1/2. All marginal primes are distinct (proved
  primeIndex_injective). For every degree d, size lower bound K, threshold A,
  there is such a prime set of size>=K and with every prime>A admitting an
  empty-free nonnegative synthetic model with exact intersection moments
  through degree d, for EVERY nonnegative real mass X.

Scope: this blocks a uniform method based ONLY on moments through a FIXED
bounded degree and their nonnegative-population constraints. It is not an
actual interval population, does not refute growing-degree sieve methods,
and does not disprove erdos_970. The spatial/AP constraints are not imposed.

Logs /tmp/{product,block,prime_block}_moment_obstruction_lean.log.
No numerical scan or background worker started. No target proof submitted.

## Further unrestricted-route audit (no settlement)

After finishing PrimeBlockMomentObstruction, re-examined spatial/coupled-row,
cardinality-bootstrap, and phase-tail routes. No new unrestricted estimate
was obtained. In particular the synthetic-moment construction cannot stand
in for a spatial realization, and the existing concentration counterexamples
are still NONCOVERS.

On-paper strength audit (not a new Lean theorem): ExponentialVoidBound(c)
for a fixed c>0 would actually give h(k)=O(k*log(k+2)^2), not merely quadratic.
For m of that order (eventually m<=k^2), bounded-prime normalization gives
q<=(k+2)^12 and hence log(product q)<=12*k*log(k+2). The already verified
prime-set density bound is delta>=d/log(k+2) for fixed d>0. Thus choosing
m>12/(c*d)*k*log(k+2)^2 makes c*m*delta>log(product q), excluding any covered
phase via its reciprocal-product minimum mass. This is only a consequence
of the UNPROVED exponential hypothesis; it does not show that hypothesis
false or prove it for any positive c.

No original conjecture proof or negation found. No submit_proof call made.
Spec.lean kept unchanged. No numerical scan or background worker started.

## Sparse-reciprocal exponential void bound verified

Original conjecture STILL UNSOLVED. Spec.lean unchanged, sole sorry retained.

NEW file SparseVoidBound.lean, namespace Erdos970.GapAverages.
Compiled and built olean; printed theorem axioms only propext,
Classical.choice, Quot.sound. Log /tmp/sparse_void_bound_lean.log.

Definitions and verified results:
- residueHits(m,p,a): number of integers in [0,m) in residue a mod p.
- residueHits_eq: exact floor(m/p)+indicator(a<m mod p).
- sum_residueHits: sum over all p phases equals m.
- residueHits_pow_mean: exact exponential-moment interpolation.
- residueHits_pow_mean_le: for real b>=1,
    E_a b^residueHits <= exp((b-1)*m/p).
  Proof: the hit count is an integer constant plus one Bernoulli variable;
  b<=exp(b-1) and 1+x<=exp(x).
- totalHits: sum of these counts, retaining multiplicities at overlaps.
- totalHits_pow_mean_le: independence of the selected residue phases gives
    E b^totalHits <= exp((b-1)*m*sum_P(1/p)).
- cover_of_count_zero and length_le_totalHits_of_cover.
- coveredFraction_le_total_hit_exponential: for any b>=1,
    coveredFraction(P,m) <= exp(m*((b-1)*sum_P(1/p)-log b)).
- coveredFraction_le_exp_of_reciprocal_half: if sum_P(1/p)<=1/2,
    coveredFraction(P,m)<=exp(-m/8).
- coveredFraction_le_exp_of_reciprocal_lt_one: if 0<alpha<1 and
  sum_P(1/p)<=alpha, choose b=1/alpha to obtain
    coveredFraction(P,m)<=exp(-(alpha-1-log alpha)*m).
- sparse_exponential_rate_pos: alpha-1-log alpha>0 for 0<alpha<1.

Scope and limitations:
This proves exponential decay only on a RESTRICTED reciprocal-sparse class.
It does not prove ExponentialVoidBound(c) for any c>0 on all prime sets.
Indeed for worst-case existence in this restricted class, ordinary counting
already gives the stronger linear restriction m<=|P|/(1-alpha) on a cover.
The new result is probabilistic information, not a better uniform Jacobsthal
bound. After conditioning on the survivors of a dense core, a residue's hit
count is no longer floor/ceiling balanced, so the one-coordinate Poisson
comparison cannot simply be reused. Conditional bounds using only a maximum
row count lose too much; no unrestricted bridge was proved.

Also re-examined the weaker fixed-positive-constant soft endpoint hazard.
No proof or disproof of that universal candidate was found. Do not infer it
from second moments, unweighted independence of the phases, or this sparse
special case. No new numerical scan or background worker was launched.
CheckSparseVoid.lean is a scratch API file with intentional unknown-name
errors; it is not imported by the verified file.

No proof or negation of erdos_970 submitted. Spec statement/import unchanged.

## Reciprocal-budget covers: quadratic and subquadratic estimates verified

Original conjecture STILL UNSOLVED. Spec.lean unchanged, sole original sorry
at2177. No proof/disproof submitted. No numerical scans or workers launched.

Two NEW compiled files, built oleans, printed axioms only propext,
Classical.choice, Quot.sound. Namespace Erdos970.ReciprocalBudget.

ReciprocalBudgetQuadratic.lean:
- probe: tagged polynomial with value (H-1)(H-k), where H is multiplicity.
  It is nonpositive on EVERY covered point, since 1<=H<=k. No multiplicity
  restriction is assumed.
- exact mean k*(1-s)+s^2-t, where s=sum1/p and t=sum1/p^2.
- tagged coefficient cost 2*k^2+2*k.
- cover_moment_budget: for every prime-class cover (even with s>1),
    m*[k*(1-s)+s^2-t] <= 2*k^2+2*k.
- prime_reciprocal_bounds: s<=k/2, t<=s/2.
- reciprocal_budget_mean_lower: if s<=1 and k>=1, this mean>=1/2.
- cover_length_le_eight_square and Finset specialization
  prime_cover_quadratic_of_reciprocal_budget: s<=1 implies m<=8*k^2.

ReciprocalBudgetSubquadratic.lean improves this RESTRICTED result:
- cover_length_le_four_prime_card: if s<=1, then for EVERY selected p,
    m<=4*p*k.
  Apply the already verified exact core-tail estimate with core {p} and tail
  P.erase p. The tail mass is at most1-1/p. The main term is at least
  m*(1-1/p)/p >=m/(2*p), and the remainder is2*k.
- reciprocal_small_of_large_min: if p is the least selected prime,
  sqrt(p)>=12, log(sqrt(p))>=12*(WeightedMertens.boundConstant+1), and
  p^2>=16*k, then s<=7/8. Uses ExactCoverLinear.tail_power_bound with x=sqrt(p),
  n=2, plus the least prime's reciprocal:
    s<=1/p+log2+1/12+k/p^2<=7/8.
- prime_cover_square_le_card_cube:
    exists C>0, for every prime set P with sum1/p<=1 and every covered
    interval of length m, m^2<=C*|P|^3.
  For sufficiently large least prime p, split at p^2<=16*k. In that case
  m<=4*p*k implies m^2<=256*k^3. Otherwise s<=7/8 and ordinary counting gives
  m<=8*k. Bounded p is handled by m<=4*p*k and one absolute constant.
  Thus this class has a uniform O(k^(3/2)) length bound, with no overlap cap.

CRITICAL SCOPE: The reciprocal budget sum1/p<=1 is not a hypothesis of
Erdos970 and is false for many prime sets (including long initial prime sets).
No constant-factor conversion of arbitrary covers to reciprocal-budget covers
has been constructed. These restricted estimates neither prove nor disprove
quadratic Jacobsthal growth. Submultiplicativity of fixed-set gap bounds, or a
smallest-prime gap-insertion estimate, was NOT established and must not be
silently used to extend this result.

Logs:
 /tmp/reciprocal_budget_quadratic_lean.log
 /tmp/reciprocal_budget_subquadratic_lean.log
Scratch CheckBudgetSubquadratic.lean has an unknown-name API check and is not
imported by either verified file.

## Gap-controlled polynomial discrepancy shortcut ruled out

Original conjecture STILL UNSOLVED. Spec.lean unchanged; no target proof or
negation submitted. No numerical scan or background worker started.

Reviewed the attempted bridge from reciprocal-budget covers to general covers:
remove a small-prime core so the tail reciprocal mass is below one, then try to
replace the exact core's exponential inclusion-exclusion error by a polynomial
in a known gap bound. No valid aggregate/positional bridge was obtained.

NEW compiled file/olean GapControlledDiscrepancyObstruction.lean.
Imports ParityDiscrepancyUnbounded and FifthPowerBound. Namespace
Erdos970.ParityDiscrepancy. Printed axioms only propext, Classical.choice,
Quot.sound. Log /tmp/gap_controlled_discrepancy_obstruction_lean.log.

Verified:
- exists_exponential_dominates_polynomial: for arbitrary A,d,K there is k>=K,
  k>0, with [A*(k+1)^d]^2 < (4/3)^k. Uses Mathlib's polynomial/exponential limit.
- unbounded_polynomial_parity_discrepancy: actual odd-prime interval parity
  discrepancies exceed A*(|P|+1)^d, with arbitrary lower bounds on |P|, length,
  and C*|P|^2. Uses the existing exact complete-period parity energy.
- jacobsthal_add_one_le_fifth: the verified unconditional fifth-power estimate
  bounds h(k)+1 by (fifthPowerConstant+1)*(k+1)^5.
- unbounded_jacobsthal_polynomial_parity: actual parity discrepancies exceed
  A*(jacobsthalFunction(|P|)+1)^d under the same lower-size/length constraints.
- no_uniform_gap_polynomial_parity_error: explicitly negates the assertion
  that any real constant times that fixed power bounds parity discrepancy
  on every interval beyond a quadratic lower threshold.

SCOPE: These are counterexamples to a UNIFORM-IN-LENGTH PARITY DISCREPANCY
estimate, not to h(k)=O(k^2). The intervals can be huge (odd multiples of the
prime-product period), not necessarily of exact length C*k^2. This does not
exclude specialized errors at a prescribed scale, aggregate core-tail estimates,
or methods retaining the coupled residue-row geometry. No negation of the
original conjecture is proved by this file. The existence of a polynomial gap
bound alone must not be promoted to a polynomial full-discrepancy bound.

Scratch CheckGapControl.lean has an intentional unknown-argument API test and
is not imported by the verified file. No submit_proof call made.

## Further unrestricted-cover review (no settlement)

Original conjecture STILL UNSOLVED. No source change to Spec.lean and no
proof/disproof submitted in this continuation.

Re-read the actual target, fifth-power bound, reciprocal-budget subquadratic
bound, double-cover quadratic bound, and the exact-cover linear argument.
No implication removing either the reciprocal-budget restriction or the
multiplicity restriction was established. In particular the on-paper linear
double-cover argument is still not a verified theorem and would not itself
settle the unrestricted conjecture.

The proposed aggregate-concentration obstruction from the preceding working
summary remains an unformalized diagnostic construction, not a cover family:
choose a fixed core of primes >T with tiny density; then take k tail primes
comparable to m/(T+1), at m=C*(|Q|+k)^2, all forbidden residues zero. Their
first T positive multiples are distinct core survivors, giving >=T*k removals.
The relative expectation can be made O(k) by the tiny fixed core density.
Prime supply in a broad fixed annulus would follow from PrimeCountingLower
and Chebyshev.eventually_primeCounting_le. This would only refute one proposed
relative-plus-linear aggregate estimate on general configurations. Point 1
survives, so it would NOT disprove erdos_970 or a cover-specific estimate.
No Lean theorem asserting this construction was added.

No new mathematical bridge to the quadratic target was found. No numerical
scan or background worker was started. The original sorry remains.

## Unconditional cubic Jacobsthal bound verified

Original conjecture STILL UNSOLVED. Spec.lean unchanged, sole original sorry
at2177, SHA256 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No proof/disproof of erdos_970 submitted. No numerical scan or background worker
was started. This continuation produced a genuine improvement of the verified
UNRESTRICTED bound from O(k^5) to O(k^3), not a quadratic settlement.

Seven NEW files, 1370 lines total, all compiled and oleans built. The final
isJacobsthalBound_cubic, jacobsthalFunction_le_cubic, and
exists_cubic_power_bound print only propext, Classical.choice, Quot.sound.
No sorry/admit/native_decide/axiom declarations in these seven files.
Final recheck log: /tmp/cubic_power_bound_lean.log.

1. SelbergNormalizerUpper.lean (459 lines), FiniteSelberg namespace.
   - coprimeHarmonic(N,R): sum_{1<=n<=R, gcd(N,n)=1}1/n.
   - coprimeHarmonic_le: <=N+(phi(N)/N)*(1+log R).
     Split below N; inject the rest into quotient/remainder pairs and use
     the harmonic upper bound. This is a finite argument.
   - primeWeight(Q)=product 1/(p-1).
   - primeNormalizer(P,R)=sum_{Q subset P, product Q<=R}primeWeight(Q).
   - primeWeight_expansion: w(Q)=(1/product Q)*sum_{T subset Q}w(T).
   - superset_reciprocal_sum_le and rough_primeNormalizer_le: if all P primes
     are coprime to N, normalizer <=coprimeHarmonic(N,R)*
       product_{p in P}(1+1/(p(p-1))).
   - primeNormalizer_union_le: adding a core costs at most product(1+1/(p-1)).
   - correction_tail_le: for P>B>=1, sum1/(p(p-1))<=1/B, by telescoping.
   - correction_product_le: corresponding product <=exp(1/B).
   - totient_core_factor: product_{p|N}(1+1/(p-1))*phi(N)/N=1.
   - normalizerOffset(B)>0 is an explicit fixed constant using B!.
   - primeNormalizer_log_upper, for EVERY finite prime set P:
       normalizer(P,R)<=exp(1/B)*log R+normalizerOffset(B), B>0.
     Add core primeFactors(B!), apply the rough estimate to P minus this
     core, and use exact totient cancellation of the leading coefficient.
   - primeNormalizer_log_upper_concrete: coefficient65/64, offset(65).
     exp(1/65)<=65/64 follows from log(x)>=1-1/x.

2. FiniteLayerCake.lean (234 lines).
   General finite weighted strict cumulative mass F(t)=sum_{a_i<t}w_i.
   - weighted_linear_cut: exact integral identity for the clipped square.
   - soft_square_lower: F(t)>=t-E on[0,L] gives sum w(L-a)_+^2
       >=L^3/3-E*L^2, assuming locations>=0.
   - capped_square_upper: F(t)<=A*t+C and0<=v<=L gives
       sum w*min(v,(L-a)_+)^2 <=A*(L*v^2-(2/3)*v^3)+C*v^2.
   - weighted_first_cut and cumulative_moments: for locations in[0,L],
     |sum w-L|<=E and |F(t)-t|<=E imply
       |sum w*a-L^2/2|<=2*E*L,
       |sum w*a^2-L^3/3|<=4*E*L^2.
   No probabilistic independence hypotheses are used.

3. SelbergNormalizerProfile.lean (128 lines).
   - indexed_normalizer_log_upper transfers the finite-prime-set estimate.
   - primeLogLocation(p,Q)=sum_{i in Q}log p_i.
   - cumulative_prime_upper: orthogonal weights w(Q)=product1/(p-1),
     with these locations, have F(t)<=(65/64)*t+normalizerOffset65 for t>=0.
   - cumulative_prime_lower: if all primes<=R are present and0<=t<=log R,
     then F(t)>=t-1. Compare to cutoff floor(exp(t-1)) and the existing
     harmonic lower bound. Strict cutoffs avoid endpoint ambiguities.
   - prime_soft_square_lower: for a complete small-prime core,
       sum_Q w(Q)*softProfile(logp,logR,Q)^2 >=log(R)^3/3-log(R)^2.

4. PrimeSharpLogMoments.lean (125 lines), WeightedMertens namespace.
   - abs_realPrimeSum_sub_log_one extends the weighted Mertens estimate
     to real cutoffs >=1.
   - sharpMomentError=boundConstant+2>0.
   - initialPrimeCumulative_error: for t in[0,logR], the weights log(p)/p
     at locations log(p), p<=R, have cumulative mass within this error of t.
   - prime_second_third_log_moments, with E=sharpMomentError:
       |sum_{p<=R}log(p)^2/p-log(R)^2/2|<=2*E*logR,
       |sum_{p<=R}log(p)^3/p-log(R)^3/3|<=4*E*log(R)^2.
     Derived from the finite cumulative_moments lemma; no new analytic
     partial-summation or PNT theorem was needed.

5. SelbergCubicEnergy.lean (223 lines).
   - Exact soft-profile coordinate difference is min(logp,softProfile(Q)).
   - prime_soft_dirichlet_coordinate uses the capped-square bound with
     v=min(logp,logR); retaining the negative cubic correction is crucial.
   - cappedLogMoment_split: capped moments equal the full initial-prime
     moments plus log(R)^n times the reciprocal tail beyond R, provided
     all primes<=R occur in the injective list.
   - prime_soft_energy_cubic_lower: if logR>=1 and reciprocal tail<=1/64,
       kernelEnergy >=log(R)^3/24-cubicEnergyError*log(R)^2,
     with an explicit positive absolute error constant.
   - prime_soft_energy_cubic: if also logR>=48*cubicEnergyError,
       kernelEnergy >=log(R)^3/48.
   Leading Dirichlet contribution before rounding is
       (65/64)*[(5/18)+(tail/3)]*log(R)^3,
     versus square mass (1/3)*log(R)^3. This is why the energy is positive.

6. SelbergCubicPrimeBound.lean (149 lines).
   - cubicCutoffScale D=64+ceil(exp(48*cubicEnergyError+1)), a fixed integer.
   - cubicBoundConstant=48*exp4*D^2*(D+1)>0.
   - prime_survivor_cubic: EVERY P with |P|<=k has a survivor once
       m>cubicBoundConstant*(k+1)^3.
     Pad P by all primes<=R=D*(k+1); this increases total prime count to
     <=k+R and does not introduce any new tail prime. The old tail is<=k/R
     <=1/64. The new energy bound and existing coefficient cost
       kernelCost<=log(R)*exp2*R
     imply cost^2<=48*exp4*R^2*kernelEnergy. The universal interval remainder
     (number_of_primes+1)*cost^2 then gives the cubic threshold. A survivor
     avoiding the padded prime set also avoids the original P.

7. CubicPowerBound.lean (52 lines).
   - isJacobsthalBound_cubic k:
       IsJacobsthalBound k (cubicPowerConstant*(k+1)^3).
   - jacobsthalFunction_le_cubic k: same bound for the infimum definition.
   - exists_cubic_power_bound:
       exists C>0, forall k>0, (jacobsthalFunction k:Real)<=C*k^3.
   This is UNCONDITIONAL and applies to arbitrary overlaps and reciprocal mass.
   It does not use erdos_970 or its sorry, as the axiom audit confirms.

Remaining loss / possible next work:
The interval error still contains (prime count+1)*kernelCost^2. At R~k this
is O(k^3), not O(k^2). No argument removing that factor was found.
An on-paper further improvement could choose R~k^alpha, using Mertens to bound
reciprocal tail by log(1/alpha)+o(1). For the current linear soft profile, the
leading energy condition is approximately
  1/3 > A*(5/18+log(1/alpha)/3), A=65/64.
For example alpha=7/8 would give an exponent1+2alpha=11/4<3, with more work
on cutoffs/cardinality transfer. THIS IMPROVED EXPONENT IS NOT YET FORMALIZED.
Taking A closer to1 gives the heuristic limiting threshold alpha>exp(-1/6),
not alpha=1/2. This is only an audit of this particular estimate/profile,
not a theorem excluding other kernels or a settlement of quadratic growth.

Scratch CheckNormalizerUpper.lean, CheckLayerCake.lean and CheckSharpMoment.lean
contain intentional failed API queries; no verified file imports them.

## Unconditional exponent 11/4 verified

Original conjecture STILL UNSOLVED. Spec.lean unchanged, sole original sorry
at2177; SHA256 unchanged. No erdos_970 proof/disproof submitted. No numerical
scan or background worker started. The previous cubic estimate has now been
strictly improved to h(k)=O(k^(11/4)) for the UNRESTRICTED Jacobsthal function.

Four NEW files (409 lines total), compiled and oleans built; no holes or new
axioms. Final audit log /tmp/seven_eighth_power_bound_lean.log prints only
propext, Classical.choice, Quot.sound for all three final theorems.

1. SelbergSeventhEnergy.lean (87 lines), FiniteSelberg namespace.
   Reuses the full sharp-moment calculation with reciprocal tail <=1/7.
   - prime_soft_energy_seventh_lower:
       energy >=log(R)^3/512-cubicEnergyError*log(R)^2.
   - prime_soft_energy_seventh: if logR>=1 and
     logR>=1024*cubicEnergyError, then energy>=log(R)^3/1024.
   The leading margin is positive:
     1/3-(65/64)*(5/18+1/21)=23/8064>1/512.

2. SevenEighthTail.lean (74 lines), WeightedMertens namespace.
   - log_eight_sevenths_le: log(8/7)<=7/50, using
     8/7<=(107/100)^2 and log x<=x-1; no numerical approximation oracle.
   - tail_seven_eighths: for |P|<=t^8, t>0, D>=1024 and
       logD>=2048*(boundConstant+1),
       sum_{p in P,p>D*t^7}1/p<=1/7.
     Apply prime_set_tail with a=D*t^7 and b=D*t^8. The log-log increment
     is <=log(8/7), since logD>=0. Each of the analytic error and the
     cardinality contribution is <=1/1024, and7/50+2/1024<1/7.

3. SevenEighthPrimeBound.lean (150 lines), FiniteSelberg namespace.
   - sevenEighthCutoffScale is the fixed integer
       1024+ceil(exp(1024*cubicEnergyError+
                     2048*(WeightedMertens.boundConstant+1)+1)).
   - sevenEighthBoundConstant=1024*exp4*D^2*(D+2)>0.
   - prime_survivor_seven_eighths:
       if |P|<=t^8, t>0 and m>sevenEighthBoundConstant*t^22,
       then an integer in[0,m) avoids every selected P-class.
     Pad by primes<=R=D*t^7. The tail lemma gives mass<=1/7, energy is
     >=log(R)^3/1024, and the unchanged coefficient-cost bound gives
       cost^2<=1024*exp4*R^2*energy.
     Total padded prime count plus one <=(D+2)*t^8, giving t^(8+14)=t^22.

4. SevenEighthPowerBound.lean (98 lines), Erdos970 namespace.
   - exists_eighth_power_envelope: for k>0 there is t>0 with
       k<=t^8<=256*k. Use the least natural t with k<=t^8; minimality
       gives(t-1)^8<k, and t<=2(t-1) unless t=1.
   - isJacobsthalBound_seven_eighths(k,t): if0<t and k<=t^8,
       IsJacobsthalBound k (sevenEighthPowerConstant*t^22).
   - jacobsthalFunction_fourth_le_eleventh(k,hk):
       jacobsthalFunction(k)^4<=elevenFourthConstant*k^11,
       where elevenFourthConstant=sevenEighthPowerConstant^4*256^11.
   - exists_eleven_fourths_bound:
       exists C>0, forall k>0,
       (jacobsthalFunction k:Real)<=C*(k:Real)^((11:Real)/4).
     This last theorem uses a genuine real exponent, not natural division.

CRITICAL SCOPE: This is exponent2.75, NOT exponent2. The interval remainder
still contains a factor proportional to prime count. At a cutoff R~k^alpha,
this method pays k*R^2, explaining exponent1+2alpha. No removal of that
factor, or different uniform quadratic estimate, was obtained. The prior
on-paper linear-profile threshold audit remains a limitation of that estimate,
not a theorem excluding every alternative kernel or method.

CheckSevenEighth.lean is a scratch API file containing intentionally failed
queries. It is not imported by any verified file. The original target was
neither changed nor replaced by one of these weaker theorems.

## First-hit/global-weight review after exponent 11/4 (no settlement)

Original conjecture STILL UNSOLVED. No change to Spec.lean or to the verified
11/4 theorem. No new Lean theorem in this continuation and no submission.

Reviewed FirstHitSigned, BooleanKernelUpperWeights, BooleanCoupledDuality,
SelbergSharpUpper, and the existing synthetic block moment constructions.
The new normalizer upper/lower estimates do not by themselves bound the SUM
of first-hit objectives below the interval length. No uniform family of prior-
supported kernels satisfying the quadratic criterion was obtained. In
particular the existing numerical/finite method comparisons do not imply
an asymptotic advantage for distinct-prime marginals.

Also considered the exact product correction in ProductMomentObstruction:
its all-block moment error factors into signed block moments. The existing
verified theorem only asserts exact preservation for tests omitting a block
(or degree below block count). No new all-degree unit-error obstruction,
spatial cover construction, or uniform quadratic certificate was proved.
Do not conflate this synthetic construction with a realizable interval.

The first-hit class and the larger global coverage-polynomial class remain
mathematically distinct; the existing finite separation is not evidence that
either can or cannot meet the target for all prime sets. No claim of a general
method-impossibility theorem is made by this review. No new numerical scan or
background worker was started.

## Alternative-profile investigation (no new bound or settlement)

Original conjecture STILL UNSOLVED. Spec.lean unchanged with its original sorry.
The strongest verified unrestricted result remains exists_eleven_fourths_bound.
No new Lean theorem or proof submission in this continuation.

Investigated a capped and a two-slope soft profile before attempting a costly
formalization. These calculations are ON PAPER / SYMBOLIC DIAGNOSTICS, not
new kernel-checked energy theorems. For the continuous leading model, writing
u for residual logarithmic distance in[0,1]:
- f(u)=u has square mass1/3 and Dirichlet term5/18, ratio5/6.
- f(u)=min(u,1/2) has mass1/6 and Dirichlet term5/36, also ratio5/6.
  The cap alone thus gives no leading-ratio improvement.
- The cross terms of these two profiles are11/48 and55/288-log2/48.
- f(u)=u+min(u,1/2) has mass23/24 and Dirichlet term
    115/144-log2/24,
  ratio5/6-log2/23. This is a modest improvement for this continuous model,
  NOT a proved improved interval/Jacobsthal exponent.

A small targeted variational diagnostic was run, not a blind cover search:
/tmp/soft_profile_variational_audit.py. For the basis g_a(x)=(a-x)_+ at rational
knots a=j/n, n=1,2,4,8,16, it forms the analytically derived Gram matrices and
uses floating generalized eigenvalues. Results were approximately
.83333,.80227,.76461,.74030,.72666. These are NOT exact certificates or rigorous
bounds on the infinite-dimensional optimum. No claim that every profile or
kernel fails follows from them. In the k*R^2 remainder framework, a cutoff
R~sqrt(k) would require a continuous ratio below1-log2~.30685, much smaller
than these specific tested profile ratios. This is a diagnostic comparison,
not a method-impossibility theorem or a quadratic proof/disproof.

The finite-grid bilinear forms used (a<=b, d=b-a) were
  N(a,b)=a^2*b/2-a^3/6,
  D(a,b)=a^3/6+d*a^2/2-[F(b)-F(d)],
  F(y)=(y^3/3-d*y^2/2)*log(y)-y^3/9+d*y^2/4,
with the limiting value at zero. They follow by integrating
min(v,a-x)*min(v,b-x) over x and dv/v. They have NOT been added to Lean.

A square-root profile was also considered analytically. Transferring it would
require new uniform weighted variation/error bounds and does not presently
supply the missing quadratic step. No unproved transfer or floating diagnostic
was inserted into Spec.lean. No background worker remains active.

## Exact all-degree errors for the block model verified

Original erdos_970 STILL UNSOLVED. Spec.lean is unchanged, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
The strongest verified unconditional upper bound remains exponent11/4.
No quadratic proof, genuine superquadratic cover, or proof submission was obtained.

Reviewed the all-intersection/global-polynomial route and the existing LP and
phase-tail investigations. Did NOT rerun the already recorded first-prime LP
comparisons or treat their finite agreement as an asymptotic theorem. The
quadratic logarithmic profile suggested before this continuation remains an
unformalized proposal; no exponent21/8 claim is made.

Two new files compile with built oleans. Final printed axioms are only
propext, Classical.choice, Quot.sound; no sorry/admit/native_decide is present:

1. BlockMomentError.lean (225 lines), namespace BlockMomentObstruction.
   Define V_j=product_i(1-q_ji), rho_j=emptyOdds(q,j)=V_j/(1-V_j).
   - signed_hit_moment: the signed single-block moment is0 for the empty
     support and -rho_j*product_(i in T_j)q_ji otherwise.
   - all_moment_error_exact: model moment minus its independent product mean
     is minus the product of these signed block moments, with NO degree cap.
   - all_moment_error_le: if0<=q_ji<=1, V_j<1, and0<=b_j with q_ji<=b_j,
     EVERY absolute intersection error is<=product_j(rho_j*b_j).
   - scaled_all_moment_model: if every V_j<=1/2 and
       X*product_j(rho_j*b_j)<=1,
     the scaled model is nonnegative, has massX, has no empty atom, and ALL
     intersection moments have absolute errors<=1.
   - singleton_moment_error: selecting one coordinate in every block attains
     the corresponding product error exactly.
   - scaled_all_moments_iff: when i0_j maximizes q_ji in each block, the budget
       X*product_j(rho_j*q_j(i0_j))<=1
     is NECESSARY AND SUFFICIENT for all intersection errors of this particular
     scaled model to be<=1.
   - global_lower_polynomial_cost: under the displayed budget, any arbitrary
     signed polynomial nonpositive off the empty pattern satisfies
       X*independent_mean<=sum(abs(coefficients)).
     This is a conditional weak-duality statement, not a uniform obstruction.

2. PrimeBlockMomentError.lean (83 lines), namespace PrimeBlockMomentError.
   For finite nonempty prime blocks P_j, V_j=product_(p in P_j)(1-1/p), and
   a_j=min(P_j):
   - all_moments_unit_iff specializes the exact budget to
       X*product_j((V_j/(1-V_j))/a_j)<=1.
     The worst intersection selects the least prime in every block.
   - certificate verifies nonnegativity, total mass, empty-atom deletion, and
     all unit moment errors under V_j<=1/2 and this explicit budget.
   Disjoint prime blocks can be used, but disjointness is not needed for the
   moment calculation. These populations are NOT asserted to be realizable
   as interval populations.

CRITICAL LIMITATION: No family satisfying this budget at arbitrary massC*k^2
was constructed. The exact threshold applies only to this rank-one block
model, not to all possible synthetic populations, all sieve certificates, or
actual residue covers. Consequently these results neither prove nor disprove
Erdos970 and do not establish a universal method barrier.

Logs: /tmp/block_moment_error_final.log,
      /tmp/prime_block_moment_error_lean.log.
No numerical optimizer or background worker was started in this continuation.

## Unconditional exponent21/8 verified

Original erdos_970 STILL UNSOLVED. Spec.lean remains unchanged (original theorem
at2175 and sole sorry at2177), SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No proof submission was made. The NEW strongest verified unrestricted bound is
  jacobsthalFunction(k)=O(k^(21/8)),
with a genuine real exponent21/8=2.625. This does NOT imply exponent2.

The beginning of this continuation reviewed the covering, phase-tail, and
half-tilted endpoint routes without finding a quadratic closure. The apparent
thinning obstruction to the fixed half-tilt was already explicitly recorded
in the earlier 'Signed-kernel review ... thinning correction' section; it is
NOT a newly proved result. The network lookup failed (DNS unavailable).
No numerical counterexample search or optimizer was launched.

The previously proposed quadratic logarithmic profile was then completed.
All11 new files below compile with built oleans, and all final printed axioms
are only propext, Classical.choice, Quot.sound. Total1206 Lean source lines.
No sorry/admit/native_decide occurs in these new files.

1. CumulativeVariation.lean (164 lines), FiniteSelberg namespace.
   - integral_general_cut, cumulative_mul_integrable, weighted_profile_integral:
     finite weighted layer cake for arbitrary interval-integrable integrands,
     including atoms outside the profile support.
   - cumulative_integral_error, weighted_profile_error:
       |sum_i w_i f(a_i) - integral_0^L t*g(t)dt|
         <=E*integral_0^L |g(t)|dt,
     when f(x)=integral_x^L g for0<=x<=L and0 beyondL, a_i>=0, and the strict
     cumulative mass A(t) is withinE of t. This retains total variation rather
     than bounding polynomial coefficients separately.
   - cumulative_power_moment for EVERY natural n:
       |sum_i w_i*a_i^(n+1)-L^(n+2)/(n+2)|<=2E*L^(n+1),
     assuming0<=a_i<=L, cumulative error<=E, and total-mass error<=E.

2. PrimeAllLogMoments.lean (45 lines), WeightedMertens namespace.
   - prime_log_moment(R,hR,n), using e=sharpMomentError:
       |sum_(p<=R)log(p)^(n+2)/p - log(R)^(n+2)/(n+2)|
         <=2e*log(R)^(n+1).
   - prime_fifth_log_moment specializes n=3. No PNT is used.

3. QuadraticLayerCake.lean (106 lines), FiniteSelberg namespace.
   F_L(a)=quadraticProfile L a=max(L^2-a^2,0).
   - quadratic_square_error: square mass differs from(8/15)L^5 by<=E L^4.
   - quadratic_square_lower: cumulative lower bound A(t)>=t-E alone gives
       sum w_i F_L(a_i)^2 >=(8/15)L^5-E L^4.
   - exact integral and nonnegative-slope identities used for these estimates.

4. QuadraticDifferenceLayerCake.lean (171 lines).
   - splitSlope and integral_splitSlope handle a piecewise-polynomial derivative
     with its possible jump; endpoint conventions are treated through strict cuts.
   - quadratic_difference_primitive identifies the squared shifted difference.
   - integral_quadraticDifferenceSlope_mul gives its continuous main term
       K_L(v)=(4/3)L^3 v^2-(2/3)L^2 v^3-(2/15)v^5, 0<=v<=L.
   - integral_abs_quadraticDifferenceSlope gives exact total variation
       2*(2Lv-v^2)^2-v^4 <=8L^2v^2.
   - quadratic_difference_error gives error<=8E L^2v^2 in the finite weighted
     squared-difference sum. Crucially this retains v^2 for small shifts.

5. CumulativePrimeSharp.lean (86 lines).
   - exp_one_div_succ_le(B,hB): exp(1/(B+1))<=1+1/B.
   - indexed_normalizer_log_upper_sharp, cumulative_prime_upper_sharp:
       A(t)<=(1+1/B)t+normalizerOffset(B+1).
   - cumulative_prime_uniform_error for a prime list containing all primes<=R:
       |A(t)-t|<=log(R)/B+normalizerOffset(B+1)+1, 0<=t<=logR.
     B can be arbitrarily large but must be positive.

6. SelbergQuadraticProfile.lean (127 lines).
   - primeQuadraticProfile p L Q=F_L(sum_(i in Q)log p_i).
   - prime_quadratic_square_lower gives(8/15)L^5-L^4.
   - prime_quadratic_dirichlet_coordinate and prime_quadratic_dirichlet_le:
       Dir <=(4/3)L^3 U2-(2/3)L^2 U3-(2/15)U5+8E L^2 U2,
     with capped logarithmic momentsU2,U3,U5 and
       E=L/B+normalizerOffset(B+1)+1.
     The restriction i notin Q is dropped only using nonnegativity.

7. SelbergQuadraticEnergy.lean (129 lines).
   C=quadraticEnergyOffset=normalizerOffset65537+1,
   D=quadraticEnergyError=1+21e+8C+16Ce>0.
   - prime_quadratic_energy_lower, forL=logR>=1 and reciprocal tail<=5/24:
       energy>=L^5/256-D L^4.
   - prime_quadratic_energy, additionallyL>=512D:
       energy>=L^5/512.
   The continuous core Dirichlet main is94L^5/225. Adding the tail5/24 to
   the square-mass ratio leaves an unperturbed marginL^5/225. The accuracy
   parameter B65536 and lower-order estimates are explicitly accounted for.

8. SelbergQuadraticCost.lean (56 lines).
   - prime_quadratic_support: profile vanishes off divisorSupport p R.
   - prime_quadratic_cost_le: kernelCost<=L^2*exp2*R.
   This uses F_L<=L^2 and the existing divisor-cost sum bound.

9. ThirteenSixteenthTail.lean (74 lines), WeightedMertens namespace.
   - log_sixteen_thirteenths_le: log(16/13)<=26/125, certified using
       16/13<=(4013/4000)^64 and log x<=x-1.
   - tail_thirteen_sixteenths: for |P|<=t^16,t>0,
       sum_(p in P,p>D*t^13)1/p<=5/24,
     assumingD>=65536 and logD>=131072*(boundConstant+1).

10. ThirteenSixteenthPrimeBound.lean (150 lines).
    Fixed cutoff scale
      D=65536+ceil(exp(512*quadraticEnergyError+
                        131072*(boundConstant+1)+1)).
    thirteenSixteenthBoundConstant=512*exp4*D^2*(D+2)>0.
    - prime_survivor_thirteen_sixteenths:
        |P|<=t^16 and m>thirteenSixteenthBoundConstant*t^42
      imply a survivor in every prime-class configuration.
      Pad P with primes<=R=D*t^13; the tail estimate survives padding.
      Energy and cost give cost^2<=512*exp4*R^2*energy, and the total padded
      prime count plus one is <=(D+2)*t^16. No extra restriction on P is used.

11. ThirteenSixteenthPowerBound.lean (98 lines), Erdos970 namespace.
    - exists_sixteenth_power_envelope: for k>0 choose t>0 with
        k<=t^16<=65536*k, using Nat.find.
    - isJacobsthalBound_thirteen_sixteenths(k,t,ht,hkt).
    - jacobsthalFunction_eighth_le_twenty_first:
        jacobsthalFunction(k)^8<=twentyOneEighthConstant*k^21 for k>0.
    - exists_twenty_one_eighths_bound:
        exists C>0, forall k>0,
          (jacobsthalFunction k:Real)<=C*(k:Real)^((21:Real)/8).
      Printed final axioms are the three permitted axioms only.

CRITICAL LIMITATION: The remainder remains proportional to k*R^2. The improved
profile allows R~k^(13/16), giving exponent1+2*(13/16)=21/8. It does not remove
the prime-count factor, supply an exponent2 estimate, or construct a disproof.
No general impossibility claim about other profiles or other methods is made.

Final verification logs include:
  /tmp/cumulative_variation_lean.log
  /tmp/prime_all_log_moments_final.log
  /tmp/quadratic_layer_cake_final.log
  /tmp/quadratic_difference_layer_cake_lean.log
  /tmp/cumulative_prime_sharp_final.log
  /tmp/selberg_quadratic_profile_lean.log
  /tmp/selberg_quadratic_energy_lean.log
  /tmp/selberg_quadratic_cost_lean.log
  /tmp/thirteen_sixteenth_tail_lean.log
  /tmp/thirteen_sixteenth_prime_bound_final.log
  /tmp/thirteen_sixteenth_power_bound_lean.log
CheckCumulativeVariation.lean is an API scratch file and is not imported.
No background worker is active. Spec.lean retains its original sole sorry.

## Exact common-core Boolean tail cost completed

No settlement of erdos_970. Spec.lean remains unchanged with its original sorry.
CommonKernelTailCost.lean compiles and its olean is built. The final printed
axioms are only propext, Classical.choice, Quot.sound.
Log: /tmp/common_kernel_tail_cost_extended.log.

For coefficient lists a,b supported on subsets of S, define
  commonTailCoefficient(S,a,b,T)
    =a(T)-sum_(i outside S) hitShiftCoefficient(i,b,T).
Proved exact identities:
  L1(commonTailCoefficient)=L1(a)+|outside S|*L1(b),
  value(commonTailCoefficient)=value(a)-sum_(i outside S)X_i*value(b).
The shifted lists have pairwise disjoint monomial supports and are disjoint
from the core list at every nonzero coefficient. This is an equality, not a
triangle-inequality estimate.

The new completion defines hitProductCoefficient(i,b,T), the unrestricted
Boolean multiplication by X_i, and coreLowerCoefficient(S,b) representing
(1-sum_(i in S)X_i)*value(b). Then commonLowerCoefficient(S,b) represents
(1-sum_i X_i)*value(b), and its exact cost is
  L1(coreLowerCoefficient(S,b))+|outside S|*L1(b).
Generic core-support lemmas for ordinaryCoefficient and booleanSquareCoefficient
specialize this to b=booleanSquareCoefficient(ordinaryCoefficient(q,c)).
Final theorems include commonLower_value and commonLower_square_cost.

SCOPE: The omitted-prime factor cannot disappear merely by Boolean coefficient
merging for this common-core lower-weight class. No R^2 lower bound on the core
cost, no universal obstruction to other kernels, and no target negation follows.

## First-uncovered-position ordered cover reduction verified

GreedyCoverOrder.lean compiles and its olean is built. Permitted final axioms
only; log /tmp/greedy_cover_order.log. It currently imports OptimalCoverCore.
Namespace Erdos970.GreedyCoverOrder:
- firstPosition(U) is min(U), with default0 for the empty set.
- greedyStep(U,p) deletes the congruence class of firstPosition(U) modulo p.
- greedyResidual(U,l) iterates these deletions in list order.
- greedyResidues(U,l) gives their canonical residue assignment.
- greedyResidual_covers: removed positions are covered by those canonical
  residues if l has no repeated moduli.
- exists_greedy_order: ANY cover of a finite U by moduli in P admits a nodup
  list l with toFinset(l)=P and greedyResidual(U,l)=empty.
- cover_iff_greedy_order gives the exact converse too.

The proof repeatedly chooses an unused modulus covering the first unhit point;
its residue is thereby determined. This works without a primality hypothesis.
It removes arbitrary phase choices from fixed-modulus cover existence, but no
quadratic estimate for the stopping point of the ordered process was proved.
No numerical experiment or background worker was launched in this continuation.

GreedyCoverOrder.lean completion:
- cover_iff_permutations: cover existence is exactly emptiness of the greedy
  residual for at least one member of (P.sort).permutations.
- isJacobsthalBound_iff_greedy: IsJacobsthalBound(k,m) is equivalent to a
  nonempty residual for every nodup prime list of length at most k.
Both print only the permitted axioms. The completed file is 180 lines; its
olean was rebuilt successfully. CheckGreedy.lean and CheckGreedy2.lean are
scratch API files (the latter has deliberate unknown-identifier queries) and
are not imported by any verified development.

Further analytic review (no new estimates):
- Submultiplicativity of void probabilities for all adjacent interval lengths
  would, by fresh-prime thinning, imply the already-obstructed exact Poisson
  PGF domination. It must not be assumed as a shortcut from adjacent negative
  covariance. Restricted coarse-scale inequalities are not excluded by this.
- The rough-number phase also obstructs a uniform full-density discrepancy
  estimate of order k*sqrt(m)*density: at m=y^2 and k=pi(y), its relative
  discrepancy tends to a positive constant, whereas k/sqrt(m) tends to zero.
  This is an on-paper observation using the same standard asymptotics as the
  earlier PGF discussion, not a newly formalized theorem. It does not exclude
  weaker positive-density lower bounds or settle the target.
- No actual-interval aggregate tail estimate or prime-order stopping bound
  sufficient for exponent2 was established.

## Weaker void-tail sufficient conditions verified

Original conjecture STILL UNSOLVED. Spec.lean is unchanged with its original
sorry. New file WeakerVoidReduction.lean compiles; olean built. Both final
printed axioms lists contain only propext, Classical.choice, Quot.sound.
Log: /tmp/weaker_void_reduction.log.

Namespace Erdos970.GapAverages, importing ExponentialVoidReduction:
- PolylogVoidBound(c,B) is the EXPLICIT UNPROVED hypothesis, uniform over prime
  sets P with |P|<=k and interval lengths m,
    coveredFraction(P,m)<=exp(-c*m/log(k+2)^B).
  B is a fixed natural, not a function of k.
- eventually_log_power_entropy_small proves the required log-power/n limit.
- eventually_quadratic_of_polylog_void: for c>0 this hypothesis implies
    eventually h(k)<=k^2.
- quadratic_bound_of_eventually_scaled patches a known eventual estimate
    h(k)<=D*k^2, D>0, to the full real-constant quadratic conclusion.
- quadratic_bound_of_polylog_void gives that full conclusion conditionally.

A yet weaker critical-cardinality hypothesis was also identified and checked:
- CriticalVoidBound(c): uniformly for |P|<=k,
    coveredFraction(P,m)<=exp(-c*m*log(k+2)/(k+1)).
- scaled_quadratic_cap: if D<=k and
    q<=256*(D*k^2+k+1)^2,
  then q<=(k+2)^14 (after real casting).
- eventually_scaled_quadratic_of_critical_void: if 28<c*D, the critical tail
  hypothesis implies eventually h(k)<=D*k^2. The normalized cover phase-space
  entropy is at most14*k*log(k+2), while the proposed tail exponent exceeds it.
- quadratic_bound_of_critical_void: for any c>0 the critical hypothesis yields
  precisely the original conjecture's real-valued conclusion.

SCOPE: No version of either void hypothesis was proved for unrestricted prime
sets. These are sufficient conditions, not axioms, not a completed target proof,
and not consequences already supplied by the phase variance or adjacent-block
covariance results. The earlier exact-density thinning obstruction does not
immediately refute these cardinality-dependent rates, since appending primes
also weakens the rate. No general validity claim is made.

Further investigation of increasing-prime conditional variances, martingale
concentration, and ordered-cover counting supplied no new unrestricted estimate.
In particular, no deterministic L2 concentration inequality for a new largest
prime was established. The existing relative-plus-constant concentration
counterexamples must still be respected; they are not full interval covers.
No numerical scan or background worker was started in this continuation.

## Unconditional stretched-exponential void tail at quadratic scale verified

Original conjecture STILL UNSOLVED. Spec.lean unchanged; original sole sorry at
2177. This continuation obtained a genuinely unconditional probabilistic bound,
not merely another sufficient condition. It is nevertheless too weak to rule
out every exceptional covered phase and is NOT a settlement.

Five new files compile, with oleans built and permitted final axioms only:

1. EssentialCoverOrder.lean, namespace Erdos970.GreedyCoverOrder.
   - Covers and EssentialCover (one private witness per retained modulus).
   - exists_essential_subcover, by minimizing the number of retained classes.
   - EssentialCover.step preserves essentialness under first-position deletion.
   - exists_essential_order: the greedy order reproduces ALL the original
     residues modulo their moduli, rather than just finding another cover.
   - essential_order_mem_permutations.
   - greedyResidues_append_of_mem and greedyResidues_take_of_mem: residues
     assigned by a prefix do not depend on the remainder of the order.

2. EssentialCoverProbability.lean, namespace Erdos970.GapAverages.
   - phaseResidues extends a normalized Phase by zero off P.
   - matchingWeight is the coordinate-match indicator on a subset Q.
   - phaseMean_matchingWeight gives its exact mean product_(q in Q)(1/q).
   - covered_phase_exposes_prefix: if IsJacobsthalBound(j-1,m), any covered
     phase exposes a canonical order of exactly j prime residues.
   - coveredFraction_le_factorial_symmetric:
       coveredFraction(P,m) <= j! * sum_(Q subset P, |Q|=j) product_(q in Q)1/q.
     The exposure argument only needs an already valid bound for j-1 primes.
     There is NO union over every larger essential-core size: taking a prefix
     reduces the bound to exactly j coordinates.

3. SymmetricExposureTail.lean.
   - symmetric_generating_bound: x^j*e_j(w) <= product(1+x*w_p).
   - generating_core_tail_bound: if the reciprocal tail outside S is <=1/2,
       product(1+x*w_p) <= (1+x)^|S| * exp(x/2), for 0<=w_p<=1.
   - factorial_two_mul_exp_le:
       (2n)! * exp(2n) <= (4n)^(2n) * exp(-n/16).
     Uses (2n)! <= (2n)^n*n!, n!<=n^n, and exp2<8*exp(-1/16).
   - coveredFraction_le_core_exponential: if IsJacobsthalBound(2n-1,m)
     and the reciprocal mass outside S is <=1/2, then
       coveredFraction(P,m) <= exp(|S|*log(1+4n)-n/16).

4. FiveEighthTail.lean, namespace WeightedMertens.
   - log_eight_fifths_le: log(8/5)<=19/40, certified via
       8/5 <= (81/80)^38 and log x<=x-1.
   - tail_five_eighths: for |P|<=t^16, t>0, D>=1024, and
       log D>=2048*(boundConstant+1),
       sum_(p in P,p>D*t^10)1/p <=1/2.
     The upper comparison cutoff is D*t^16; the two error budgets are 1/1024.

5. StretchedQuadraticVoid.lean, namespace GapAverages.
   - exposure_core_log_bound: for t>=384*(D+1), |S|<=D*t^10+1,
       |S|*log(1+4*t^12) <= t^12/32.
     An elementary bound log(1+4*t^12)<=12t suffices; no asymptotic log lemma.
   - quadratic_bound_at_exposure_depth: the verified exponent21/8 bound,
     together with t^16<=65536k and a sufficiently large absolute t, supplies
       IsJacobsthalBound(2*t^12-1,k^2).
     Specifically t>=twentyOneEighthConstant*2^21*65536^16 is sufficient.
   - D is the existing thirteenSixteenthCutoffScale; it meets the tail conditions.
   - exposureThreshold is the maximum of this cardinality threshold and
     384*(D+1); its sixteenth power is an explicit threshold for k.
   - coveredFraction_quadratic_stretched and eventually_quadratic_stretched_void:
       for all sufficiently large k, uniformly over ALL prime sets P with |P|<=k,
         coveredFraction(P,k^2) <= exp(-(k:Real)^(3/4)/32).
     No cap on the prime magnitudes is assumed. This is UNCONDITIONAL.
   - stretched_exponent_le_phase_entropy: if |P|=k>0,
       k^(3/4)/32 <= sum_(p in P)log p.
     Thus the new exponent does not by itself beat the mass of a single phase.

CRITICAL LIMITATION: The uniform stretched exponent k^(3/4) is far short of the
critical k*log k scale used in the existing counting reduction at m~k^2. A tiny
but nonempty set of covering phases is still compatible with this new result.
No quadratic worst-case bound and no superquadratic actual cover was obtained.

Final logs include:
  /tmp/essential_cover_order.log
  /tmp/essential_cover_probability.log
  /tmp/symmetric_exposure_tail.log
  /tmp/five_eighth_tail.log
  /tmp/stretched_quadratic_void_final.log
and /tmp/{EssentialCoverOrder,EssentialCoverProbability,SymmetricExposureTail,
FiveEighthTail}_final.log. No numerical scan or background worker was launched.

Lean implementation note: directly applying Nat.pow_pos or
Nat.pow_le_pow_iff_left with the enormous concrete exposureThreshold caused a
kernel deep-recursion error, despite increasing maxRecDepth. Factoring the
same arguments through generic lemmas sixteenth_envelope_pos and
sixteenth_envelope_threshold (with a variable natural A) eliminated the issue.
The final theorems have successfully kernel-checked, non-self-referential
proofs and print ONLY the three allowed axioms. No kernel checks were disabled.
Also qualify Finset.mem_sdiff when Filter is open: Filter.mem_sdiff can shadow it.
Scratch CheckStretchedKernel.lean intentionally retains failing direct examples;
no verified file imports it or any other Check*.lean scratch file.

## Further exposure and high-moment review (no new theorem)

Original conjecture STILL UNSOLVED. No Lean source was changed in this
continuation. Spec.lean keeps its sole original sorry. No verification
submission or numerical worker was started.

The new stretched tail was reviewed against the exact exceptional-phase
threshold. Its exponent does not dominate sum(log p), as already formally
proved by stretched_exponent_le_phase_entropy. Neither the permutation
encoding nor minimal-cover extraction has supplied an additional factor which
would eliminate all exceptional phases. In particular, do not multiply two
separate upper bounds on the same covered fraction without an independence or
conditional estimate justifying that operation.

A high-central-moment route was examined. A Gaussian-shaped estimate
  E|S-mu|^(2r) <= (C*r*mu)^r
at r=k would yield, at m=D*k^2 and density~1/log k, only an exponent roughly
  k*log k - k*log log k + O_D(k),
whereas the first-k-prime phase entropy is
  k*log k + k*log log k + O(k).
Thus that particular moment estimate, even if available at order2k, does not
remove the logarithmic deficit.

ON-PAPER CAUTION, NOT LEAN-FORMALIZED: extending this same full-centered
Gaussian estimate uniformly to r=ceil((1+epsilon)*k), epsilon>0, is obstructed
by the earlier rough-number phase. For P the first k primes, m=D*k^2, and the
phase representing integers1,...,m, PNT and sharp Mertens give
  S/mu -> exp(gamma)/2 <1,
  log(product P) = k*log k+k*log log k+O(k).
That single phase contributes at least (c0*mu)^(2r)/product(P) to the moment,
for some fixed c0>0. Its ratio to (C*r*mu)^r has logarithm
  epsilon*k*log k - (2+epsilon)*k*log log k + O_{C,D,epsilon}(k),
which tends to positive infinity. This only excludes the stated uniform
full-centered Gaussian moment proposal. It does NOT rule out suitably
one-sided lower-tail moments, other concentration estimates, or the original
quadratic conjecture. No such stronger one-sided estimate was proved.

## Further actual-interval and overlap review (no new theorem)

No settlement and no Lean-source change in this continuation. Re-examined
large-prime overlaps, canonical first-hit orders, and possible conditional
largest-prime second-moment estimates. No uniform estimate excluding every
cover was obtained. In particular, no nonlinear concentration statement was
derived from the verified pair moments, and no additional independence of
cover events or exposure prefixes was proved.

The fact that distinct primes p,q with p*q>=m have at most one common hit
cannot by itself control the core-sifted union of all such intersections at the
scale needed for the quadratic target. Counting pair incidences may greatly
overcount concurrent intersections; conversely, replacing this by a stronger
distinct-intersection estimate requires a proof not present here. No such
estimate should be assumed in subsequent work.

Spec.lean retains its original theorem and sorry. No submit_proof call, no
numerical experiment, and no background worker in this continuation.

## Further review of canonical orders and concentration (no settlement)

No new Lean theorem was obtained in this continuation. The original Spec.lean
was not changed, and no proof was submitted.

Reviewed whether canonical greedy orders, multiple window encodings, or
negative association after exposing a small-prime core could amplify the
verified stretched void tail enough to exclude every covering phase. No such
amplification was justified. In particular, overlapping windows depend on the
same prime residues, so their cover probabilities cannot simply be multiplied.
A negative-association argument on disjoint residue-coordinate sets would need
a proved packing statement; none was supplied. Likewise, a concentration bound
based only on a maximum class size m/p does not automatically control the
exceptional phases at the required entropy scale.

Also reviewed the induction based on a putative quadratic bound for a smaller
prime set: its guaranteed number of survivors, obtained by partitioning into
intervals of that bound's length, is far weaker than a uniform density estimate.
No density estimate or uniform conditional-variance bound should be inferred
from that gap bound alone.

These are limitations of the arguments examined, not a disproof of any of the
unproved sufficient conditions and not a disproof of the original conjecture.

## Exact one-coordinate cover fibers and insertion identity verified

Original conjecture STILL UNSOLVED. Spec.lean is unchanged, with its original
sole sorry at 2177. No proof was submitted.

New file Submission/CoverFiberIdentity.lean compiles and has a built olean.
Namespace Erdos970.CoverFibers; all final printed axioms are permitted.
Log: /tmp/cover_fiber_identity.log.

Definitions and results:
- completingResidues(U,p): normalized residues whose class contains all of U.
- Concentrated(U,p): U is nonempty and all its points agree modulo p.
- completingResidues_card: for p>0 the fiber cardinality is p if U is empty,
  1 if U is nonempty and concentrated, and 0 otherwise.
- completingResidues_mean: exact normalized indicator formula.
- phaseSurvivors and phaseSurvivors_empty_iff connect to the existing phase
  interval count.
- extendPhase and insertPhaseEquiv: genuine bijection
      Phase(P) x Fin(p) <-> Phase(insert p P), when p is not in P.
- inserted_cover_iff: the added residue completes coverage precisely when it
  contains every old survivor.
- inserted_cover_fiber_mean and phaseMean_insert justify actual phase averaging.
- concentratedFraction(P,p,m): probability of a nonempty old survivor set lying
  in one class modulo p.
- coveredFraction_insert: the exact identity
      F(P union {p},m) = F(P,m) + concentratedFraction(P,p,m)/p.
- concentratedFraction_nonneg and concentratedFraction_le give the elementary
  bounds 0 <= concentratedFraction <= 1-F(P,m).
- coveredFraction_insert_le gives the resulting weak insertion inequality.

SCOPE: No sufficiently strong estimate on concentratedFraction was proved.
The exact identity does not justify nonlinear concentration, independence of
windows, or a quadratic worst-case bound. No new growth exponent or actual
superquadratic cover was obtained. The initial one-step translation and
phase-adaptive polynomial review also supplied no uniform quadratic estimate.

Implementation note: a dependent phase-coordinate equality is most reliably
used via `cases` on the subtype equality before rewriting extendPhase_new.
For products over a finset subtype, the existing `prod_attach` lemma works as
an exact `calc` step where direct rewriting against `univ` does not match.

## Competing completion primes and singleton phase tail verified

Original conjecture STILL UNSOLVED. Spec.lean unchanged, original sole sorry at
2177; no proof submitted. Three new files compile with built oleans and only
permitted final printed axioms:
- CompetingCoverFibers.lean
- CompetingCoverVariance.lean
- SingletonStretchedTail.lean
All use namespace Erdos970.CoverFibers.

CompetingCoverFibers:
- concentrated_product_dvd: the product of distinct candidate primes that
  concentrate U divides every ordered difference of two members of U.
- concentrated_product_lt: if U is a nonsingleton subset of [0,m), that
  candidate product is <m.
- concentrated_log_sum_le: consequently the sum of log p over concentrated
  candidates is <=log m.
- concentrated_candidates_card_le_one: if all distinct candidate pairs
  satisfy p*q>=m, at most one can concentrate a nonsingleton U.
- singletonFraction(P,m): probability of exactly one old survivor.
- concentratedFraction_log_sum_le gives
    sum_R log(p)*M_p <= log(m)*(1-F-S1) + sum_R log(p)*S1.
- concentratedFraction_sum_le, under the pair-product condition, gives
    sum_R M_p <= 1-F + (|R|-1)*S1.
- weighted_cover_increment_sum_le transfers the latter via the exact insertion
  identity, with p not in P enforced by disjointness of P and R.
These express mutual exclusion outside singleton phases, NOT independence.

CompetingCoverVariance:
- phaseSurvivors_card identifies the finite survivor cardinality with the
  existing real intervalCount.
- concentrated_card_le: |U|<=m/p+1 for a concentrated subset of [0,m).
- concentratedFraction_sum_le_variance: if all candidate pairs have product
  >=m and each m/p+1<=mu-b, b>0, where mu=m*density(P), then
    sum_R M_p <= mu*(1-density(P))/b^2 + |R|*S1.
  The proof applies the already verified phase variance once to the total
  candidate count outside singleton phases, rather than separately for each p.
- concentratedFraction_sum_le_half_mean gives
    sum_R M_p <= 4*(1-density(P))/mu + |R|*S1
  under the explicit half-mean size condition. No relative class-count bound
  or unproved nonlinear concentration estimate was used.

SingletonStretchedTail:
- concentrated_iff_singleton_of_large: when p>=m, a nonempty U in [0,m) is
  concentrated modulo p iff it has exactly one point.
- singletonFraction_le_new_cover: for fresh p>=m,
    S1(P,m) <= p*F(P union {p},m).
- exists_bounded_fresh_prime: if |P|<=k, one can choose a fresh prime
    m<=p<=256*(m+k+1)^2,
  by pigeonholing k+1 consecutive prime indices and using the existing prime
  counting lower bound. No bound on the primes already in P is needed.
- singletonFraction_quadratic_stretched: for k above the existing threshold
  and |P|+1<=k,
    S1(P,k^2) <= 256*(k^2+k+1)^2 * exp(-k^(3/4)/32).
- competing_concentration_quadratic combines this with the half-mean aggregate
  variance estimate; the candidate size and pair-product hypotheses remain
  explicit in the theorem.

SCOPE: These are exact structural identities and averaged estimates. None
excludes every exceptional completing phase for a specified prime. In the
case of a polynomially bounded fresh-prime pool, the earlier stretched void
estimate and the insertion identity can already give a stronger asymptotic
aggregate probability bound than the new variance term. No new Jacobsthal
power exponent, quadratic worst-case estimate, or superquadratic actual cover
was obtained. Singleton probabilities were not silently discarded.

Further examination of two-completion incidence bounds and code/entropy
arguments did not supply the additional uniform estimate. The earlier warnings
about arbitrary deletion doubling and about an optimal core containing 2 still
apply; neither was assumed. No numerical scan or background worker was started.

Logs:
  /tmp/competing_cover_fibers.log
  /tmp/competing_cover_variance.log
  /tmp/singleton_stretched_tail.log

## Absolute additive normalizer and exact hard-cubic energy verified

Original conjecture STILL UNSOLVED. Spec.lean remains unchanged, with its sole
original sorry at line 2177. No completed proof has been submitted. The best
verified worst-case exponent is STILL 21/8; there is NO 5/2 bound yet.

Six new development files compile and have built oleans. Their audited final
theorems use only propext, Classical.choice, Quot.sound. They do not use the
conjecture in Spec.lean.

### HardCubicProfileCertificate.lean

Exact, kernel-checked analytic and rational calculations for
  F(u) = 2392 + 11017*u - 8076*u^2 + 4667*u^3.
The intended profile is F(1-x) for 0<=x<=1 and zero for x>1, with a nonzero
endpoint jump. The functions in the file give the norm matrix
  N_ij = 1/(i+j+1)
and proposed energy matrix
  D_ij = (H_i+H_j-H_(i+j))/(i+j+1) + 1/(i+j+1)^2
for i,j in Fin 4, along with c=(2392,11017,-8076,4667).
The general monomial energy formula is not separately proved, but the actual
norm and split-shift integrals for this particular cubic ARE proved directly
by polynomial integration, giving exactly the same matrix values:

  hardCubicNorm = 4715325794/105
  hardCubicEnergy = 1410547801651/44100
  ratio = 1410547801651/1980436833480 (about 0.7122407429538675).

Theorems include:
- hardCubicNorm_integral
- integral_hardCubic_difference
- hardCubic_split_shift
- hardCubicEnergy_integral
- hardCubicEnergy_double_integral, which proves
    integral v=0..1 [ integral u=v..1 (F(u)-F(u-v))^2
                     + integral u=0..v F(u)^2 ] / v
      = hardCubicEnergy.
  The single point v=0 is handled via the actual Ioc integration interval.
- hardCubic_margin and hardCubic_margin_pos:
    (1-2877/10000)*Norm-Energy = 29338709201/11025000 > 0.
- log_four_thirds_lt_hardCubic_budget:
    log(4/3) < 2877/10000,
  using the existing log-series remainder at x=1/7, n=3.
- hardCubic_ratio_threshold:
    Energy/Norm < 1-log(4/3).
- hardCubic_positive and hardCubic_derivative_positive.
- hardCubic_not_quadratic_threshold:
    NOT (Energy/Norm < 1-log 2).
  This last fact concerns THIS profile and threshold, not all sieve methods.

Thus the continuous cubic energy calculation is no longer only a floating
numerical diagnostic. Its transfer to prime energy and a Jacobsthal power bound
is STILL UNPROVED.

Historical diagnostic behind this profile: piecewise-linear grids with
32,64,128,256,512 knots gave floating ratios approximately
0.71939214, 0.71560115, 0.71365049, 0.71265468, 0.71214893.
The endpoint appeared to approach a jump. Hard-cutoff monomial bases then gave
floating minima of about .71370035 (degree 1), .71294135 (degree 2), .71224074
(degree 3), .71197163 (degree 4), and .71173262 (degree 7). These broader
variational minima remain unverified diagnostics, not mathematical bounds.
The concrete cubic above, unlike those minima, now has an exact certificate.

### RadicalTailNormalizer.lean

Defines
  primeRadical(n) = product of n.primeFactors,
  radicalHalfWeight(n) = 1/(sqrt(n)*primeRadical(n)),
  radicalTailSeries = tsum n:Nat, n^(-3/2).
The latter series is summable, using Mathlib's real p-series theorem. The
zero term is zero under Real.rpow; there is no divergent n=0 contribution.

- primeRadical_mul and radicalHalfWeight_mul for coprime arguments.
- radicalHalfWeight_prime_hasSum computes the local prime-power series:
    sum_a radicalHalfWeight(p^a) = 1+1/(p*(sqrt(p)-1)).
- radicalHalfWeight_factored_hasSum: finite Euler-product identity.
- sqrt_prime_correction_le:
    1/(p*(sqrt(p)-1)) <= 4*p^(-3/2).
- radicalHalfWeight_factored_bound, uniformly in P:
    sum_{n in factoredNumbers(P)} radicalHalfWeight(n)
      <= exp(4*radicalTailSeries).

This avoids the initially proposed logarithmic Euler-moment calculation.

### RadicalHarmonicWindow.lean

- harmonic_Ioc: exact reciprocal sum on a natural Ioc.
- harmonic_multiplicative_window: harmonic difference bounded by 1+log b,
  including the case where the lower endpoint is below 1.
- reciprocal_multiples_window: for positive b,q and finite s satisfying
    0<d<=R<d*b and q|d for every d in s,
    sum_{d in s}1/d <= (1+log b)/q.
- log_add_one_le_twice_sqrt:
    1+log b <= 2*sqrt b for positive natural b.

### RadicalReciprocalBound.lean

- primeRadical_div_dvd: rad(n/rad(n)) divides rad(n), also treats n=0.
- radical_fiber_window_bound: for fixed positive b=n/rad(n), the tail fiber
  R<n, rad(n)<=R has reciprocal sum <=2*radicalHalfWeight(b).
- radical_reciprocal_finite_bound: for any finite s of positive P-factored
  numbers with radical at most R,
    sum_s 1/n <= harmonic(R) + 2*exp(4*radicalTailSeries).

Proof: split n<=R from n>R; group the tail by b=n/rad(n); use the injective
map n -> rad(n) within each fiber and retain rad(b)|rad(n); then apply the
harmonic-multiple window estimate and the convergent Euler-product bound.
No signed cancellation or independence assumption is used.

### SelbergNormalizerAdditive.lean

- primeWeight_fiber_hasSum: geometric prime-support fiber identity.
- primeNormalizer_harmonic_additive:
    primeNormalizer(P,R) <= harmonic(R) + 2*exp(4*radicalTailSeries).
  Uses the sigma family of (Q,b) with Q in smallDivisorFamily(P,R) and b
  Q-factored. The map (Q,b) -> (product Q)*b is injective because its prime
  factor set is Q. Every finite partial sum satisfies the preceding bound.
- additiveNormalizerConstant := 1+2*exp(4*radicalTailSeries).
- primeNormalizer_log_additive:
    primeNormalizer(P,R) <= log R + additiveNormalizerConstant.
  This bound is uniform in both P and R, with leading coefficient EXACTLY ONE.
- indexed_normalizer_log_additive.
- cumulative_prime_upper_additive.
- cumulative_prime_error_additive: when every prime <=R is present,
    |cumulativeMass(t)-t| <= additiveNormalizerConstant
  for 0<=t<=log R. The lower side uses the earlier t-1 bound.

This resolves the fixed-accuracy normalizer obstacle in the hard-jump program.
In particular the variation error no longer contains a term L/B that would
be multiplied by log log R.

### JumpProfileTransfer.lean

Defines the strict-cutoff profile
  jumpProfile(L,c,g,x) = if x<L then c+integral_x^L g else 0.
- weighted_jump_integral: exact representation including c*cumulativeMass(L).
- weighted_jump_error: if |cumulativeMass(t)-t|<=E on [0,L], then the profile's
  weighted-sum error is bounded by
    E*(|c| + integral_0^L |g|).
The endpoint atom is treated explicitly. No continuity at the cutoff is
assumed, and the jump c may be signed. This is a generic transfer theorem;
its specialization to the cubic squared-shift kernel has not been done.

### Scope and next steps

The existing common-kernel coefficient cost is still proportional to k*R^2.
The verified cubic energy margin corresponds to alpha=3/4 and hence the
potential auxiliary exponent 1+2*alpha=5/2, NOT 2. The actual quadratic
threshold for that model would require a ratio below 1-log 2, and this cubic
provably does not meet it. No exponent 5/2 theorem has yet been established.

Remaining work in the auxiliary cubic program:
1. Scale the cubic and specialize the jump/variation transfer to its norm
   and squared-shift kernels, keeping jumps at both L-v and L explicit.
2. Combine the resulting O(E*L^6) error with reciprocal/logarithmic prime
   sums. Since E is now absolute, L^6*log L is lower order than L^7.
3. Prove a tail budget <=2877/10000 for cutoff R=D*t^3 and |P|<=t^4.
4. Bound coefficient cost and absorb fixed lower-order errors to obtain 5/2.
These steps, even if finished, would NOT settle the original theorem.

Audit file:
  Submission/NormalizerAdditiveAudit.lean
Logs:
  /tmp/hard_cubic_cert.log
  /tmp/radical_tail_normalizer.log
  /tmp/radical_harmonic_window.log
  /tmp/radical_reciprocal_bound.log
  /tmp/selberg_normalizer_additive.log
  /tmp/jump_profile_transfer.log
  /tmp/normalizer_additive_audit.log
No numerical covering search or background worker was started in this round.

## Hard-cubic program completed: unconditional exponent 5/2 verified

Original conjecture STILL UNSOLVED. Spec.lean is unchanged, sole sorry at 2177,
SHA256 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed proof of the original theorem has been submitted.

The auxiliary hard-cubic program described in the previous section IS NOW
COMPLETE. The best verified worst-case power in these development files has
improved from 21/8 to 5/2. This is NOT a quadratic bound, and no claim is made
that it improves the strongest classical bounds in the mathematical literature.

Final theorems in Submission/HardCubicPowerBound.lean:

  Erdos970.isJacobsthalBound_three_quarters
    (k t : Nat) (ht : 0<t) (hkt : k<=t^4) :
      IsJacobsthalBound k (hardCubicPowerConstant*t^10)

  Erdos970.jacobsthalFunction_sq_le_fifth
    (k : Nat) (hk : 0<k) :
      jacobsthalFunction k ^ 2 <= fiveHalvesConstant*k^5

  Erdos970.exists_five_halves_bound :
    exists C>0, forall k>0,
      (jacobsthalFunction k : Real) <= C*(k : Real)^(5/2)

All nine new proof files and the audit file compile, have built oleans, and
all audited final theorems depend only on propext, Classical.choice, Quot.sound.
They import Submission.Work transitively, not the theorem in Submission.Spec.
No native_decide, new axioms, sorry, or admit was used.

### New files and proof architecture

1. SmoothCutoffTransfer.lean (65 lines)
   cutoffValue(L,f,x) is f(x) when x<L and zero otherwise.
   cutoff_smooth_error: for globally C1 f with |f(L)|<=M and |f'|<=D on [0,L],
   finite weighted cumulative discrepancy <=E gives
      |sum_i w_i*cutoffValue(L,f,a_i)-integral_0^L f|
        <= E*(M+D*L).
   The proof uses the prior explicit-jump transfer and integration by parts.
   No positivity of the weights or f is required.

2. CutoffSquareDifference.lean (148 lines)
   Uses the exact two-cutoff decomposition
      (cut_L f(x)-cut_L f(x+v))^2
        = cut_L(f^2)(x)
          + cut_(L-v)(-2*f(x)*f(x+v)+f(x+v)^2)(x),
   for v>=0. Both jumps are retained, including at x=L-v.
   If |f|<=B and |f'|<=D on [0,L], 0<=v<=L, it proves
      squared norm error <= E*(B^2+2*B*D*L),
      squared shift error <= E*(4*B^2+8*B*D*L).
   The latter main term is the actual split integral. The error does not
   vanish with v, which is intentional for a hard cutoff.

3. HardCubicTransfer.lean (182 lines)
   Defines
      scaledHardCubic(L,x)
        =10000*L^3-8866*L^2*x+5925*L*x^2-4667*x^3,
   and its strict hard cutoff hardCubicProfile.
   Proves on 0<=x<=L:
      0<=scaledHardCubic<=10000*L^3,
      |derivative|<=35000*L^2.
   Proves the exact norm integral hardCubicNorm*L^7 and exact split-shift main
      J(L,v)=5721664*L^6*v +(428544696/5)*L^5*v^2
        -(434463325/6)*L^4*v^3 +49600525*L^3*v^4
        -(147536616/5)*L^2*v^5 +9217325*L*v^6 -(239589779/70)*v^7.
   In particular J(L,L)=hardCubicNorm*L^7.
   Specializes the transfer to obtain
      norm error <=800000000*E*L^6,
      shift error <=3200000000*E*L^6.

4. HardCubicPrimeProfile.lean (146 lines)
   Specializes to primeLogLocation and the Selberg weights, with the absolute
   E=additiveNormalizerConstant established in the previous round.
   - prime_hardCubic_square_error
   - prime_hardCubic_dirichlet_coordinate
   - prime_hardCubic_dirichlet_le, with accumulated error exactly bounded by
       3200000000*E*L^6 * sum_i 1/p_i.
     This reciprocal factor is explicitly retained, not discarded.
   - prime_hardCubic_cost_le:
       kernelCost <=10000*L^3*exp(2)*R.
   Strict support implies zero outside divisorSupport(p,R), as required.

5. HardCubicPrimeEnergy.lean (147 lines)
   Adds the sharp first logarithmic prime moment to the previously verified
   all-higher-moment theorem, and transfers all seven terms in J.
   - prime_hardCubic_shift_main_le:
       sum_i J(L,min(log p_i,L))/p_i
         <=(hardCubicEnergy+hardCubicNorm*T)*L^7
           +1000000000*sharpMomentError*L^6,
     where T=sum_{p_i>R}1/p_i.
   - prime_hardCubic_energy_lower, assuming T<=2877/10000:
       kernelEnergy >=2000*L^7
         -(800000000*E+1000000000*sharpMomentError
             +3200000000*E*sum_i1/p_i)*L^6.
   The rational leading margin was verified from the earlier exact cubic
   certificate, not from a floating approximation.

6. HardCubicEnergyThreshold.lean (136 lines)
   Absorbs the reciprocal-prime jump error without needing a log-log theorem.
   For fixed integer B>=2,
      sum_{p<=R}1/p <= B+(log R+boundConstant)/log B.
   Let A=3200000000*E and B=ceil(exp(A+1))+2, both absolute constants.
   Then A/log B<=1. With the tail budget <=2877/10000<1, the entire coefficient
   of L^6 in the energy error is <=L+hardCubicEnergyThreshold, an absolute
   threshold. Consequently, for L>=hardCubicEnergyThreshold,
      prime_hardCubic_energy: kernelEnergy >=L^7.
   No growing accuracy parameter or unverified asymptotic estimate is used.

7. ThreeQuarterTail.lean (72 lines)
   Proves log(4/3)<=28769/100000 using the log-series remainder at 1/7, n=3.
   Using the established prime-set tail bound, obtains
      tail_three_quarters:
        |P|<=t^4, D>=1000000,
        log D>=2000000*(boundConstant+1)
        => sum_{p in P, p>D*t^3}1/p <=2877/10000.
   Both errors from the prime-set estimate are bounded by 1/1000000.

8. HardCubicPrimeBound.lean (159 lines)
   Sets the absolute scale
      D=1000000+ceil(exp(hardCubicEnergyThreshold
                         +2000000*(boundConstant+1)+1)).
   For R=D*t^3, pads the prime set by all primes through R, applies the above
   energy and cost estimates, and uses survivor_of_kernelEnergy.
   With
      hardCubicBoundConstant=100000000*exp(4)*D^2*(D+2),
   proves prime_survivor_three_quarters for |P|<=t^4 and
      hardCubicBoundConstant*t^10 < m.
   The factor proportional to the total number of primes is still present
   in the interval error. It is exactly why the exponent here is 5/2, not 2.

9. HardCubicPowerBound.lean (98 lines)
   Converts the prime-class survivor theorem to IsJacobsthalBound, uses an
   integer fourth-power envelope k<=t^4<=16*k, and proves the final natural
   square/fifth-power bound and real exponent 5/2 statement above.

Audit:
  Submission/HardCubicBoundAudit.lean
  /tmp/hard_cubic_bound_audit.log
Per-file compilation logs have the corresponding snake_case basename in /tmp.

### What did NOT change

The initial review of alternative coefficient-cost and phase-geometry routes
produced no unrestricted quadratic certificate or actual superquadratic
family of consecutive-interval covers. The exact common-kernel omitted-prime
cost remains an obstruction to simply deleting its cardinality factor.
This is not a theorem that all other kernels or sieve methods must fail.

The concrete cubic still provably fails the continuous threshold 1-log 2
that would be needed for a quadratic result in the current common-kernel
model. The 5/2 theorem does not imply a quadratic bound by changing its constant.
The square-root improvement of an exposure exponent would likewise not by
itself exclude all exceptional covering phases; no such claim was made.

Priority for actual settlement remains a genuinely new unrestricted argument,
not merely deriving further averaged consequences of this auxiliary bound.
No numerical cover scan or background worker was started in this round.

## Post-5/2 unrestricted-route review: no new theorem

Original conjecture STILL UNSOLVED. Spec.lean is unchanged and retains its
original sole sorry at 2177. The best auxiliary power remains 5/2, proved in
HardCubicPowerBound.lean. No proof of the target has been submitted.

Re-examined these potential routes to a genuinely quadratic argument:

- LargestPrimeIncrement and its necessary global two-survivor consequence.
  The existing exact reduction for a new prime p greater than the old gap
  bound remains valid. No proof of the global two-survivor strengthening was
  obtained. A local companion within O(k) cannot be substituted: the already
  verified SymmetricIsolation construction refutes that shortcut. The
  isolation construction still does not refute LargestPrimeIncrement, since
  the longest old gap may occur elsewhere in the period.

- Global reoptimization of a singleton-survivor interval by moving a prime
  class to its hole. Such a move can uncover private positions in the interior;
  the existing private-position and exchange results do not guarantee an
  improving move, even though arbitrary phase changes are permitted. No
  assertion that local stability implies global optimality was used.

- Canonical first-uncovered-position ordering. The verified greedy-order
  equivalence removes arbitrary residue choices for a fixed ordering, but a
  quadratic stopping bound is still missing. No justification was found for
  restricting to increasing prime order or for exchanging two prime choices
  without losing coverage. Old permutation or adjacent-gap scans were not
  repeated.

Also reviewed lower-tail blocking with primes larger than each block.
Conditioning on the small-prime phases does not make different blocks
independent: a single large-prime residue can hit several distant blocks.
Multiplying separate conditional block-cover probabilities would therefore
require a further theorem. The accumulated-error or phase-entropy loss was
not silently discarded. No sufficient concentration estimate was proved.

No new Lean source was added in this review, no cover scan was launched, and
no background worker remains. These observations are not a proof or disproof
of the original conjecture and do not improve the verified exponent.

## Linear double-cover bound and conversion obstruction completed

Original conjecture STILL UNSOLVED. Spec.lean is unchanged, with its sole sorry
at 2177 and SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
The best unrestricted auxiliary exponent remains 5/2. Do not submit Spec.lean
as a completed solution.

The multiplicity-at-most-two branch is now fully proved, rather than merely
proposed. All seven new source files compile, their oleans are rebuilt, and
all final axioms are only propext, Classical.choice, Quot.sound:

1. DoubleCoverSelectedPairs.lean (154 lines)
   - four_band_margin: for a<=.184, b<=.225, c<=.184, d<=.512 and
     nonnegative a,b,c,
       1-a-b-c-d+(a+b)^2/2+a*c >= 24993/2000000 = .0124965.
   - triple_product_gt: no triple hit implies m<p*q*s for any three
     distinct retained primes; this uses an explicit CRT witness, including
     the equality endpoint, not an insufficient absolute-error estimate.
   - small_core_card_le_two: t^3<=m implies at most two primes <=t.
   - cover_selected_pairs_bound: for disjoint prime sets Q,R, selected
     family F subset R.powersetCard 2, coverage by Q union R, and tail hit
     multiplicity <=2,
       m*density(Q)*(1-sum_R 1/p+sum_{T in F}1/prod(T))
          <=2^|Q|*(1+|R|+|F|).
     This follows from exact core avoidance and selected-pair counting.

2. DoubleCoverPairFamily.lean (115 lines)
   F = H.powersetCard 2 union image(A x C, {p,q}), where A subset H and
   H,C disjoint. Proves the exact mass
       ((sum_H w)^2-sum_H w^2)/2 + (sum_A w)*(sum_C w)
   and card(F)<=|H|^2/2+|A|*|C|. Injectivity and disjointness of the selected
   pair families are explicit; no ordered/unordered factor is omitted.

3. DoubleCoverBandAnalysis.lean (98 lines)
   Exact log bounds log(6/5)<=.183, log(5/4)<=.224, log(5/3)<=.511.
   Under t>=2 and log t>=2000*(WeightedMertens.boundConstant+1), the bands
       A=(t^10,t^12], B=(t^12,t^15], C=(t^15,t^18], D=(t^18,t^30]
   have reciprocal caps .184,.225,.184,.512, uniformly in prime subsets.
   Also proves an eventual threshold beyond which pi(n)<=n/100.

4. DoubleCoverLinearCertificate.lean (81 lines)
   If |Q|<=2, |R|<=k, |F|<=m/5000, and the selected main expression is
   at least 1/100-k/m, then a double cover has m<=6000*k. Uses
   density(Q)>=1/4, density(Q)<=1, and 2^|Q|<=4, retaining all error terms.

5. DoubleCoverThirtieth.lean (130 lines)
   prime_double_cover_thirtieth: beyond the fixed analytic thresholds,
   every no-triple-hit prime-class cover of length t^30 satisfies
       t^30<=6000*|P|.
   Q is the <=t^10 core; the triple restriction proves |Q|<=2.
   R is the remaining tail; H=A union B. The reciprocal tail above t^30
   is <=|P|/t^30. Diagonal mass <=1/1000; selected pair count <=t^30/5000.

   IMPORTANT SIMPLIFICATION over the original plan: no three small-prime
   cases are required. Avoid the at most two core primes by exact
   inclusion-exclusion. This multiplies the cost by at most four and the
   mean by density(Q)>=1/4. The selected-pair inequality is applied only
   on core-avoiding positions. This handles all small-prime cases at once.

6. DoubleCoverLinear.lean (69 lines)
   - thirtieth_power_floor, using Nat.findGreatest, gives
       t^30<=m<(t+1)^30, and T^30<=m implies T<=t.
   - prime_double_cover_linear:
       exists C>0, every prime-class cover of multiplicity <=2 has
       m<=C*|P|.
   Prefix restriction and (t+1)^30<=2^30*t^30 extend the power-length
   theorem to all m, with bounded lengths absorbed into the constant.

7. DoubleCoverConversionObstruction.lean (29 lines)
   - no_constant_factor_double_conversion:
     There is no fixed A>0 permitting every arbitrary prime-class interval
     cover to be replaced by a multiplicity<=2 cover of the same interval
     using at most A times as many primes. Every prime and every residue
     in the replacement may be changed. This is derived from the new
     linear double-cover bound and the earlier no_linear_cover_bound.

Audit:
  Submission/DoubleCoverLinearAudit.lean
  /tmp/double_cover_linear_audit.log
  Per-file final rebuild logs: /tmp/DoubleCover*_final.log
No background process or numerical search remains.

### Consequence and remaining gap

The constant-factor multiplicity-reduction route to the existing quadratic
bound is now formally disproved, even allowing arbitrary global reoptimization.
This disproof is NOT the negation of erdos_970. General covers may have triple
and higher hits, so neither the linear bound nor its certificate applies to
them. No unrestricted quadratic proof or superquadratic covering family was
obtained. The new auxiliary theorems have deliberately not been inserted into
Spec.lean or represented as a completed solution.

Revisited the common-kernel remainder route as well. Exact coefficient-cost
identities still do not imply a lower bound on actual interval discrepancy,
but no sufficient uniform cancellation estimate was proved. A standard
lower-sieve plus upper-tail comparison at m~k^2 has matching leading losses:
with cutoff z=k/log^B(k) and sieve level D=m/log^A(k), the schematic lower
coefficient is 2B-A, whereas the tail upper coefficient is 2(B+1). Merely
increasing B does not create a positive margin. This is an explanation of
why that particular comparison did not close, not a universal impossibility
claim about sieve methods.

## Greedy ordering stability review and two kernel-checked obstructions

Original conjecture STILL UNSOLVED. Spec.lean is unchanged and still contains
its sole sorry. No proof/disproof of erdos_970 was obtained or submitted.

Examined a possible amortized sorting route after the completed linear
double-cover branch. The existing GreedyCoverOrder equivalence represents
cover existence by some canonical first-uncovered-position prime ordering.
A sufficiently cheap comparison with an increasing ordering might therefore
be useful. Neither a general sorting comparison nor the required increasing-
order endpoint bound was proved.

Two particularly simple proposed comparison lemmas are FALSE, now verified
in Submission/GreedySortingObstruction.lean (olean built):

1. Adjacent inverted swap need not lose at most two positions.
   beforeSwap = [5,3,2,7], endpoint in range100 =9.
   afterSwap  = [5,2,3,7], endpoint in range100 =6.
   Both residuals are nonempty and both lists are permutations of four
   distinct primes. Thus sorting the adjacent 3,2 loses three positions.
   The theorem no_two_position_adjacent_loss explicitly negates the proposed
   universal local bound. This does NOT refute a larger fixed local constant
   or a more subtle amortized sorting inequality.

2. The first k primes need not maximize the canonical endpoint among
   increasing prime lists of length k.
   firstSeven   = [2,3,5,7,11,13,17], endpoint in range100 =17.
   shiftedSeven = [2,3,7,11,13,17,19], endpoint in range100 =21.
   Both lists are strictly increasing, prime-valued, and have length7.
   Every coordinate of shiftedSeven is >= the corresponding firstSeven
   coordinate. Thus coordinatewise larger sorted primes can increase the
   canonical greedy endpoint. This says nothing about the maximal endpoint
   over all permutations of the respective prime sets.

All finite certificates use decide +kernel, not native_decide. All printed
axioms are only propext, Classical.choice, Quot.sound.
Log: /tmp/greedy_sorting_obstruction.log.
Diagnostic scripts (not trusted by the proofs):
  /tmp/greedy_adjacent_stability.py
  /tmp/greedy_sorted_comparison.py
Both terminated at the displayed small witnesses. No worker remains active.

Other routes reviewed without a new theorem:
- Moment/cost methods: all-degree unit-error information is stronger than
  fixed-degree moments, but no successful uniform quadratic global polynomial
  was found. Existing numerical feasible moment relaxations are not actual
  interval covers and were not treated as counterexamples.
- Positional Fourier/Gram-matrix ideas: no uniform arithmetic discrepancy
  cancellation was proved. Coefficient-cost obstruction is not automatically
  an obstruction to every phase-dependent discrepancy estimate.
- Bilinear/product candidate sets and prime-class matching descriptions did
  not yield a lower survivor count sufficient for the target.
- A hypothetical tensor amplification of covers could interact with a
  near-quadratic upper bound, but residue classes on product digit grids do
  not automatically become single classes for new distinct primes; no such
  amplification was asserted.

The original unrestricted quadratic bound, and its negation, both remain
unproved in this development. Auxiliary exponent remains5/2.

## Survivor resampling, affine phase transfer, and conditional Chernoff

Original conjecture STILL UNSOLVED. Spec.lean remains unchanged, with its
sole sorry in erdos_970. No submission of an incomplete proof was made.
The best unrestricted auxiliary exponent remains 5/2; no improved void-tail
exponent or unrestricted quadratic argument was obtained in this branch.

New completed development files (all final axioms permitted):

1. SurvivorResampling.lean (completed in the preceding context):
   For S before insertion, old residue b, U=S avoiding b, N=|U|,
   B=old-class hits, and C_a=hits in U by a, the increment Delta_a obeys
       Delta_a = (if a=b then 0 else B) - C_a.
   Mean: E Delta=(1-1/p)B-N/p.
   Second moment: E Delta^2=(1-1/p)B^2-2BN/p+E C_a^2.
   Centered variance: Var Delta=Var C_a+((p-1)B^2-2BN)/p^2.
   Downward change is controlled by old survivor hits; upward change by
   private positions. At U empty, resampling second moment is
   (1-1/p)B^2, not necessarily zero.

2. PrimeCoverResampling.lean:
   Links the abstract populations to OptimalCoverCore.survivors and
   privatePositions under Function.update, using a normalized old residue.
   Main theorems: prime_resampling_increment,
   prime_increment_second_moment, prime_covered_second_moment.
   Genuine cover example P={2,3}, m=3, r(2)=0,r(3)=1: zero old survivors,
   two private positions for p=2, resampling raw second moment=2.
   no_survivor_only_conditional_second_moment negates the existence of a
   uniform C times current-survivor-count bound for conditional increments.
   This is NOT a disproof of erdos_970. Finite checks use decide +kernel.

3. AffinePhaseRescaling.lean:
   Constructs affineResidueEquiv and affinePhaseEquiv from coprimality.
   For d coprime to every core prime, the count on a+d*t, 0<=t<n, has
   exactly the same uniform-core-phase distribution as intervalCount(P,n).
   progression_distribution transports ANY scalar statistic F:real->real,
   not only the first two moments. This does not factor joint statistics
   of different rows, which remain correlated through the common phase.
   rowCount_eq_progression retains the rounded progressionLength.
   row_variance_eq and row_variance_le give the single-row variance.

4. RowConditionalVariance.lean:
   rowCount_eq_classHits identifies weighted row counts with hits in the
   genuine phaseSurvivors population. The rows partition that population.
   Let V(n)=countVariance(P,n), delta=density(P), q=floor(m/p), and
   theta=m/p-q. For p coprime to the core, the exact averaged identity is
       E_core Var_a(rowHits) =
         (1-theta)V(q)+theta V(q+1)+delta^2 theta(1-theta)-V(m)/p^2.
   Main results: mean_rowConditionalVariance,
   mean_rowConditionalVariance_rounded, mean_rowConditionalVariance_le.
   Upper bound retains the negative V(m)/p^2 term:
       <=(m/p)delta(1-delta)+delta^2 theta(1-theta)-V(m)/p^2.
   The finite-statistic interpolation is exact for arbitrary F on the
   two adjacent integer row lengths. This is averaged over core phases,
   NOT a uniform bound at each core phase.

5. ConditionalSurvivorChernoff.lean:
   A finite independent-coordinate exponential estimate follows from
   exp(z)<=1+z+z^2 when |z|<=1. Each centered coordinate has mean zero.
   For a fixed old finite population S and independently chosen new
   prime residues P, put N=|S|, rho=sum_{p in P}1/p, and
       V_S=sum_{p in P} Var_a(classHits(S,p,a)).
   If t>=0 and |t*(classHits(S,p,a)-N/p)|<=1 for every p,a, then
       populationCoveredFraction(S,P)
          <=exp(-t*N*(1-rho)+t^2*V_S).
   Main results: phaseMean_exp_centered_sum_le,
   populationCoveredFraction_le, centeredHits_abs_le,
   mean_classVariance_sum.
   This is a LOCAL variance-sensitive Chernoff estimate with an explicit
   boundedness condition, not a full unrestricted Bennett theorem.
   mean_classVariance_sum transports the exact averaged row-variance
   identity to a sum of candidate-prime variances by linearity.

Remaining analytic gap:
- Averaging the last exponential bound over old phases requires nonlinear
  control of the conditional variance budget together with the old count.
- Its known mean cannot simply be substituted into exp(+t^2 V): Jensen's
  inequality gives the opposite direction.
- A resulting tail must still beat the FULL phase entropy, not just that
  of the core. No such estimate or quadratic implication was proved.
- Merely restricting to sparse tail primes does not resolve low-survivor
  core phases at the parity/sieve boundary.

Logs:
  /tmp/survivor_resampling.log
  /tmp/prime_cover_resampling.log
  /tmp/affine_phase_rescaling.log
  /tmp/row_conditional_variance.log
  /tmp/conditional_survivor_chernoff.log
Audit file: Submission/SurvivorResamplingAudit.lean
No background workers or numerical searches were started.

## Largest-prime review: exact multi-survivor reduction and conditional hierarchy

Original conjecture STILL UNSOLVED. Spec.lean is unchanged and retains its
sole original sorry. No proof submission made. Best unrestricted auxiliary
exponent remains 5/2. The resampling/Chernoff results did not close their
nonlinear averaging gap, so this round revisited the deletion route.

New verified files, with oleans built and only permitted axioms:

1. LargePrimeCountReduction.lean (132 lines)
   Namespace Erdos970.IncrementReduction.
   PrimeSetCountBound(P,m,t): every old residue phase leaves at least t
   survivors in [0,m). Its t=1 case is equivalent to PrimeSetBound.

   cover_remaining_with_prescribed_moduli:
   Any prescribed set R of unused distinct moduli can cover the old
   survivor population if its size is at least that population's size.
   This extends the earlier fresh-prime construction to a prescribed R,
   with explicit preservation of the old residues on P.

   primeSetBound_union_iff_count_of_injective:
   If every new modulus is injective on the old survivors at every phase,
       PrimeSetBound(P union R,m)
         iff PrimeSetCountBound(P,m,|R|+1).
   Disjointness of P and R is required. No primality is needed for this
   abstract one-hit equivalence.

   primeSetBound_union_large_iff_count:
   The exact equivalence applies when all p in R satisfy p>=m.

   primeSetBound_union_half_large_iff_count:
   If 2 is already in P and R consists of disjoint odd primes, it suffices
   that 2p>=m for each p in R. Proof uses same-parity separation, not
   independence of rows.

2. IncrementCountConsequences.lean (102 lines)
   Every theorem using LargestPrimeIncrement has it as an EXPLICIT
   hypothesis. No theorem asserting that increment was added.

   primeSetBound_union_of_increment:
   For nonempty old P with |P|=k and known bound g, adjoining t distinct
   primes, each above every old prime, would give bound
       g+2kt+t(t-1).
   The proof orders the new primes by maximum and retains the exact old g.

   exists_prime_set_above:
   Constructs a prescribed cardinality of fresh primes beyond any threshold.

   count_bound_of_largestPrimeIncrement:
   Choose those new primes beyond the displayed interval length and apply
   the exact one-hit equivalence. Thus the proposed increment implies
       PrimeSetCountBound(P, g+2kt+t(t-1), t+1)
   for every t. This generalizes the existing two-survivor consequence.

   length_lt_increment_envelope_of_few_survivors:
   Under the same increment hypothesis, an actual interval with <=t old
   survivors must have length strictly less than g+2kt+t(t-1).

Audit: Submission/IncrementCountAudit.lean
Logs: /tmp/large_prime_count_reduction.log
      /tmp/increment_count_consequences.log
      /tmp/increment_count_audit.log
No sorries or native_decide occur in either new development file.

Remaining gap in this route:
- The existing two-survivor equivalence requires p>g, or 2p>g with parity.
- The new one-hit count equivalence requires p>=m, or 2p>=m with parity.
- Neither proves modular separation for smaller newly adjoined primes.
- The hierarchy is a consequence to test/prove, not a proof of the increment
  and not a sufficient replacement for its smaller-prime cases.
- The old diagnostic scans and SymmetricIsolation obstruction remain only
  what their earlier entries state; no new uniform increment was inferred.

Additional small exact-integer diagnostic (not Lean formalized in this round):
For canonical greedy endpoint in range500,
  [5,3,2,7] gives 9, whereas moving 2 to the front gives [2,5,3,7] with 7.
Thus unconditional endpoint monotonicity under moving the minimum to the
front cannot be assumed. This says nothing about an O(k) amortized loss or
about globally maximizing over all prime orders. No numerical worker is
running. No new generalized-gap scan was started.

## Radial and nonradial common-kernel barriers (completed)

Original conjecture STILL UNSOLVED. Spec.lean unchanged, with its sole original
sorry. Best unrestricted auxiliary exponent remains 5/2.

Verified files (oleans built; audit permits only propext, Classical.choice,
Quot.sound):

1. ProfileTriangleIntegral.lean: exact continuous-profile identity
   int_0^1 A_f(v) dv = int f^2 - (int f)^2 + int (1-u)f(u)^2 du,
   where A_f(v)=int_v^1 (f(u)-f(u-v))^2 du + int_0^v f(u)^2 du.
   Uses compact-square Fubini and FTC.

2. RadialProfileBarrier.lean: for continuous f and EXPLICIT integrability
   of A_f(v)/v, E(f)>=N(f)/3. Thus for N(f)>0, E/N cannot be less than
   1-log 2, and (1-T)N-E<0 for T>=log 2. This excludes all such radial
   profiles in the common-profile scheme, not all sieve methods.

3. KernelSupportEnergyBound.lean: without any radial assumption,
   kernelEnergy(q,c)<=prod(1-q)*(sum c)^2. For c_Q=w(Q)f(Q), supported
   on D, weighted Cauchy-Schwarz gives
   kernelEnergy <= [prod(1-q)*sum_D w]*sum_Q w f^2.
   Scalar tail penalty at least the bracketed support mass makes the
   common-kernel energy nonpositive.

4. SmoothReciprocalMass.lean: Euler product lower bound from retaining
   R-smooth terms in the harmonic sum through N and charging each omitted
   term to a prime divisor greater than R:
   eulerMass(primes<=R) >= H_N-(1+log N)*sum_{R<p<=N}1/p
                            +sum_{R<p<=N}(log p)/p.

5. PrimeSupportMassBarrier.lean: specialize N=R^2, log R>=1, obtaining
   eulerMass(primes<=R)>=(3-2 log 2)log R-8(C+1), C the weighted Mertens
   constant. Beyond explicit supportMassLogThreshold this is at least
   (3/2)(log R+additiveNormalizerConstant). The verified additive divisor
   normalizer estimate implies normalized support mass <=2/3 for all
   squarefree products <=R with core primes <=R. Consequently EVERY
   (possibly nonradial) common kernel on that support has nonpositive
   energy after a scalar tail penalty T>=2/3.

Scope: the scalar tail parameter remains explicit. This does NOT handle
arbitrary prime-dependent kernels, signed actual interval remainders, or
other positional constructions. No original-conjecture disproof follows.
Actual quadratic-cutoff tail identification/asymptotics were not added.

Targeted nonradial spectral diagnostic, not a Lean theorem:
  /tmp/nonradial_divisor_spectrum.py and .log, scipy sparse eigsh.
  R=100,1000,10000,100000 gives min energy ratio
  0.41756710,0.49851954,0.54714907,0.57812483 respectively,
  compared with threshold 1-log2=0.30685282.
  Artifacts /tmp/nonradial_spectrum_<R>.npz. No asymptotic inference and
  no larger computation was started.

Audit: SupportBarrierAudit.lean, /tmp/support_barrier_audit.log.
Logs: /tmp/profile_triangle_integral.log, /tmp/radial_profile_barrier.log,
/tmp/kernel_support_energy_bound.log, /tmp/smooth_reciprocal_mass.log,
/tmp/prime_support_mass_barrier.log. In the last file, an apparent heartbeat
problem was resolved by explicitly rewriting Nat.cast_pow before change;
it was not a failure of the arithmetic inequality.

## Status after support-barrier audit

No settlement was obtained. Re-examining lower-tail rather than full-centered
concentration does not automatically close the conditional-variance or full
phase-entropy gaps. In particular the rough-number phase obstruction to a
Gaussian moment bound at fixed order (1+epsilon)k does not by itself rule out
all near-critical orders k+O(k loglog k/log k); however no valid estimate at
those orders was proved. No new moment theorem, conditional independence,
or strengthened void bound is being asserted.

The original Spec.lean remains unchanged, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9,
with the sole original sorry at line 2177. The support-barrier results are
auxiliary development only. No complete proof was submitted.

## Low-count cylinders and full conditional Bennett bounds (verified)

Original conjecture STILL UNSOLVED. Spec.lean unchanged; best unrestricted
auxiliary exponent remains 5/2. New oleans built; LowTailBennettAudit.lean
prints only propext, Classical.choice, Quot.sound.

1. LowCountCylinder.lean:
   AgreesOn and matchingWeight_agrees identify fixed-coordinate cylinders.
   For a covered phase and retained Q subset P, every phase agreeing on Q
   leaves at most deletionBudget(P,Q,m)=sum_{p in P\Q}(m/p+1) survivors.
   Thus lowCountFraction(P,m,B)>=prod_{p in Q}1/p when B covers that budget.
   More generally, for A>=B and any natural moment order d,
     E[max(A-N,0)^d]>=(A-B)^d*prod_{p in Q}1/p.
   survivor_of_deleted_moment and survivor_of_deleted_lowCount_tail are
   explicit sufficient criteria. prime_log_sum_le_cutoff gives retained
   entropy <=(log 4)y for primes<=y, and survivor_of_cutoff_lowCount_tail
   uses that smaller threshold. This improvement applies to LOW-COUNT
   probabilities, not directly to the previously known zero-count bound.

2. BennettAnalytic.lean:
   J(x)=int_0^1(1-u)exp(ux)du is nonnegative and monotone, with
   x^2 J(x)=exp x-1-x. Consequently for t>=0 and x<=B,
     exp(tx)<=1+tx+bennettFactor(t,B)*x^2,
   where bennettFactor=t^2 J(tB)=(exp(tB)-1-tB)/B^2 if B!=0.
   No lower bound on the increment and no |tx|<=1 restriction are needed.
   The optimized exponent uses h(x)=(1+x)log(1+x)-x.

3. ConditionalSurvivorBennett.lean:
   Independent new residue coordinates, conditional on a FIXED old
   population S, give
     Pr(cover S)<=exp[-t*N*(1-rho)+sum_p factor(t,B_p)*V_p].
   For common B>0, V=sum V_p>0 and u=N*(1-rho)>=0, optimization gives
     Pr(cover S)<=exp[-(V/B^2)*h(B*u/V)].
   If log(1+B*u/V)>=2 this is at most
     exp[-u/(2B)*log(1+B*u/V)].
   Caps are one-sided bounds on centered class-hit increments.

4. PopulationLowCountBennett.lean:
   Generalizes the same statements to Pr(new survivors<=b), with deficit
   u=N*(1-rho)-b. All sign and positive-variance hypotheses are explicit.

5. PhaseUnionBennett.lean:
   joinPhase/unionPhaseEquiv and phaseMean_union prove exact product-space
   factorization for disjoint core and tail prime coordinates. The survivor
   set and low-count probability decompose exactly under that bijection.
   lowCountFraction_union_bennett bounds the full low-count probability by
   the core expectation of min(1,exp[-t(r)*u(r)+sum factor*V_p(r)]).
   Crucially, the nonlinear expression stays INSIDE the expectation.
   survivor_of_averaged_bennett_cylinder combines this with the cylinder
   criterion; retained Q need not equal the analysis core P. Its strict
   nonlinear average bound remains an explicit unproved hypothesis.

Remaining gap: neither the actual conditional variances nor their nonlinear
average are controlled sufficiently to meet the retained-entropy threshold.
The earlier averaged-variance identity alone cannot be substituted inside
an exponential. Full-centred high moment estimates should not be assumed;
small-prime rough-number phases can already create nonnegligible fractional
count deviations, while a suitably sub-mean truncated moment may avoid that
particular obstruction. No truncated moment bound was proved in this round.

Logs: /tmp/low_count_cylinder.log, /tmp/bennett_analytic.log,
/tmp/conditional_survivor_bennett.log, /tmp/population_low_count_bennett.log,
/tmp/phase_union_bennett.log, /tmp/low_tail_bennett_audit.log.

## Rectangular variance route and unconditional count strengthening

Original conjecture still UNSOLVED. New verified files, with oleans built:

- RectangularVarianceTransfer.lean: a single row satisfies
  (rowCount-totalCount/p)^2 <= p*rowConditionalVariance.
  For m=p*n, affine phase rescaling identifies row zero exactly with ANY
  prescribed phase count on the shorter interval n. Consequently a uniform
  long-rectangle count >=p*A, plus UNIFORM row variance <=V and
  p*V<(A-b)^2, implies every short interval phase has count>b.
  The uniform variance assumption is not supplied by its known phase mean.

- KernelSurvivorCount.lean: arbitrary lower kernels give the count estimate
  m*energy-(numberCoordinates+1)*cost^2 <= (sum c)^2*survivorCount.
  The generic statement is specialized to distinct prime moduli.

- HardCubicCountKernel.lean: sum of hard-cubic coefficients is nonnegative
  and <=20000*(log R)^4 once log R>=additiveNormalizerConstant.
  Under the existing full-core, energy threshold, and tail hypotheses,
  if 2*10^8*exp(4)*(card+1)*R^2 <= m*log R, then
    m <= 800000000*log R*survivorCount.
  All hypotheses and the absolute error budget are explicit.

- HardCubicSurvivorCount.lean: UNCONDITIONAL count strengthening at the
  existing 5/2 cardinality scale. For |P|<=t^4, t>0, and
    m >= 2*hardCubicBoundConstant*t^10,
  every phase satisfies
    m <= 800000000*log(hardCubicCutoffScale*t^3)*intervalCount(P,m,r).
  This is a genuine uniform m/log(t) lower count above the 5/2 scale;
  it is NOT a count bound at quadratic lengths.

- HardCubicRectangularCriterion.lean: supplies the long-rectangle count
  input unconditionally at that scale. With
    A=n/hardCubicCountDenominator(t), |P|<=t^4,
    p*n >=2*hardCubicBoundConstant*t^10,
  any phase with short count<=b (b<=A) forces, after affine dilation,
    (A-b)^2 <= p*rowConditionalVariance(P,p*n,p,dilated_phase).
  A uniform variance upper bound strictly below that threshold would
  exclude every such short low-count phase. That upper bound is UNPROVED.

Targeted exact-integer diagnostic, not Lean formalized:
  /tmp/small_modulus_row_variance.py and .log.
  P is the first k primes, k=2,...,8; p is the next prime;
  n=C*p and m=C*p^2 for C=1,4,16. All shifts modulo product(P) are
  enumerated. Row counts T(a)=sum_{t<n}1_units(a+p*t) are exact integers;
  variance numerator is p*sum_{a<p}T(a)^2-(sum_{a<p}T(a))^2.
  Max variance / (m*density(P)/p), for C=1, was
  0.144000,0.371720,0.387866,0.486288,0.573033,0.686467,0.749694.
  No uniform or asymptotic variance bound follows. The condition p<=sqrt(m)
  and p above all core primes differs from the earlier large-p concentration
  counterexamples. No numerical worker remains.

Possible future direction, ON PAPER ONLY:
A much weaker bound than linear variance might suffice: a uniform bound
V_p(P,p*n) <=C*n^(4/3), for primes in P below p and n>=p, would combine with
large-scale counts, a cutoff around k^(5/4), and a cheap tail deletion to
imply a quadratic bound. No such variance estimate or full asymptotic
implication has yet been proved. Do not assume it.

Logs: /tmp/rectangular_variance_transfer.log,
/tmp/kernel_survivor_count.log, /tmp/hard_cubic_count_kernel.log,
/tmp/hard_cubic_survivor_count.log, /tmp/hard_cubic_rectangular_criterion.log.
All printed axioms after successful compiles were only the three permitted
ones. Spec.lean has not been changed and retains its original sorry.

## Uniform rectangular variance proposal: new obstruction (in progress)

The conjecture is STILL UNSOLVED. The proposed unrestricted estimate
V^3 <= C*n^4 for P consisting of primes below p and n>=p should NOT be
assumed or pursued as a likely true lemma. A zero-residue phase already
compares rough-number densities at two different scales.

New verified files, with oleans built and only permitted printed axioms:
- ZeroPhaseRectangularVariance.lean: zeroPhase and affine_zeroPhase;
  intervalCount_zeroPhase, row_zeroPhase_rectangle; exact lower bound
    (roughCount(P,n)-roughCount(P,p*n)/p)^2 <= p*V(P,p*n,p,zero).
  Also roughCount_primesBelow_eq: for p>2, p<=m<=p^2,
    roughCount(primesBelow(p),m)=primeCounting'(m)-primeCounting'(p)+1.
- RectangularVarianceScaleBarrier.lean: the proposed V^3 bound at n=p^2
  implies that the sixth power of the difference of the logarithmically
  normalized short/long densities is <=C*(log p)^6/p.
  rough_limits_eq_of_variance_cube_bound consequently forces any two
  such limiting densities to agree. Those limits remain explicit hypotheses.
- RectangularCountAudit.lean audits the preceding hard-cubic count and
  rectangular transfer chain; all audited axioms are permitted.

Analytic explanation (NOT a Lean disproof): for the zero phase with core
all primes<p and n=p^2, standard rough-number asymptotics give normalized
short density 1/2 and long density (1+log 2)/3. Their unequal values imply
V is at least a constant times p^3/(log p)^2, exceeding n^(4/3).
This is NOT a disproof of the Jacobsthal conjecture.

An elementary formal disproof of the VARIANCE PROPOSAL is being explored:
iteration of the rectangle comparison would imply a power-saving uniform
count discrepancy. Below the square of a cutoff this would force a
power-saving prime-counting scaling recurrence, contradicted by elementary
prime-counting bounds. This implication is not yet formalized.

Logs: /tmp/zero_phase_rectangular.log, /tmp/rectangular_variance_scale.log,
/tmp/rectangular_count_audit.log. Spec.lean unchanged.

## Auxiliary uniform variance bound DISPROVED (kernel checked)

Original erdos_970 STILL UNSOLVED. This is a disproof of an AUXILIARY estimate
only. Do not replace the target with this negation: its type is different.

The preceding in-progress elementary obstruction is now complete. New verified
files and built oleans, with permitted axioms only:

1. RectangularVarianceIteration.lean
   - roughCount_error: CRT inclusion-exclusion gives absolute discrepancy
     <=2^|P| from m*density(P).
   - roughCount_scaled_limit: roughCount(P,n*p^j)/p^j -> n*density(P).
   - upper_of_halving_recurrence_at / abs_sub_le_of_halving_recurrence:
     a convergent normalized scaling sequence with increments bounded by
     D*(p/2)^j differs from its limiting main term by at most 2D at j=0.
   - roughCount_discrepancy_of_variance_cube: if p>=8 and is coprime to P,
     V(P,p*(n*p^j),p,zero)^3 <= C*(n*p^j)^4 for every j, and
     p^3*C*n^4 <= D^6 with D>=0, then
       |roughCount(P,n)-n*density(P)| <=2D.
     Uses p^4 <=(p/2)^6 for p>=8. All premises are explicit.

2. PrimeCountingPowerSavingObstruction.lean
   - density'_tendsto_zero and elementary lower prime-counting bounds imply
     primeCounting'(4096^j) cannot be O(2048^j).
   - not_bounded_4096_difference / not_eventually_bounded_4096_difference:
     even the ONE-SIDED recurrence
       4096*pi'(4096^j)-pi'(4096^(j+1)) <= B*2048^j
     is impossible uniformly, or eventually, for any real B.
     This is a power-saving obstruction, with no PNT assumption.

3. UniformRectangularVarianceDisproof.lean
   - Defines UniformRectangularVarianceCubeBound(C) as the proposal:
       all prime sets P; prime p above all q in P; n>=p; all phases r:
         rowConditionalVariance(P,p*n,p,r)^3 <= C*n^4.
   - rectangle_power_budget: if C>=1, p<=128*t^6 and m<=4096*t^12,
       p^3*C*m^4 <=(4096*C*t^11)^6.
   - prime_recurrence_of_variance_cube: for t>=4, set y=64*t^6 and
     P=primesBelow(y). Bertrand gives y<p<=2y. Apply the iterated count
     discrepancy at m=t^12 and m=4096*t^12=y^2. Both counts have the exact
     prime-counting formula. The density cancels, yielding
       4096*pi'(t^12)-pi'(4096*t^12)
         <= (8194*4096*C+262080)*t^11.
   - not_uniformRectangularVarianceCubeBound(C): the proposal is FALSE
     for EVERY real C. Use t=2^j and the prime recurrence obstruction.
     The proof uses only zero phases, though the named proposal quantifies
     all phases. It does not construct a covered interval.

Audit: RectangularVarianceBarrierAudit.lean,
/tmp/rectangular_variance_barrier_audit.log. Other logs:
/tmp/rectangular_variance_iteration.log,
/tmp/prime_counting_power_saving.log,
/tmp/uniform_rectangle_variance_disproof.log.

Consequence for the research plan: DO NOT attempt to prove the previously
proposed uniform V^3<=C*n^4 estimate or use it as the missing ingredient in
the 48th-power quadratic reduction. It is now rigorously refuted, without
assuming the rough-number asymptotics discussed earlier. A suitably truncated
low-count estimate is not excluded, but none sufficient for erdos_970 has
been proved. The best unrestricted exponent is still 5/2.

Spec.lean is unchanged and still has its sole original sorry. No proof has
been submitted for verification as a purported solution of erdos_970.

## Soft exposure and unconditional sub-mean tail (VERIFIED)

Original erdos_970 STILL UNSOLVED. Best unrestricted gap exponent remains
5/2. A NEW unconditional lower-tail bound has been obtained. It improves the
old zero-count exponent 3/4 to 4/5 at a fixed absolute multiple of quadratic
length, and permits a positive threshold comparable to m/log k. It does not
exclude every phase and is NOT a quadratic Jacobsthal theorem.

Six new files compile, with oleans built:

1. SoftExposureTree.lean, namespace Erdos970.SoftExposure
   - avoid, survivors, hitFraction are finite population operations using
     arbitrary natural residue functions.
   - tree(0,U,P,r)=1, and
       tree(j+1,U,P,r) = sum_{p in P} hitFraction(U,p,r)
         *tree(j,avoid(U,p,r),P.erase(p),r).
     A weight is the fraction of the current population hit by the next
     class. This averages a uniformly chosen remaining witness; positions
     are NOT asserted to be independent.
   - budget(0,P)=1; budget(j+1,P)=sum_p (1/p)*budget(j,P.erase(p)).
   - PartialLower(j,U,P,r,A) requires every partial sieve Q subset P with
     |Q|<j to leave at least A positions.
   - tree_lower: if A>0, 0<=b<=A, PartialLower holds, and the full phase
     leaves <=b positions, then tree >=(1-b/A)^j.
     The union bound on hit counts is used only pointwise as a lower bound
     on the sum of the possible successful next-step weights.

2. SoftExposureAverage.lean
   - step_mean_le and tree_mean_le_budget: average only the independent
     residue coordinates, not positions. The continuation population may
     be arbitrary. Conditioning on a new coordinate costs at most 1/p.
   - lowCountFraction_mul_le_budget:
       (1-b/A)^j * Pr(S_m<=b) <= budget(j,P),
     provided the partial-count lower bound holds in every phase.
     There is NO binomial(m,b) loss for specifying survivor holes.

3. SoftExposureSymmetric.lean
   - weighted_insert_sum / symmetric_erase_sum double-count weighted
     subsets with a distinguished element.
   - budget_eq_factorial_symmetric: budget(j,P)=j!*e_j((1/p)_{p in P}).
   - lowCountFraction_factorial_symmetric is the corresponding soft
     extension of the previous hard ordered-exposure bound.
   - budget_le_core_exponential: if S subset P and the reciprocal sum
     outside S is <=1/2, then
       budget(2n,P) <= exp(|S|*log(1+4n)-n/16).

4. SoftExposureLowTail.lean
   - If b<=A/256, then log(1-b/A)>=-1/128.
   - lowCountFraction_le_core_exponential yields
       Pr(S_m<=b) <= exp(|S|*log(1+4n)-3n/64),
     retaining the uniform partial-count hypothesis and reciprocal-tail
     hypothesis explicitly.

5. HardCubicLowCountTail.lean
   - hardCubic_partial_count supplies PartialLower at depth 2*t^64,
     with A=m/hardCubicCountDenominator(2*t^16), whenever
       m>=2048*hardCubicBoundConstant*t^160.
     It uses the verified unrestricted hard-cubic survivor count, NOT the
     disproved uniform rectangular variance bound.
   - soft_exposure_core_cost: for t>=2048(D+1), a core of size
     <=D*t^50+1 has entropy penalty <=t^64/32.
   - lowCountFraction_envelope: for |P|<=t^80 and those length/threshold
     hypotheses, and D satisfying the existing reciprocal half-tail bounds,
       Pr(S_m<=b) <= exp(-t^64/64)
     for 0<=b<=m/(256*hardCubicCountDenominator(2*t^16)).
     The tail bound is FiveEighthTail applied at parameter t^5.

6. SoftQuadraticLowTail.lean
   - exists_power_envelope works for any positive natural exponent e:
     k<=t^e<=2^e*k with 0<t<=k.
   - softQuadraticScale is the positive natural constant
       (ceil(2048*hardCubicBoundConstant)+1)*2^160.
   - softLowCountLogConstant is the positive real constant
       256*800000000*(2*log(hardCubicCutoffScale)+6*log 2+48).
   - hardCubic_denominator_le_log bounds the previous denominator by this
     constant times log(k+2), including the factor 256.
   - eventually_soft_quadratic_low_tail and exists_soft_quadratic_low_tail:
     there are absolute B:Nat, B>0, and L:Real, L>0 such that for every
     sufficiently large k and every prime set P with |P|<=k,
       lowCountFraction(P,B*k^2, (B*k^2)/(L*log(k+2)))
         <= exp(-k^(4/5)/64).
     All hypotheses needed for this assertion are discharged.

Scope: the exponent k^(4/5) remains below the full phase entropy, which can
be of order k*log k. The available low-count cylinder criterion also needs
its deletion budget below the small low-count threshold; no unrestricted
argument meeting both requirements has been proved. This tail therefore
must NOT be substituted for a proof of erdos_970. No independence of rows,
Gaussian high moments, or uniform rectangular variance has been assumed.

Audit: SoftExposureAudit.lean; /tmp/soft_exposure_audit.log.
All audited axioms are only propext, Classical.choice, Quot.sound.
Logs: /tmp/soft_exposure_tree.log, /tmp/soft_exposure_average.log,
/tmp/soft_exposure_symmetric.log, /tmp/soft_exposure_low_tail.log,
/tmp/hard_cubic_low_count_tail.log, /tmp/soft_quadratic_low_tail.log.
Spec.lean remains unchanged with its original sorry at line2177.
No purported solution of the original conjecture has been submitted.

## Core-filtered cylinders, sharp Selberg rows, and exposure limitation

Original erdos_970 STILL UNSOLVED. The strongest unrestricted auxiliary
Jacobsthal exponent remains 5/2. The following three files are newly proved;
none removes the original sorry or gives its exact negation.

1. CoreFilteredDeletion.lean
   - corePhase restricts a phase to Q subset P.
   - count_le_core_of_agrees: all phases agreeing on Q have count at most
     the original Q-core count (no cover assumption needed).
   - filteredDeletionBudget sums the original tail residue hits only at
     positions surviving Q. Tail overlaps are still counted with multiplicity.
   - filteredDeletionBudget_le_deletionBudget proves the new budget is no
     larger than the old raw sum of m/p+1.
   - core_count_le_filteredDeletionBudget uses an actual cover.
   - count_le_filteredDeletionBudget and
     reciprocal_le_lowCountFraction_filtered give the improved cylinder.
   - reciprocal_le_lowCountFraction_of_core is stronger when the core count
     itself is known small, and does not assume the original phase covered.

2. CoreFilteredSelberg.lean
   - intervalCount_le_sharp_log transfers the existing upper sieve to Phase.
   - rowCount_le_sharp_log transfers it along the exact affine row, retaining
     its rounded length residueHits(m,p,a):
       row <= residueHits/log(R+1) + (exp(2)*R/log(R+1))^2.
     Requires all primes <=R in the core, and p coprime to the core.
   - rowCount_le_sharp_log_real replaces residueHits by m/p+1.
   - filteredDeletionBudget_le_sharp_rows permits a distinct cutoff R_p for
     each tail prime and sums EVERY main term and EVERY error term.
   - survivor_of_sharp_rows_low_tail supplies an explicit sufficient criterion.
     Its row-sum <= low-count-threshold premise is NOT discharged uniformly.
   No row independence or uniform variance assumption is used.

3. FilteredExposureBarrier.lean
   This identifies a real limitation of the particular soft-exposure/cylinder
   combination; it is NOT a disproof of the quadratic conjecture.
   - factorial_cylinder_weight_le_budget: for Q subset P and j<=|Q|,
       j! * product_{q in Q}(1/q) <= budget(j,P).
     Proof: choose a j-element subcore T of Q; its reciprocal product appears
     in the exact elementary-symmetric budget, and is >= the product for Q.
   - cylinder_weight_le_scaled_budget: if A>0 and 0<=b<A, then for |Q|>=j,
       product_Q(1/q) <= budget(j,P)/(1-b/A)^j.
     Thus the exact exposure upper bound cannot beat the cylinder weight in
     the large-retained-core case. Any upper estimate on that budget also
     cannot beat it.
   - partial_lower_core_count: if |Q|<j, the PartialLower(j,...,A) premise
     already gives coreCount(Q)>=A.
   - depth_le_core_card_of_filtered_cover: a covered phase with filtered
     budget <=b<A must therefore have |Q|>=j.
   - no_cover_of_small_core_filtered_budget: for |Q|<j, a filtered budget
     <=b<A contradicts a cover directly, WITHOUT a phase-probability estimate.
   Interpretation: for this exact combination, either the budget is too big
   to beat the cylinder weight, or the deterministic row/core comparison
   already excludes a cover. Stronger or different lower-tail estimates are
   not excluded. Do not continue assuming this combination automatically
   converts the stretched-exponential soft tail into a worst-case bound.

All three source files compile and their oleans are built. Combined audit:
CoreFilteredAudit.lean, /tmp/core_filtered_audit.log. Individual logs:
/tmp/core_filtered_deletion.log, /tmp/core_filtered_selberg.log,
/tmp/filtered_exposure_barrier.log. Audited axioms are only propext,
Classical.choice, Quot.sound. The scratch CheckFilteredExposure.lean contains
some deliberately unresolved #check queries; do not import it.

Spec.lean remains unchanged with its sole original sorry at line2177 and
SHA256 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No purported solution of the original conjecture has been submitted.

## Unconditional full logarithmic saving in the 5/2 bound (VERIFIED)

Original erdos_970 STILL UNSOLVED. Reviewed first-hit kernels with individual
prime cutoffs and the exact ordinary-coefficient objective. No family with
sum(mean + cost) < m uniformly at m=C*k^2 was found. In particular, the
existing first-hit criteria must not be invoked without proving that premise.

A logarithmic factor discarded in the old hard-cubic bound was instead
recovered. The new strongest unrestricted verified estimate in this development
is now
  h(k) <= C*k^(5/2)/log(k+2), k>0,
with an absolute C>0. It still does NOT imply h(k)<=C'*k^2.

1. HardCubicLogPrimeBound.lean
   Imports HardCubicPrimeBound for the existing constants and ingredients.
   prime_survivor_three_quarters_log: for |P|<=t^4, t>0, every residue
   configuration has a survivor whenever
     hardCubicBoundConstant*t^10 < m*log(hardCubicCutoffScale*t^3).
   The existing energy lower bound is L^7 and coefficient cost squared is
   <=100000000*exp(4)*R^2*L^6. The proof retains the resulting factor L:
     L*cost^2 <=100000000*exp(4)*R^2*energy.
   It does not replace L^6 by L^7 as the old proof did. All existing tail
   and error hypotheses are still discharged explicitly.

2. HardCubicLogPowerBound.lean
   - isJacobsthalBound_three_quarters_log transfers the new interval criterion.
   - cardinality_log_le_scale_log: for k<=t^4,
       log(k+2)<=2*log(hardCubicCutoffScale*t^3).
   - jacobsthal_mul_scale_log uses exact natural floor rounding at
       m=floor(hardCubicBoundConstant*t^10/L)+1,
     proving h(k)*L<=hardCubicBoundConstant*t^10+L.
   - jacobsthal_mul_log_envelope uses the harmless upper bound
       L<=hardCubicCutoffScale*t^10
     to absorb that rounding error into an absolute constant.
   - fourth_envelope_tenth_le: t^4<=16*k implies t^10<=1024*k^(5/2).
   - logFiveHalvesConstant :=
       2048*(hardCubicBoundConstant+hardCubicCutoffScale), positive.
   - jacobsthalFunction_mul_log_le_five_halves:
       h(k)*log(k+2)<=logFiveHalvesConstant*k^(5/2), k>0.
   - exists_five_halves_div_log_bound is the existential quotient form.

Both files compile, oleans built, and all audited axioms are only propext,
Classical.choice, Quot.sound. Audit: HardCubicLogAudit.lean.
Logs: /tmp/hard_cubic_log_prime_bound.log,
/tmp/hard_cubic_log_power_bound.log, /tmp/hard_cubic_log_audit.log.
No numerical search or unverified analytic input is used in these results.

Spec.lean is unchanged, with its original sole sorry at line2177. No proof or
exact negation of erdos_970 has been obtained or submitted.

## Additional global-coefficient diagnostic (no conjecture progress)

Original erdos_970 STILL UNSOLVED. No Lean source was changed in this round.
The strongest verified unrestricted bound is still the logarithmically improved
5/2 bound in HardCubicLogPowerBound.lean.

Re-read FirstHitDisjointCost and BooleanCoupledDuality before testing the global
coverage-polynomial class. The existing theorem already proves that coefficients
from different first-hit indices have disjoint monomial supports, so merging
cannot create a cross-index saving. Earlier global-versus-first-hit strict gaps
were for non-prime marginals; they are not uniform prime-class certificates.

New DIAGNOSTIC scripts (not imported by Lean):
- /tmp/global_moment_adaptive.py
- /tmp/global_moment_divisor_support.py

At the first 14 primes, the floating recursive threshold (exact root-mass
convention, no constant coefficient error) is 738.3717129824363.
An adaptive full-moment relaxation was limited to180 seconds. It ended after
21 completed solves and a time-limited22nd solve. The final completed restricted
solve still had9 violated omitted moments. Therefore that adaptive run by itself
is NOT a complete feasibility certificate. Log:
  /tmp/global_moment_adaptive_14.log.

A separate divisor-supported population problem at the same 14 primes used
only nonempty patterns with prime product<=544644. Its2605 pattern variables
and61179 nonzero containment incidences solved in~0.42s. The numerical threshold
was738.3717129824321, agreeing with the recursive threshold. A zeta transform
then checked ALL16384 intersection moments, not only the selected constraints.
This is finite numerical evidence, NOT a theorem of universal optimality or an
asymptotic method obstruction. Log and data:
  /tmp/global_moment_divisor_support_14.log
  /tmp/global_moment_divisor_support_14_544644.npz.

The142 positive atom masses were also rounded to denominator10^12 and normalized.
At the slightly smaller total mass738, Python exact integer arithmetic checked
all16384 inequalities
  738*abs(d_T*momentNumerator(T)-totalNumerator)
    <= d_T*totalNumerator,
as well as nonnegativity, zero empty-atom mass, and exact total mass. Data:
  /tmp/global_moment_divisor_support_14_exact.json.
This exact calculation has NOT been transferred to Lean. It is a synthetic
population, NOT an actual cover of738 consecutive integers. It is NOT the
negation of erdos_970 and must not be submitted as such.

Both diagnostics have ended; no worker remains active. Spec.lean is unchanged,
with its sole original sorry at2177. No proof or exact negation was obtained.

## Gap-based prime caps for optimal cores (VERIFIED)

Original erdos_970 STILL UNSOLVED. The strongest unrestricted bound remains
h(k)<=C*k^(5/2)/log(k+2). No numerical search was used in this round.

New file OptimalCoreGapCap.lean compiles; olean built. Namespace
Erdos970.OptimalCoverCore. The argument refines the old p<m cap by using a gap
bound g for the core after deleting p and the final survivor count S.

- interval_length_le_gap_mul_survivor_card: if every Q-survivor in (a,a+L)
  is also a P-survivor, a+L<=m, and Q has uniform gap bound g, then
      L<=g*(|survivors(m,P,r)|+1).
  If not, choose one Q-survivor in each of S+1 disjoint g-blocks inside
  that open interval. The block positions are injective final survivors.
- prime_le_gap_mul_survivor_card: two private positions of p give an open
  p-interval in which every old survivor avoids p, hence p<=g*(S+1).
- used_prime_le_gap_mul_survivor_card supplies the two-private-point premise
  from global optimality, including the secondary minimization of core size.
- two_mul_prime_le_gap_mul_survivor_card and
  two_mul_used_prime_le_gap_mul_survivor_card: when 2 remains in the core and
  p is odd, same-parity p-hits are at least2p apart, giving 2p<=g*(S+1).
- primeSetBound_jacobsthal_card supplies a gap bound using the original
  jacobsthalFunction definition, via its already-proved finite infimum property.
- used_prime_le_previous_jacobsthal:
      p<=h(|P|-1)*(S+1).
- two_mul_used_prime_le_previous_jacobsthal is the parity refinement.
- Their _of_full_cover versions give p<=h(|P|-1), respectively
  2p<=h(|P|-1), when the optimal core itself has no remaining survivors.

Scope: these assertions concern the globally optimal cost-and-core-size
configuration, or explicitly assume two private points. They do NOT assert
that every arbitrary cover has two private points per class. No assertion
that an optimal core always has S=0 or contains2 was made. The resulting
caps alone do not close a quadratic induction: the old gap estimate and the
factor S+1 remain. No uniform prime cap O(k*log k) was established.

Audit: OptimalCoreGapCapAudit.lean, /tmp/optimal_core_gap_cap_audit.log.
Compilation log: /tmp/optimal_core_gap_cap.log. All audited axioms are only
propext, Classical.choice, Quot.sound.
Spec.lean remains unchanged, with its original sorry at2177. No proof or
exact negation of erdos_970 has been obtained or submitted.

## Optimal-core and soft-endpoint continuation (no settlement)

The original erdos_970 is STILL UNSOLVED. No Lean theorem was added in this
continuation. Reviewed OptimalCoverCore, OptimalCoreExchange,
OptimalCoreGapCap, ParityReduction, IncrementReduction, the radial/support
barriers, and the existing void-tail reductions.

Global optimality has not supplied a lower bound for the final survivor count
that closes a quadratic estimate. In particular, no assertion that optimal
positive-length cores always leave a survivor was proved. Even positivity
alone would not close the gap: the gap-cap argument still involves the
smaller-cardinality Jacobsthal bound and the factor S+1. Two-private-point
and local-exchange properties remain insufficient substitutes for global
optimality or for a quantitative count estimate.

Revisited the weaker soft endpoint hypothesis
  E[Y_0 * z^S_m] >= c * density(P) * E[z^S_m]
with fixed 0<z<1 and a fixed c>0. This is not the previously refuted c=1
candidate. Uniform iteration would yield an exponential void bound and hence
the conjecture via the existing reduction. No such positive constant was
established. The verified pair variance, adjacent-block covariance, and soft
exposure inequalities do not imply this tilted estimate. No independence or
unproved tilted association was assumed.

No numerical search or computational worker was launched. Spec.lean remains
unchanged with its original theorem and sole sorry; no purported proof or
negation of the conjecture was submitted.

## Exact common-kernel Boolean tail cost (VERIFIED)

Original erdos_970 STILL UNSOLVED. No stronger unrestricted growth estimate or
superquadratic cover was obtained. Spec.lean is unchanged.

New file Submission/CommonKernelBooleanCost.lean compiles, with a built olean.
Namespace Erdos970.FiniteSelberg. Audited final axioms are only propext,
Classical.choice, Quot.sound. Log: /tmp/common_kernel_boolean_cost.log.

This resolves an algebraic question about the existing common lower kernel:
for a Boolean polynomial g supported on core coordinates A, write b for the
fully Boolean-reduced coefficients of g^2 and c for those of
  (1 - sum_(i in A) X_i) g^2.
For disjoint tail B, the coefficients of
  (1 - sum_(i in A union B) X_i) g^2
have EXACT L1 norm
  ||c||_1 + |B| * ||b||_1.
Every tail monomial contains its own unique tail variable and no other tail
variable. Its support is disjoint from every other tail contribution and
from the entire core contribution. Thus merging cannot cancel this factor.

Results:
- CoeffSupportedOn and support preservation for ordinaryCoefficient and
  booleanSquareCoefficient.
- tail_hitShift_disjoint, core_tail_abs_identity, core_tail_merged_cost.
- booleanHitCoefficient (handles coordinates already in a monomial),
  booleanHit_expansion, booleanLowerCoefficient, booleanLower_expansion.
- common_lower_boolean_cost, tail_card_mul_booleanSquareCost_le.
- common_lower_expansion links the exact coefficients to the existing
  orthogonal Selberg lower kernel and its kernelEnergy.
- arbitrary_lowerKernel_boolean_error and common_lower_error_core_tail.
- survivor_of_kernelEnergy_boolean_cost is a sufficient criterion, with its
  main-term-versus-cost inequality explicitly retained as a hypothesis.
- nonemptyCoeffCost omits the empty monomial, whose interval error is zero.
- common_lower_nonempty_cost and
  tail_card_mul_booleanSquareCost_le_nonempty prove the same exact tail factor
  survives this legitimate constant-coefficient improvement.
- boolean_polynomial_interval_error_nonempty and
  arbitrary_lowerKernel_nonempty_boolean_error rigorously remove that charge.

CRITICAL SCOPE: This is about the coefficient norm used in a termwise unit-
error estimate. It does NOT show that actual interval discrepancies attain
that norm, that compatible CRT remainders may be chosen independently, or
that every common kernel or every sieve method fails at quadratic scale.
Boolean merging can still reduce the square norm itself and the core cost.
No universal quadratic main-term inequality was established here.

Reviewed the existing first-hit cost and recurrence diagnostics before this
formalization. Did not rerun the already completed million-prime diagnostic
or infer an asymptotic impossibility theorem from it. No numerical optimizer
or counterexample-search worker was launched. No proof of erdos_970 or of its
exact negation was submitted.

## Adjacent-gap continuation after Boolean cost audit (no settlement)

Original erdos_970 STILL UNSOLVED. Revisited TwoSurvivorReduction,
IncrementCountConsequences, GapReduction, the parity reduction, and the
SymmetricIsolation counterexample. No new Lean theorem was obtained.

The global adjacent-gap estimate remains unproved. The existing isolation
construction forbids replacing it with a pointwise claim that every survivor
has another survivor at distance O(|P|). Reflection about the lone survivor
only exchanges its two adjacent gaps; it does not, without an additional
argument, produce a covered interval whose length is their sum minus O(|P|).
No residue-reassignment or deletion argument establishing such a global
comparison was found. The exact large-new-prime/two-survivor equivalence is
still a reduction, not a proof of the necessary two-survivor estimate.

No numerical scan was launched, no helper assumption was introduced, and
Spec.lean was not changed. The verified CommonKernelBooleanCost results from
the preceding entry remain available, but no proof or exact negation of the
original quadratic conjecture has been obtained or submitted.

## Cardinality-scaling review (no new theorem)

Original erdos_970 STILL UNSOLVED. Reviewed CardinalityBootstrap,
CardinalityBlockBootstrap, Bootstrap, the logarithmically improved 5/2 bound,
and the previously recorded tensor-amplification limitation. No new Lean
source was added or altered in this continuation.

Neither monotonicity nor a polynomial growth estimate supplies a doubling or
multiplicative law for the Jacobsthal function. A relation such as
h(2*k)<=4*h(k) would be an additional substantive hypothesis, not a consequence
of the available estimates. No such relation was proved. Likewise, composing
covers on a product digit grid does not automatically give one residue class
for each of a controlled number of distinct primes on a consecutive interval.
No valid cover amplification resolving that issue was found.

The existing smaller-cardinality count lemmas retain their explicit bound
hypotheses and do not establish a terminal quadratic induction step. No
unproved scaling assertion was introduced as a lemma or axiom. Spec.lean is
unchanged, with its original erdos_970 statement and sole sorry. No proof or
exact negation of the original conjecture was obtained or submitted.

## Unique residue-preserving greedy encodings at unbounded length/budget (VERIFIED)

Original erdos_970 STILL UNSOLVED. New file UniqueGreedyCoverOrder.lean
compiles with built olean; all printed axioms are only propext,
Classical.choice, Quot.sound. Log: /tmp/unique_greedy_cover_order.log.
Namespace Erdos970.GreedyCoverOrder. No numerical search was used.

Definitions and general results:
- Encodes U P r l: a nodup list with prime set P, empty greedy residual,
  and agreement with every original residue modulo its prime.
- pairwise_residues_of_private_representatives: if each r(p) is normalized
  (r(p)<p), belongs to U, and is private to p, every agreeing greedy order
  has strictly increasing r-values. At a step, the selected residue is at
  most the first remaining position, while every unused private
  representative is still present.
- encodings_unique_of_private_representatives: consequently two such
  encodings must be the same list.

Explicit unbounded family:
For m>=2 use every prime p<=m with r(p)=p-1, and a fresh prime q>m with
r(q)=0. Position0 is covered by q; every positive i<m is covered by a prime
factor of i+1. The representative p-1 is private to p, because any other old
prime dividing (p-1)+1=p must equal p; the fresh q cannot hit it. Conversely,
0 is private to q. Thus the cover is essential and has a unique agreeing
order (fresh q first, then the old primes in increasing order).
- exists_unique_order_cover: cardinality exactly primeCounting(m)+1,
  essential cover of range m, and existence of exactly one Encodes list.
- arbitrarily_long_unique_order_covers: for all A,K there are such covers
  with |P|>=K and m>A*|P|. Uses the already proved elementary limit
  primeCounting(m)/m ->0 through SymmetricIsolation.eventually_small_budget.
- no_linear_length_order_multiplicity: no fixed length/budget threshold,
  even after excluding finitely many budgets, forces two distinct
  residue-preserving greedy encodings of every essential cover.

CRITICAL SCOPE: This is a limitation of a blanket order-multiplicity claim,
not of all entropy methods. It does not assert uniqueness among orders that
produce OTHER residue configurations. The prime classes in this family may
have only one private point; global budget optimality is not asserted. The
construction does not have an unbounded m/|P|^2 ratio and does NOT refute
Erdos970 or a multiplicity estimate restricted to quadratic-length covers.
No adequate quadratic-scale multiplicity/concentration estimate was proved.

CheckUniqueOrder.lean is a scratch API query file, with no failing queries;
it is not imported by the proof. Spec.lean is unchanged, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9,
with its original sole sorry at2177. No proof or exact negation of erdos_970
has been obtained or submitted.

## Sorted increasing-anchor assertion disproved (VERIFIED)

Original erdos_970 STILL UNSOLVED. New file SortedGreedyAnchorObstruction.lean
compiles, with a built olean. The kernel-checked finite certificate uses
range 52 and the prime prefix
[2,3,5,7,13,17,19,23,29,31,37,41,43].
Its first remaining position is exactly 51, although the next prime in the
strictly increasing order is 47. Thus increasing the primes does not ensure
that the next first-uncovered anchor is below its prime.

The finite certificate uses decide +kernel, not native_decide; printed axioms
of exists_sorted_anchor_above_prime are only propext, Classical.choice,
Quot.sound. Log: /tmp/sorted_anchor_lean.log. This strengthens the prior exact
Python diagnostic to a Lean-checked statement. It is NOT a counterexample to
erdos_970, nor to an amortized estimate on anchors.

Reviewed the hard-cubic bound and the exact common-tail coefficient cost.
The existing argument retains error on the scale k*R^2, with its positive
energy certificate at R on the scale k^(3/4). The logarithmic saving gives
O(k^(5/2)/log(k+2)), not O(k^2). No justified removal of the tail cost or
replacement interval-remainder estimate was found. No new quantitative
hypothesis has been treated as a theorem. No additional numerical search
was run in this continuation.

Spec.lean remains unchanged, with its sole sorry in the original erdos_970.
No complete proof or exact negation of that statement has been obtained.

## Further integrality review (no new theorem or settlement)

Original erdos_970 STILL UNSOLVED. Reviewed MixedPatternMomentExample,
MixedPatternRescaling, the rounded-moment diagnostics, and the exact common
kernel/support barriers. The already proved six-point INTEGER synthetic
model obeys every rounded intersection bound but is not an actual interval
sieve. Thus integer atom counts do not alone recover CRT phase consistency.

One bounded restricted MILP feasibility test was performed, followed by its
continuous relaxation to interpret the outcome. Parameters: first14 primes,
mass600, nonempty pattern support restricted to prime products<=544644,
2605 variables and63784 matrix entries. All constrained moments used exact
integer floor/ceiling bounds; the solver was floating-point HiGHS. The integer
model was reported infeasible in0.64s; the continuous relaxation was ALSO
reported infeasible in0.055s. Therefore this test found NO integrality gain,
NO full-support infeasibility certificate, and NO interval-cover information.
No conclusion is inferred beyond these restricted diagnostic outcomes.

Scripts: /tmp/integer_moment_check.py, /tmp/fractional_moment_check.py.
Integer log: /tmp/integer_moment_check.log. No witness was produced; no new
Lean certificate or new universal inequality resulted. Worker PID115809
finished (only a defunct process entry remained when checked).

Spec.lean is unchanged. Neither the original conjecture nor its exact
negation has been proved. No completed proof has been submitted.

## Interval-recurrence continuation (no new theorem or settlement)

Original erdos_970 STILL UNSOLVED. Revisited the raw integer recurrence,
closed integer hulls, quantum reference transfer, smaller-cardinality
bootstrap, and common-phase row rescaling. No new numerical search was run.

The integer recurrence and closed-hull soundness theorems apply to actual
specified prime sequences; neither supplies uniform positivity at C*k^2.
The continuous/quantum reference constructions have proved arbitrary-prime
transfer, but retain their unproved uniform-positive-envelope premise.
Existing first-prime diagnostics are not evidence of a bounded asymptotic
ratio: for example the raw interval run at one million primes was still zero
at length4*k^2. This is not an asymptotic impossibility theorem either.

The smaller-cardinality injection excludes the terminal cardinality. Its
use at that terminal stage would be circular. The fixed-cost redundancy
lemma does not assert redundancy when recursive child costs also change.
The exact common-phase row identities do not supply a bound on simultaneous
vanishing. The earlier uniform rectangular variance-cube disproof concerns
its stated n>=p domain; it must not silently be treated as a disproof for
all other aspect ratios or restricted phase families.

No missing positivity or row-coupling estimate was established. No new Lean
proof file was produced. Spec.lean remains unchanged with its original sole
sorry; neither erdos_970 nor its exact negation has been proved.

## Soft endpoint-to-void reduction (VERIFIED, CONDITIONAL)

Original erdos_970 STILL UNSOLVED. New file SoftEndpointReduction.lean
compiles, with built olean. All printed axioms are only propext,
Classical.choice, Quot.sound. Log: /tmp/soft_endpoint_reduction.log.
Namespace Erdos970.GapAverages. No new numerical search was run.

Definitions:
- countLaplace(P,t,m)=E[exp(-t*S_m)].
- endpointLaplace(P,t,m)=E[Y_m*exp(-t*S_m)].
- SoftEndpointBound(c,t) is the EXPLICIT UNPROVED hypothesis that the second
  quantity is at least c*density(P) times the first, for every prime set and
  interval length. It is not introduced as an axiom or claimed unconditionally.

Proved results:
- countLaplace_succ: exact F_(m+1)=F_m-(1-exp(-t))*G_m, using Y_m in{0,1}.
- countLaplace_le_of_softEndpoint: for t>=0, the hypothesis gives
    F_m<=exp(-c*(1-exp(-t))*m*density(P)).
- coveredFraction_le_countLaplace.
- exponential_void_of_softEndpoint: resulting ExponentialVoidBound with
  the EXACT constant c*(1-exp(-t)). No adjacent-window independence is used.
- quadratic_bound_of_softEndpoint: c>0 and t>0 and the SAME UNPROVED
  hypothesis imply the original quadratic conclusion, via the prior valid
  ExponentialVoidReduction. This is a conditional theorem, not erdos_970.
- softEndpoint_constant_le_one: even P=empty forces c<=1.
- phase_term_le_countLaplace and count_lower_of_softEndpoint: the same
  hypothesis forces, for EACH individual phase r,
    c*(1-exp(-t))*m*density(P) <= t*S_m(r)+sum_(p in P)log p.
  Thus the endpoint proposal entails a deterministic positive-density count
  estimate after paying phase entropy; it is substantially stronger than the
  already proved variance estimate.
- softEndpoint_zero_parameter_iff: SoftEndpointBound(c,0) iff c<=1.
  This trivial zero-parameter case cannot be used in the quadratic reduction,
  where t>0 is essential.

No uniform positive c at a positive t was proved. The earlier on-paper
obstruction to c=1 must not be ignored; the new conditional theorem does not
repair that false exact-density candidate. No proof or exact negation of
erdos_970 has been obtained. Spec.lean remains unchanged with its sole sorry.

## Flexible hard-cubic cutoff (VERIFIED, UNCONDITIONAL PARTIAL BOUND)

Original erdos_970 STILL UNSOLVED. The following new files compile, have
built oleans, and print only propext, Classical.choice, Quot.sound:
- HardCubicFlexibleTail.lean (83 lines)
- HardCubicFlexiblePrimeBound.lean (144 lines)
- HardCubicFlexiblePowerBound.lean (172 lines)
Logs: /tmp/hard_cubic_flexible_{tail,prime,power}.log.

The exact logarithmic certificate
  log(200000/149999) <= 287697/1000000
uses log(4/3)<=28769/100000 and log(150000/149999)<=1/149999.
With two tail errors of at most 10^-6, it still fits the old 2877/10000
reciprocal-tail budget. No new cubic energy or coefficient estimate is needed.

Generic tail_power_ratio accepts 0<e<=f, P.card<=t^f and sufficiently large
D, proving sum_(p>D*t^e)1/p<=2877/10000 under that log(f/e) bound.
prime_survivor_power_ratio_log then gives a survivor whenever
  hardCubicBoundConstant*t^(f+2*e) < m*log(hardCubicCutoffScale*t^e).
For f<=2*e, the root envelope k<=t^f<=2^f*k transfers this to a power/log
bound. Taking e=149999,f=200000 proves
  Erdos970.exists_below_five_halves_div_log_bound :
    exists C>0, forall k>0,
      jacobsthalFunction k <= C*k^(249999/100000)/log(k+2).
The exponent is exactly 2.49999, strictly below 5/2 but still above 2.
The huge generic constant is symbolic; no evaluation of 2^499998 is needed.

This is NOT an iterative route to exponent two. A diagnostic evaluation of
the fixed cubic gives its limiting exponent about 2.499884227576454; this
number is not a new formal optimality theorem. The existing verified
hardCubic_not_quadratic_threshold already rules out the quadratic threshold
for this fixed profile. No proof or exact negation of erdos_970 was obtained.
Spec.lean remains unchanged with its original sole sorry.

## Simultaneous two-cover CRT constraint (VERIFIED, PARTIAL)

Original erdos_970 STILL UNSOLVED. New file CoverPhasePacking.lean compiles,
with built olean and only propext, Classical.choice, Quot.sound in all
printed axiom audits. Log: /tmp/cover_phase_packing.log.
Namespace Erdos970.CoverPhasePacking.

- card_le_offDiag_of_two_covers: if U is contained in [0,m), two residue
  vectors both cover U using the same distinct prime set D, their residues
  disagree modulo every p in D, and p*q>=m for every distinct p,q in D,
  then |U|<=|D|*(|D|-1). Each x chooses a prime from each cover; these primes
  must differ. CRT and the interval length make the map to ordered distinct
  prime pairs injective. No independence of phase coordinates is used.
- differing(P,r,s): the primes in P on which r and s differ modulo p.
- common_survivors_eq: both phases have exactly the same survivor set for
  the retained common core P\differing(P,r,s).
- common_core_card_le: for two full covers of [0,m), that common survivor
  set has size at most j*(j-1), j=|differing(P,r,s)|, under the pair-product
  condition on just the differing primes.

Scope: this does not give a lower bound for the common-core survivor count.
The current unrestricted count bounds cannot supply the missing lower
bound at quadratic length for an arbitrary near-full common core. A code
or packing interpretation of the result does not itself exclude a single
covering phase. No quadratic theorem, soft-endpoint estimate, or negation
of erdos_970 follows from this constraint as presently proved.

CheckCoverPhasePacking.lean is a scratch #check file with intentionally
unresolved library names; it must not be imported. An intermediate failed
compile of the proof file printed sorryAx, but the final successful compile
and built olean have only the permitted axioms.

Spec.lean is unchanged with the original theorem and sole sorry. No proof
or exact negation of the target has been obtained or submitted.

## Deterministic separated-prime collision variance (VERIFIED, PARTIAL)

Original erdos_970 STILL UNSOLVED. New file SeparatedCollisionVariance.lean
compiles and has a built olean. All final printed axioms are only propext,
Classical.choice, Quot.sound. Log: /tmp/separated_collision_variance.log.
Namespace Erdos970.Resampling.

For a FIXED arbitrary S subset [0,m), distinct prime set P, and the explicit
separation premise p*q>=m for distinct p,q in P:
- separated_equal_residues_card_le_one: each distinct x,y in S can agree
  modulo at most one prime in P, by CRT and x,y<m.
- classHits_square_sum: exact second moment as an ordered-pair collision sum.
- separated_collision_sum_le: sum_p sum_a N_(p,a)^2 <= s*(k+s-1),
  where s=|S| and k=|P|.
- prime_mul_classVariance: exact identity
    p*V_p = sum_a N_(p,a)^2 - s^2/p.
- separated_weighted_variance_sum_le:
    sum_p p*V_p <= s*(k+s-1)-s^2*rho, rho=sum_p 1/p.
- separated_variance_sum_le: for y>0 with all p>=y,
    sum_p V_p <= [s*(k+s-1)-s^2*rho]/y.

The actual fixed-population variance has NOT been replaced by its average
over core phases. These are deterministic aggregate bounds, not the earlier
refuted uniform row-variance proposal.

- populationCoveredFraction_separated_bennett inserts this explicit budget
  into the previously proved conditional Bennett bound. The cap B on each
  centered class count is still an explicit hypothesis.
- populationCoveredFraction_separated_optimized optimizes t using ANY positive
  upper budget V for the displayed expression, with rho<=1 and B>0. No
  positivity of the actual variance is assumed or silently used.
- classVariance_single_residue: if every point of S lies in one residue modp,
    V_p = s^2/p*(1-1/p).
  This verifies that a quadratic-in-s term cannot simply be discarded for
  arbitrary populations. It is not an interval-cover counterexample.

No uniform small-core survivor bound or sufficiently strong exceptional-phase
estimate at quadratic length has followed. The separated-tail premise does
not apply to an arbitrary full prime set, and the fixed population S need
not be a uniformly large core-survivor set. These hypotheses must not be
removed when applying the new results. The original critical void bound,
positive soft-endpoint estimate, and unrestricted quadratic conclusion
remain unproved. No proof or exact negation of erdos_970 was submitted.

Spec.lean remains unchanged with its sole original sorry. Failed intermediate
compiles were repaired; the final axiom audit contains no sorryAx.

## Full-support rounded-moment follow-up (INCONCLUSIVE DIAGNOSTIC)

Original erdos_970 STILL UNSOLVED. This continuation reviewed unrestricted
coverage-polynomial certificates, their earlier finite comparisons with
first-hit certificates, and the existing all-mixed-count and quantum interval
results. No new asymptotic estimate or Lean proof was obtained.

One bounded diagnostic removed the artificial pattern-product support cap
from the previous mass-600 test. It used the first 14 primes, all 16383
nonempty Boolean patterns, all exact floor/ceiling intersection constraints,
and total mass 600. The incidence matrix had 4782968 nonzero entries.
Command used the existing /tmp/fractional_moment_check.py with a support cap
larger than the full prime product, integrality zero, and a 90-second limit.
Log: /tmp/full_rounded_moment_14_600.log.

HiGHS returned TIME LIMIT after 90.5767 seconds, with primal status
"At lower/fixed bound". Thus this run established NEITHER feasibility NOR
infeasibility. It produced no witness and no exact or Lean certificate.
No integer solve was launched after this inconclusive continuous relaxation.
PID118264 finished (defunct when last checked). No worker remains active.

No claim of universal first-hit optimality for distinct primes follows from
finite LP agreement. Nor does the quantum threshold ratio observed through
k=1000 establish a bounded asymptotic ratio. No old large recurrence run was
repeated. Spec.lean remains unchanged with its original sole sorry, and no
proof or exact negation of erdos_970 has been obtained or submitted.

## Grid and adjacent-shift encoding review (NO NEW THEOREM)

Original erdos_970 STILL UNSOLVED. No Lean source was added or changed in
this continuation. Revisited interval grids and simultaneous row rescaling.
The common-inverse identities do preserve all row correlations, but no
quantitative simultaneous-row inequality closing the quadratic scale was
proved. Separate universal row estimates reproduce the existing sieve
limitation. No independence of grid rows was assumed.

Also considered adjacent translations of greedy encodings. The simple
finite encoding bound by the number of prime orders is not quadratic.
No useful uniform insertion-position bound or sufficient lower bound on
numbers of greedy orders was established. The existing unique-order
examples still prevent inferring abundant orders merely from a large
length/cardinality ratio. No assertion about unbounded length/cardinality-
squared ratios follows from those examples.

The possible use of trimmed or phase-dependent lower kernels was reviewed
without obtaining a coefficient-cost or arithmetic remainder estimate.
A pointwise cap on a kernel does not by itself bound its Boolean coefficient
cost or its progression discrepancy. No such substitution was used as a
proof step. No numerical experiment or worker was started this round.

Spec.lean remains unchanged with its original theorem and sole sorry.
Neither erdos_970 nor its exact negation has been proved or submitted.

## Smaller-cardinality feedback and translated packing review (NO SETTLEMENT)

Continued the smaller-cardinality bootstrap review. No recursive feedback
estimate closing the quadratic induction was proved. The fixed-subtraction
redundancy theorem was not extended to changing recursive child costs.
In particular, the unrestricted exponent 2.49999 was not treated as a
quadratic induction hypothesis or as an iteratively improving exponent.

Also reviewed applying CoverPhasePacking to a cover and its one-step
translate. Consecutive positions cannot use the same prime, but the
injection into ordered distinct-prime pairs still requires the pair-product
hypothesis. Arbitrary prime covers include small prime pairs, for which
multiple occurrences of the same ordered pair are possible. Counting those
occurrences by their CRT periods gives a reciprocal-product contribution;
no estimate controlling that contribution sufficiently to settle the
unrestricted conjecture was obtained. This is not a limitation theorem for
all translated-cover methods.

No new Lean theorem or numerical diagnostic resulted. Spec.lean remains
unchanged, with its original erdos_970 statement and sole sorry. Neither
the proposition nor its exact negation has been proved. No completed proof
was submitted for verification.

## Critical-rate, quantum, and overlap continuation (NO SETTLEMENT)

Re-read the precise probabilistic sufficient conditions. SoftEndpointBound
with positive constants implies the full ExponentialVoidBound and is stronger
than the already stated sufficient CriticalVoidBound, whose rate is
c*m*log(k+2)/(k+1). No proof of either hypothesis resulted. The unconditional
stretched-exponential low-count estimate was not treated as sufficient to
exclude a single exceptional phase.

Revisited the guarded quantum refinement and its accumulated dilation
comparison. The comparison remains a bound on a multiplicative length factor,
not a quadratic positive-envelope theorem. No new trigger-growth estimate,
stage-independent dilation budget, or uniform positivity theorem was proved.
The diagnostic first-positive values through k=1000 were not extrapolated to
a uniform bound, and no duplicate or larger numerical run was launched.

Inspected whether the exact- and double-cover linear bounds generalize with
useful dependence on maximum overlap multiplicity. Their CRT separation and
selected-pair hypotheses remain indispensable to the existing proofs. No
variable-multiplicity estimate sufficient for arbitrary covers was obtained;
in particular, no automatic bounded-overlap reduction was assumed.

No Lean source was added or changed in this continuation. Spec.lean retains
its original conjecture and sole sorry. Neither erdos_970 nor its negation
has been proved, and no completed proof has been submitted for verification.

## Linear-in-overlap shortcut disproved (VERIFIED AUXILIARY RESULT)

Original erdos_970 STILL UNSOLVED. New compiled file and olean:
Submission/MultiplicityLinearObstruction.lean (namespace
Erdos970.MultiplicityObstruction). It imports FormalConjecturesUtil directly,
not Spec.lean. Log: /tmp/multiplicity_linear_obstruction.log. Final axiom
audits report only propext, Classical.choice, Quot.sound.

Verified results:
- factorial_card_succ_le_prod: for a finite set S of integers >=2,
  (|S|+1)! <= product(S).
- primeFactors_card_le_of_le_factorial: 0<n<=t!, t>0 implies omega(n)<=t.
- log_double_factorial_lower: log((2t)!) >= t*log t for t>0.
- factorial_cover: the primes <=t!, with forbidden residue p-2, cover
  [0,t!-1), corresponding to integers 2,...,t!. The prime budget is pi(t!),
  and pointwise hit multiplicity is <=t.
- exists_cover_gt_card_mul_multiplicity: for every C>0 there is a genuine
  prime-class cover with length > C*(prime count)*(allowed multiplicity).
  Uses the preceding family with t replaced by 2t and the verified Mathlib
  Chebyshev upper bound for pi((2t)!). No numerical search is involved.
- no_uniform_linear_overlap_bound negates the proposed universal estimate
  length <= C*(prime count)*(maximum allowed overlap), even for genuine
  prime-class covers.

CRITICAL SCOPE: this is NOT the negation of erdos_970. The unbounded ratio is
length/(prime count * overlap bound), not length/(prime count)^2. It only
blocks obtaining the target by extending the exact- and double-cover linear
estimates with a constant linear in arbitrary overlap multiplicity.
No other dependence on multiplicity is ruled out by this theorem.

The first compile failed on the final real inequality; the successful proof
uses positivity of F*log F explicitly. Intermediate sorryAx output from the
failed compile is superseded by the clean final build. The source has no
sorry/admit/native_decide. Spec.lean was not changed and retains its original
statement and sole sorry. No completed target proof was submitted.

## Recursive-feedback and conditional-concentration follow-up (NO SETTLEMENT)

Rechecked the precise scope of the old cardinality diagnostics before proposing
another child-feedback test. The earlier interval_bootstrap_compare and
interval_bootstrap_propagated runs already propagate changes through recursive
children and selected/full finite lists of block constraints. They show finite
gains but no closing induction in those runs; they are not asymptotic
impossibility theorems. No duplicate numerical run was launched. No extension
of fixed-cost terminal redundancy to changing child costs was assumed.

Also considered a conditional concentration route after fixing a small-prime
core. Near the square-root cutoff, the currently available uniform core count
and separate bounds for tail residue-class loads do not yield the required
critical entropy exponent. A stronger joint estimate relating small core
counts to unusually large tail loads was not proved. No independence of
survivor positions or substitution of an averaged variance into an exponential
was used as a proof step.

No new Lean source resulted in this follow-up. The previous verified
MultiplicityLinearObstruction auxiliary result remains separate from the
original target. Spec.lean remains unchanged with its sole sorry, and no
proof or exact negation of erdos_970 has been obtained or submitted.

## Stronger count-induction review (NO NEW THEOREM)

Continued examining induction hypotheses stronger than the fresh-prime
single-block count. No quantitative propagation theorem preserving a useful
terminal count at a fixed quadratic length was obtained. Stronger uniform
count bounds at smaller cardinalities were not inserted as unconditional
lemmas, and no terminal-cardinality assumption was used. The review produced
neither a new Lean result nor an asymptotic obstruction theorem.

The original target remains unresolved. Spec.lean is unchanged, and its sole
sorry remains. No completed proof or exact-negation theorem was submitted.

## High-overlap incidence packing (VERIFIED AUXILIARY RESULT)

Original erdos_970 STILL UNSOLVED. New compiled file and olean:
Submission/HighMultiplicityPacking.lean (298 lines), namespace
Erdos970.HighMultiplicityPacking. Imports MultiplicityLinearObstruction,
which imports FormalConjecturesUtil directly; no dependency on Spec.lean.
Log: /tmp/high_multiplicity_packing.log. All final printed axioms are only
propext, Classical.choice, Quot.sound.

Notation: k=|P|, H(x)=number of selected prime classes hitting x, and
U={x<m : B<=H(x)}. Assume any distinct positions share at most t hitting
primes. The finite constant-weight incidence argument proves
  |U|*(B^2-k*t) <= k*(B-t),
with t<=B. Consequently, if B>0, t<=B, and B^2>=2*k*t:
  |U|*B <= 2*k;
  |U|^2*t <= 2*k;
  sum_{x in U} H(x) <= 2*k;
  sum_{x in U} H(x)^2 <= 2*k^2.
These are deterministic statements, not averaged estimates over phases.
The total-hit bound uses a proved two-term union/intersection incidence
inequality; it does not follow merely by multiplying |U| by k.

Actual arithmetic supplies the common-hit hypothesis in two ways:
- common_hits_factorial_bound: if m<=t! and t>0, distinct positions share
  at most t selected primes, because each shared prime divides their nonzero
  difference and the preceding factorial prime-factor bound applies.
- common_hits_separated_bound: if every distinct selected pair satisfies
  m<=p*q, then t=1 suffices, by CRT injectivity inside the interval.

Theorems include incidence_packing, high_positions_packing,
high_positions_factorial_card_mul_le, high_positions_separated_card_mul_le,
high_positions_total_hits_le, and high_positions_square_hits_le.
The exact constants and the threshold hypotheses remain explicit.

CRITICAL SCOPE: this bounds the quadratic hit mass of very high-overlap
positions. It is not a bound on an arbitrary sieve polynomial, its Boolean
coefficient cost, or its CRT remainder. The remaining moderate-overlap
contribution was not controlled sufficiently to close the unrestricted
quadratic argument. No bounded-overlap replacement of a general cover was
assumed, and no independence or nonlinear variance substitution was used.

The initial incidence and arithmetic results compiled immediately. The
extension had one missing `mul_zero` simplification in the k=0 case; the
successful final build and clean audits supersede the intermediate error.
No numerical diagnostic was launched. Spec.lean remains unchanged with its
original theorem and sole sorry. No completed target proof was submitted.

## Triple-cover probe and trimmed overlap reduction (VERIFIED, NO SETTLEMENT)

Original erdos_970 STILL UNSOLVED. Two new files compile with built oleans;
all final printed axioms are only propext, Classical.choice, Quot.sound:
- Submission/TripleCoverQuadratic.lean
- Submission/QuadraticOverlapReduction.lean
Logs: /tmp/triple_cover_quadratic.log and /tmp/quadratic_overlap_reduction.log.
The earlier failed compile output is superseded by the clean builds.

TripleCoverQuadratic (namespace Erdos970.TripleCover):
- probe has value (H-1)*(H-3), where H is the number of hitting prime classes.
- With rho=sum_p 1/p, separating the unique possible prime 2 proves
    sum_p 1/p^2 <= rho/3 + 1/12.
- The probe mean is 3-3*rho+rho^2-sum_p 1/p^2, hence at least 5/36.
- Its displayed coefficient cost is 3+4*k+k^2.
- total_probe_lower holds for every phase, with no cover hypothesis.
- prime_triple_cover_quadratic proves m<=60*k^2 when every position is covered
  and has at most three hits. This extends the previous restricted quadratic
  overlap argument; it is NOT a bound for arbitrary covers.

QuadraticOverlapReduction (namespace Erdos970.QuadraticOverlap):
- moderatePositions consists of positions with 4<=H(x)<B.
- moderateMass is the sum of H(x)^2 over those positions.
- quadratic_probe_pointwise and total_probe_le_split_mass prove the actual
  pointwise/summed comparison for THIS SPECIFIC probe. No estimate for an
  arbitrary polynomial or its coefficient cost is inferred from hit packing.
- If B>0, t<=B, B^2>=2*k*t, and distinct positions share at most t hitting
  primes, high_positions_square_hits_le controls the discarded high part and
  covered_length_le_moderate_mass gives
      m <= 72*k^2 + 8*moderateMass.
- quadratic_of_small_moderate_mass consequently gives m<=144*k^2 under the
  ADDITIONAL premise moderateMass<=m/16.
- covered_length_le_moderate_mass_factorial supplies the shared-hit premise
  from t>0 and m<=t!, using the verified difference/factorial argument.

CRITICAL GAP: no adequate bound for moderateMass on arbitrary long covers was
proved. In particular moderateMass<=m/16 is NOT asserted as a uniform fact.
These deterministic results use neither phase independence nor a phase-average
variance in place of a conditional estimate. The original unrestricted best
bound remains k^(249999/100000)/log(k+2), not quadratic.

The translated-block and general signed-polynomial reviews preceding these
results yielded no additional estimate closing the target. No full-support LP
was rerun and no new numerical cover search or active worker was launched.
Spec.lean remains unchanged, with its original conjecture and sole sorry.
No completed target proof or exact-negation theorem has been submitted.

## Coupled-CRT and optimal-core review (NO NEW TARGET ESTIMATE)

The original erdos_970 remains unsolved. No edit to Spec.lean was made in
this continuation, and no new theorem is claimed here.

Re-examined CoverPhasePacking, SeparatedCollisionVariance, TrianglePacking,
HardCubicRectangularCriterion, OptimalCoverCore, and OptimalCoreExchange.
The two-cover bound retains the actual shared-core survivor population;
its bound by j*(j-1) does not contradict any currently verified lower count
at the required quadratic length. The aggregate collision variance retains
its quadratic-in-population term. Neither bound yields a uniform small
conditional variance. Triangle incompatibility supplies genuine finite
packing cuts but no uniform estimate disposing of the CRT remainder.

The minimum-budget formulation is exact, not an independent bound on that
budget. Unused-prime injectivity and the two-private-point condition are
necessary optimality properties. They do not imply that an improving
exchange exists, or that the surviving population is large. In particular,
an optimal configuration may have an empty surviving population; it is
invalid to apply a nonempty-population argument to every optimal core.

No additional unproved premise was introduced as a theorem, no numerical
scan was launched, and no completed proof was submitted. The strongest
unrestricted verified bound is still the one stated at the top of this log.

## Further transform review (NO SETTLEMENT)

No edit to Spec.lean and no new verified theorem in this continuation.
Reviewed the one-sided transform route and the earlier PGF obstruction
before launching any new finite test. No new test was launched.

The recorded rough-number obstruction also cautions against trying to
prove a uniform tilted-variance bound Var_t(S) <= A*E_t(S), with a fixed A,
for every t>=0. Such a bound would imply
  E[exp(-t*S)] <= exp(-mu*(1-exp(-A*t))/A).
For any fixed A, the rate divided by t tends to mu as t decreases to zero.
The old rough phase has count/mean tending to alpha=e^gamma/2<1 and
log(phase-space size)=o(mu), so a sufficiently small fixed positive t
contradicts that bound along the same family. This observation is an
on-paper implication using the previously recorded asymptotics; it is NOT
a new Lean disproof theorem. A bound at a suitably sub-mean threshold is
not excluded by this argument and remains unproved.

The interval core/tail review again isolates simultaneous near-extremality
of core lower counts and progression upper counts as a potential place for
an arithmetic saving. Neither separate unit-error sieve bounds nor the
existing second-order collision budget proves that saving. No such saving
was silently assumed. The original quadratic conjecture remains unsolved.

## Variable-cutoff first-hit normalizer estimates (VERIFIED INGREDIENTS ONLY)

The original erdos_970 is STILL UNSOLVED. Spec.lean is unchanged.
Four new files were compiled in the preceding continuation, with final printed
axioms restricted to propext, Classical.choice, and Quot.sound:
- EulerMassLogUpper.lean: an elementary p-series comparison and fifth-order
  exponential polynomial prove E({p<=R}) <= (19/10)*log R eventually.
- SmoothNormalizerLower.lean: for 1<=u<=3, log N=u*log R, and log R>=1,
  G_{<=R}(N) >= (2*u-1-u*log u)*log R - 12*(boundConstant+1).
- NormalizerRankin.lean: the squarefree-divisor exponential moment gives
  E(P)-G_P(N) <= E(P)*exp(sum_p (exp(t*log p)-1)/p-t*log N).
- PrimeExponentialMoment.lean: when log R>=50*sharpMomentError,
  E_{<=R}-G_{<=R}(N) <= E_{<=R}*exp(9/2-2*u), and this exponential
  is <= (1/4)*exp(-2*(u-3)).
These exponential moments are for divisor measures, NOT interval survivor
counts or phase-count Laplace transforms.

Prospective first-hit plan: use R_p approximately sqrt(D/p). The normalizer
estimates above, together with the existing eventual E>=1.5*log p, suggest
positive main-term margin for D=z^(12/5). The sufficient finite integral
certificate is integral_{7/10}^3 1/g(u) du <=17/10, where g(u)=u below 1
and g(u)=2*u-1-u*log u on [1,3]. An external quadrature gave approximately
1.69438, and a 10-piece trapezoid approximately 1.69780; these numbers are
NOT Lean theorems. The prospective margin is 70/19-2*(17/10)-2/9>0.

Remaining gaps include strict-prefix removal, cutoff floors, a rigorous
finite integral certificate, the global prime-summed main-term estimate,
total coefficient cost, and transfer to arbitrary prime sets. Even a completed
2.4-ish exponent would not settle the requested quadratic conjecture.
The strongest unrestricted verified bound remains exponent 249999/100000
with division by log(k+2). No target proof has been submitted.

## Strict-prefix reciprocal tails (VERIFIED)

New file Submission/NormalizerPrefix.lean compiles; final printed axioms
are only propext, Classical.choice, Quot.sound. Log /tmp/normalizer_prefix.log.
- normalizer_strict_prefix_ge: G_{<p}(N)>=(1-1/p)*G_{<=p}(N).
- normalizer_strict_prefix_tail: removing p cannot worsen the relative tail.
- strict_normalizer_lower_through_cube: the prior lower profile for 1<=u<=3
  transfers to primes <p with an additional absolute error of only 3.
- strict_normalizer_reciprocal_rankin: for u>=3 and the explicit log threshold,
  G_{<p}(N)>0 and 1/G_{<p}(N)-1/E_{<p} <= exp(-2*(u-3))/(3*E_{<p}).
- eulerMass_strict_prefix_ge_three_halves: the existing additive padding
  absorbs removal of p and gives E_{<p}>=1.5*log p under its log threshold.
- strict_normalizer_reciprocal_log_tail: combines these to bound the reciprocal
  excess by 2*exp(-2*(u-3))/(9*log p).
No Jacobsthal exponent improvement or settlement is claimed. Spec.lean and
its sole sorry are unchanged.

## First-hit finite integral certificate (VERIFIED)

New file Submission/FirstHitIntegral.lean compiles with a built olean.
Final printed axioms are only propext, Classical.choice, Quot.sound.
Log: /tmp/first_hit_integral.log. The file supplies:
- firstHitProfile(u)=2*u-1-u*log u, concave and positive on [1,3].
- firstHitReciprocal=1/firstHitProfile is convex and continuous there.
- convex_integral_le_chord: a general trapezoidal upper bound, proved by
  integrating the defining convexity inequality.
- firstHitReciprocal_grid_bound: 21 rational endpoint bounds, with logarithms
  certified using sum_range_sub_log_div_le and 12 terms, NOT floating point.
- firstHitReciprocal_integral_le: integral_1^3 firstHitReciprocal <=67/50.
- log_ten_sevenths_le: log(10/7)<=9/25.
- firstHit_integral_budget: log(10/7)+integral_1^3 firstHitReciprocal<=17/10.
- firstHit_analytic_margin_pos: 70/19-2*(17/10)-2/9>0.
The 20-piece rational trapezoid sum is exactly 13385667/10000000.
The exploratory CheckFirstHitIntegral.lean contains API queries and unknown
identifier errors; it is not imported by verified results.

The former numerical integral gap is now closed. Still missing are a global
prime-summed estimate with floors and errors, coefficient cost, and reference
certificate transfer. This does not prove an improved Jacobsthal exponent,
much less the original quadratic conjecture. Spec.lean remains unchanged.

## Further first-hit assembly idea (NOT YET FORMALIZED)

An alternative to integrating the infinite Rankin tail may simplify the next
step. These observations are on paper only, not new Lean theorems:
- Improve exp(-3/2)<=1/4 to exp(-3/2)<=9/40. Six nonnegative Taylor terms
  at 3/2 give exp(3/2)>=40/9.
- Then the strict-prefix reciprocal excess for u>=3 is at most
  (6/31)*exp(-2*(u-3))/log p, using E_{<p}>=1.5*log p.
- For u>=3, exp(-2*(u-3))<=(3/u)^6, by log(u/3)<=u/3-1.
  Write L=log D and u=(L/log p-1)/2. For p<=D^(1/7),
  (3/u)^6 <= (7*log p/L)^6.
- The existing sharp fifth log moment then bounds L times the early-prime
  excess sum by 42/155+o(1). The leading residual
    70/19 - 2*(17/10) - 42/155
  is still positive (about .01324). This could replace the infinite-tail
  integral by one already-verified prime moment.
- The first-hit integer cutoff can be CEIL(sqrt(D/p)), rather than floor:
  the coefficient cost grows by at most factor 4 when sqrt(D/p)>=1, while
  its logarithm is >=the target and differs by at most log 2. This makes
  the Rankin direction favorable. On target ratios 1<=u<=3, ceiling stays
  <=p^3; the smooth-profile logarithmic perturbation is an absolute error.
- For the medium prime sum, the 20 certified trapezoid chords on [1,3],
  plus three exact reciprocal chords on [.7,1], give a fully rational
  piecewise-affine upper profile with integral <1.7. Under u=(L/log p-1)/2,
  each chord can be summed using prime sums of 1/(p log p) and 1/(p log^2 p).
  Partial summation of weighted Mertens should give their leading terms
  with O(1/L^2) errors on each of the finitely many fixed logarithmic bins.
- A fixed finite initial wheel still has to be treated exactly, rather than
  applying eventual logarithmic threshold hypotheses to all small primes.

None of this assembles a reference certificate yet. Nor does its prospective
exponent 12/5 reach the task's target exponent 2. The original conjecture is
still unsolved and the submission file still has its original sole sorry.

## Early-prime sum and inverse logarithmic moments (VERIFIED)

Three new files compile with built oleans and final printed axioms only
propext, Classical.choice, Quot.sound:
- FirstHitEarlyTail.lean (log /tmp/first_hit_early_tail.log): exp(-3/2)<=9/40,
  the sharper reciprocal excess <=6*exp(-2*(u-3))/(31*log p), and a sixth
  power majorant for this exponential tail. first_hit_early_sum_bound proves
  the full early-prime sum <=42/(155*L)+588*sharpMomentError/(31*L^2),
  with explicit prime/log/cutoff hypotheses. The fixed initial wheel is
  not covered by the eventual-threshold hypotheses and must be treated separately.
- PrimeInverseLogMoments.lean (log /tmp/prime_inverse_log_moments.log):
  inverseLogPrimeInterval n a b sums 1/(p*log(p)^(n+1)) over a<p<=b.
  For a>=2 and b>=a, its difference from
    (log(a)^(-(n+1))-log(b)^(-(n+1)))/(n+1)
  has absolute value <=2*(boundConstant+1)/log(a)^(n+2).
  The theorem is generic in n; it includes both moments needed for affine chords.
- PrimeAffineRatio.lean (log /tmp/prime_affine_ratio.log): on the prime bin
  exp(L/(2*b+1))<p<=exp(L/(2*a+1)), the sum of
  (A+B*((L/log p-1)/2))/(p*log p) has main term
    (b-a)*(2*A+B*(a+b))/L
  and error at most (boundConstant+1)/L^2 times
    2*|A-B/2|*(2*b+1)^2 + |B|*(2*b+1)^3.
  All sign and endpoint hypotheses are displayed in the theorem.

These close additional analytic ingredients, not the global first-hit sieve
or the original conjecture. Spec.lean and its original sole sorry are unchanged.

## Integer cutoffs and actual medium-prime sum (VERIFIED)

Three further files compile with built oleans and clean final axiom audits:
- FirstHitIntegerCutoff.lean: firstHitCutoff L p=ceil(exp((L-log p)/2)).
  It is positive; its logarithm is between the target and target+log 2
  when L>=log p; its square is <=4*exp L/p. The full normalizer profile
  (u below 1, 2u-1-u log u above 1) survives this ceiling with an explicit
  constant error. With log p>=20000*firstHitProfileError, the reciprocal
  is at most (10001/10000)/(profile(u)*log p) for .7<=u<=3.
- FirstHitGrid.lean: 23 rational affine chords from u=.7 to u=3 bound the
  reciprocal full profile. The excess chords include factor10001/10000
  and subtract10/19. firstHit_affine_prime_sum_le bounds their prime-bin
  sum by (93/95+17/50000)/L+firstHitChordError/L^2.
- FirstHitMediumSum.lean: the bin partition telescopes exactly, including
  the integer floor endpoints. firstHit_medium_sum_le applies the chord
  budget to the ACTUAL normalizer reciprocal excess over
  exp(L/7)<p<=exp(5L/12), with explicit large-log and Euler-product premises.
Logs /tmp/first_hit_integer_cutoff.log, /tmp/first_hit_grid.log,
/tmp/first_hit_medium_sum.log. Some linter messages remain, but no errors
or sorryAx in the final audits.

Still needed: global eventual thresholds/fixed-wheel treatment, the exact
Euler-density telescoping identity, total coefficient cost, and reference
certificate transfer. Even that would only yield a ~2.4 exponent, not the
requested quadratic bound. The original erdos_970 remains unsolved.

## Global unconditional first-hit main-term slack (VERIFIED)

Submission/FirstHitMainSum.lean compiles; final axiom audit uses only the
permitted three axioms. Log /tmp/first_hit_main_sum.log.
- initial_density_telescope proves the exact sum of prefix Euler densities.
- primeNormalizer_eq_eulerMass_of_prod_le and firstHitMeanExcess_zero_on_wheel
  handle the entire fixed initial wheel exactly.
- firstHitMainSum_finite_bound combines early and medium prime excesses,
  with explicit finite threshold and wheel assumptions.
- exists_firstHit_threshold_wheel discharges the prime-threshold requirements.
- exists_firstHitMainSum_slack is UNCONDITIONAL: there is L0>0 such that,
  for every real L>=L0, with Z=floor(exp(5L/12)),
    sum_{p<=Z} 1/(p*G_{<p}(ceil(exp((L-log p)/2)))) <= 1-1/(100*L).
This is a proved first-hit MAIN TERM, not yet an interval-survivor estimate.

Submission/FirstHitTransfer.lean also compiles (log /tmp/first_hit_transfer.log),
with a clean final axiom audit. It explicitly expands the first-hit polynomial,
bounds its absolute coefficient cost by 1+sum_i card(D_i)^2, and proves
survivor_of_dominating_first_hit. The latter transfers reference kernels to
coordinatewise smaller actual hit marginals, under its explicit main+cost
inequality. No transfer cost or independence assumption is omitted.

Next assembly tasks are embedding prior divisor supports into the full index
set, identifying their normalizers, summing cutoff-squared costs, and applying
the construction to arbitrary prime sets via increasing reference marginals.
These results still do not settle erdos_970 or improve the currently stated
unrestricted Jacobsthal exponent until the survivor argument is assembled.

## Actual first-hit survivor criterion assembled (VERIFIED)

Submission/FirstHitDivisorSupport.lean and FirstHitPrimeSurvivor.lean compile,
with final printed axioms only propext, Classical.choice, Quot.sound.
Logs /tmp/first_hit_divisor_support.log and /tmp/first_hit_prime_survivor.log.
- priorDivisorSupport restricts the divisor family to coordinates before i.
  It is nonempty, downward closed, and has cardinality <= its integer cutoff.
- normalizer_priorDivisorSupport identifies its exact normalizer with the
  prime normalizer of the image of prior coordinates. firstPrimeList_prior_image
  proves that image is exactly the primes strictly below the i-th prime.
- reference_prior_main_le and reference_prior_cost_le bound a truncated initial
  list by the complete prime-cutoff main sum and total cost.
- firstHit_total_cutoff_cost bounds sum_{p<=Z} N_p^2 by 4*exp(L)*(1+L).
- prime_survivor_of_firstHitMainSum applies the explicit lower polynomial
  and marginal transfer to every actual prime set whose reference primes lie
  below Z=floor(exp(5L/12)).
- isJacobsthalBound_of_firstHitMainSum: if nthPrime(k)<=Z, main<=1-1/(100L),
  and m>100L*(1+4exp(L)*(1+L)), then IsJacobsthalBound k m.
Thus the survivor assembly gap for this scale has now been closed.
An explicit power bound in k is being extracted next. No quadratic bound
or negation has been obtained; Spec.lean is still unchanged.


## NEW STRONGEST UNRESTRICTED BOUND: exponent 30603/12500 (VERIFIED)

Submission/FirstHitPowerBound.lean compiles with a built olean. Both final
printed axioms are only propext, Classical.choice, Quot.sound.
Log: /tmp/first_hit_power_bound.log.
- firstHit_remainder_exp_bound: for L>=0, the full required interval budget
  100*L*(1+4*exp(L)*(1+L)) is <=8050000*exp(101*L/100).
- exists_firstHit_prime_power_bound: there is A>0 such that for EVERY k,
    jacobsthalFunction(k) <= A * nthPrime(k)^(303/125).
  This uses the unconditional main-term margin, the explicit coefficient
  cost, the actual arbitrary-prime survivor transfer, and integer rounding.
- nth_prime_small_power: for k>0,
    nthPrime(k) <=48000*k^(101/100),
  from the elementary prime-counting bound and log_le_rpow_div.
- exists_firstHit_power_bound: there is C>0 such that for every k>0,
    jacobsthalFunction(k) <= C*k^(30603/12500).
  The exponent is EXACTLY 2.44824, not 2. No logarithmic divisor is asserted.

This strictly improves the previous unrestricted exponent 2.49999. The
variable-cutoff first-hit survivor/transfer assembly is NOW COMPLETE for this
bound; do not continue treating its old wheel, cost, or transfer gaps as open.
The remaining task is the genuine exponent gap to 2 (or an exact negation),
not a missing normalization step in the new bound. Letting the two harmless
1/100 power slacks tend to zero would approach exponent12/5, still not 2;
no uniform bound at 2 follows from such a limit.

Spec.lean is unchanged, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
The original theorem erdos_970 and its sole sorry remain at lines2175/2177.
No completed target proof or exact-negation disproof has been submitted.

## Sharper Euler-product upper coefficient: nine fifths (VERIFIED)

EulerMassNineFifths.lean now compiles and its olean is built. The pending
factor-2 typo in the linear exponential bound was corrected to factor 4;
the generator /tmp/generate_euler_nine.py was corrected too. Build log:
/tmp/euler_mass_nine_fifths.log. All final audits list only propext,
Classical.choice, Quot.sound.

New theorem eventually_eulerMass_initial_le_nine_fifths_log proves
E_{<=R} <= (9/5)*log R eventually. It uses an eleven-term alternating
exponential bound, general scaled prime logarithmic moments, and the
explicit bound (1+log R/4)*exp(1064111336/540280125 +
112*sharpMomentError/log R). No prime-number theorem is used.

The sharper coefficient would permit extending the medium first-hit grid
to bottom ratio .63 and Euler subtraction 5/9, with prospective cutoff
exp(50*L/113). This yields a base exponent 2.26, NOT a quadratic bound.
That extension is not yet implemented. The existing verified unrestricted
exponent remains 30603/12500. The quadratic conjecture remains unsolved,
and Spec.lean still contains its original sorry.

## Post-Euler continuation review (NO SETTLEMENT)

Reviewed the existing smaller-cardinality induction, recursive-child feedback,
conditional Bennett estimates, phase cylinders, and overlap arguments. None
supplies the missing uniform quadratic step. No smaller-cardinality bound was
used at its terminal cardinality, and no conditional variance estimate was
replaced by an unconditional average. The nine-fifths Euler estimate is an
auxiliary result only. The final conjecture file was left unchanged; no proof
or exact negation has been obtained in this continuation.


## Refined first-hit pipeline completed: exponent 2.305426 (VERIFIED)

The repaired nine-fifths Euler-product cap has now been incorporated in a
complete unrestricted bound, not just in an auxiliary integral. New files,
all compiled with built oleans and only the permitted axioms in final audits:

- FirstHitExtendedCutoff.lean: the existing full-profile normalizer and
  reciprocal estimates now have new variants valid for u >= 3/5. The old
  declarations are unchanged. The threshold stays 20000*firstHitProfileError.
- FirstHitRefinedGrid.lean: new 24-bin grid .63,.7,.8,...,3. The first
  reciprocal chord has endpoint values 100/63 and 10/7. The excess subtraction
  is 5/9. Exact rational budget: 35213/36000. Affine prime errors retained.
- FirstHitRefinedMedium.lean: exact integer prime bins and their partition;
  actual medium-prime excess <= (35213/36000)/L+refinedHitChordError/L^2.
- FirstHitRefinedMain.lean: cutoff Z=floor(exp(50L/113)); exact wheel and
  density telescoping. Main margin is 113/90-35213/36000-42/155 > 6/1000.
  All eventual thresholds discharged, yielding
    exists_refinedHitMainSum_slack:
      exists L0>0, forall L>=L0, refinedHitMainSum L <= 1-1/(200L).
- FirstHitRefinedSurvivor.lean: actual-prime transfer, integer cutoffs,
  and total coefficient cost <=1+4 exp(L)(1+L). Required interval budget
  is 200L(1+4 exp(L)(1+L)).
- FirstHitRefinedPower.lean: this budget is <=16100000 exp(101L/100).
  The prime-power bound has exponent 11413/5000. Using the previous
  nth-prime estimate gives
    exists_refinedHit_power_bound:
      exists C>0, forall k>0,
        jacobsthalFunction k <= C*k^(1152713/500000).
  The final exponent is exactly 2.305426, still strictly greater than 2.

Logs: /tmp/first_hit_extended_cutoff.log, /tmp/first_hit_refined_grid.log,
/tmp/first_hit_refined_medium.log, /tmp/first_hit_refined_main.log,
/tmp/first_hit_refined_survivor.log, /tmp/first_hit_refined_power.log.
Grid development briefly had two local elaboration/algebra failures; these
were repaired before the clean final build and axiom audit. No unverified
numerical value is used in any theorem.

Analytic diagnostic (NOT A LEAN THEOREM): approximating the full Dickman
normalizer in the continuous first-hit Selberg model gives tail integral
about .378747 and a limiting base exponent about 2.06568. Thus merely
sharpening this particular normalizer model does not appear to reach 2.
This is not a universal sieve barrier or a disproof of erdos_970.

The shared-phase collision, triangle, cover-packing, cardinality-induction,
and optimal-core routes were reviewed again. No missing uniform arithmetic
saving was proved. No completed target theorem or exact negation exists.
Spec.lean remains unchanged, with its sole original sorry at line 2177.

## Ordinary histogram log-concavity ruled out (VERIFIED AUXILIARY RESULT)

The weaker ordinary log-concavity route also fails, not merely the previous
ultra-log-concavity route. New file GapOrdinaryLogConcavityObstruction.lean
compiles with a built olean; all printed axioms are permitted. It imports
GapCountShapeExample, not Spec.lean. Log /tmp/gap_ordinary_lc_obstruction.log.

For N=231=3*7*11 and m=26 the exact frequencies at counts14,15,16 are89,18,4.
The kernel checks these finite computations independently. Since18^2<89*4,
not_countLogConcave_231 and not_all_squarefree_countLogConcave disprove the
ordinary histogram shape assertion, NOT the Jacobsthal conjecture.
The targeted exact-integer diagnostic /tmp/count_ordinary_lc.py found this
witness; it is not a trusted proof dependency. No worker remains active.

A square-root-scale sub-mean lower tail remains a potentially sufficient
unproved candidate when combined with filtered core cylinders and small
retained entropy. Full-centered subexponential concentration must be treated
more carefully: on-paper rough-number asymptotics at m=y^u with fixed u>2
can give a nonzero fractional discrepancy, with phase weight exp(-O(y)),
whereas sqrt(m*density) grows faster than y. Thus a uniform full-centered
psi_1 bound of size O(sqrt(m*density)) would be false. For example u=21/10
still has Buchstab density (1+log(11/10))/(21/10)<exp(-gamma), while
sqrt(m/log y)>>y. This uses standard asymptotics and is NOT a new Lean
counterexample. It does not refute a tail restricted to a sufficiently small
fixed fraction of the mean. No such truncated tail has been proved.

The two-sided greedy, overlap, and conditional Bennett reviews yielded no
new uniform saving sufficient for the original conjecture. In particular,
conditional high-count caps cannot simply be applied to the exceptional
low-count cores whose control is precisely missing. Spec.lean is unchanged.


## Refined first-hit logarithmic extraction (VERIFIED)

New file FirstHitRefinedLogPower.lean compiles with built olean and permitted
axioms only. Log: /tmp/first_hit_refined_logpower.log. It removes the two
auxiliary positive power allowances from FirstHitRefinedPower, while keeping
the same substantive first-hit base exponent 113/50=2.26.

- refinedHit_remainder_log_bound:
    200 L (1+4 exp(L)(1+L)) <=1000 (1+L)^2 exp(L), for L>=0.
- nth_prime_log_bound:
    log(nthPrime k)<=160 log(k+2), k>0.
- exists_refinedHit_logpower_bound:
    exists C>0, forall k>0,
      jacobsthalFunction k <= C*k^(113/50)*log(k+2)^(213/50).
  Uses L=L0+(113/50)log(nthPrime k), interval length floor(X)+1 with
  X=1000(1+L)^2 exp(L), and nthPrime k <=160*k*log(k+2).
- log_rpow_le_small_power: an explicit arbitrary-positive-power absorption
  bound using Real.log_le_rpow_div, with no limiting-constant inference.
- exists_refinedHit_power_bound_any(epsilon), epsilon>0:
    exists C>0, forall k>0,
      jacobsthalFunction k <= C*k^(113/50+epsilon).
  The constant DEPENDS on epsilon. This is not a quadratic bound, and even
  removing epsilon would leave the substantive exponent 2.26.

The first compile had a harmless failing `dsimp` inside a local cast/log
inequality; it was removed. The successful final build and clean axiom
prints supersede that intermediate failure. No original statement or import
in Spec.lean was altered. No completed target proof was submitted.


## Rounded-moment timeout resolved (EXACT DIAGNOSTIC, NOT LEAN-CHECKED)

The old full-support 14-prime, length600 feasibility test timed out because
it started with every moment row. A new adaptive run retained ALL Boolean
patterns (no pattern-product cap) and started with170 moment constraints.
It completed its first solve in~1.3 seconds and found a minimum empty-atom
mass22. Thus no further rows were necessary to prove infeasibility of the
zero-empty-atom relaxation. The solver's minimizing population violated26
omitted moments; that does NOT invalidate a positive lower bound obtained
from the relaxed constraints, and it was not called a full feasible population.

Script /tmp/rounded_moment_adaptive_full.py; log
/tmp/rounded_moment_adaptive_full_14_600.log; data
/tmp/rounded_moment_adaptive_14_600.npz. No worker remains running.
An exact Python Fraction reconstruction checks the dual independently:
constant1,71 nonconstant coefficients all +/-1, value<=0 at all16383
nonempty patterns, value1 at the empty pattern, rounded main22.
Data: /tmp/rounded_moment_14_600_exact_dual.json.
This finite certificate has NOT been checked in Lean, is not an arbitrary-
prime transfer, and is not a uniform quadratic theorem. Do not rerun the
old unresolved test or treat it as an actual interval-cover counterexample.

## Cubic saturation and eighth-power tail: base exponent2.16 (VERIFIED)

All new source files below compile with built oleans and final printed axioms
only propext, Classical.choice, Quot.sound. Combined audit:
Submission/FirstHitSaturatedAudit.lean, /tmp/first_hit_saturated_audit.log.
The exact original conjecture is still UNSOLVED; Spec.lean is unchanged.

New components:
- FirstHitLowerCutoff.lean: normalizer and reciprocal variants extend the
  old medium-range lower cutoff to u>=11/20. The same20000*profileError
  threshold suffices because (11/20)*20000>=10001.
- FirstHitEighthTail.lean: for u>=4,
    exp(-2(u-3)) <= (1/7)*(4/u)^8.
  This uses exp(2)>=7, not a numerical oracle. The seventh prime logarithmic
  moment then gives first_hit_far_sum_bound, for primes through exp(L/9):
    excess sum <=54/(1519L)+972*sharpMomentError/(217L^2).
- FirstHitCubeBridge.lean: cutoff monotonicity of the prime normalizer;
  firstHitProfile(3)>=17/10 from the existing rational log certificate;
  reciprocal cutoff bound beyond the cube. Over exp(L/9)<p<=exp(L/7),
    excess <=A/(p log p), A=(10001/10000)*(10/17)-5/9.
  The actual prime sum is <=1/(15L)+firstHitBridgeError/L^2,
  with firstHitBridgeError=162*A*(boundConstant+1).
- FirstHitSaturatedEarly.lean: exact finite-prime split and fixed-wheel
  treatment assemble the two early ranges. Main coefficient
    saturatedEarlyMain=1/15+54/1519;
  error saturatedEarlyError=firstHitBridgeError+972*sharpMomentError/217.
- FirstHitSaturatedGrid.lean:24 bins .58,.7,.8,...,3. The first reciprocal
  endpoint is50/29. Exact finite excess budget<=109/100.
- FirstHitSaturatedMedium.lean: actual medium-prime sum with that budget,
  using the nine-fifths Euler cap and the extended cutoff lemma.
- FirstHitSaturatedMain.lean: cutoff Z=floor(exp(25L/54)). Main margin
    6/5-109/100-saturatedEarlyMain >6/1000.
  All eventual thresholds are discharged, including W<=floor(exp(L/9)).
  exists_saturatedHitMainSum_slack gives eventually main<=1-1/(200L).
- FirstHitSaturatedSurvivor.lean: same genuine arbitrary-prime transfer and
  summed coefficient cost as before; actual interval budget remains
    200L(1+4 exp(L)(1+L)).
- FirstHitSaturatedLogPower.lean: with L=L0+(54/25)log(nthPrime k), proves
    exists_saturatedHit_logpower_bound:
      exists C>0, forall k>0,
        jacobsthalFunction k <=C*k^(54/25)*log(k+2)^(104/25).
  exists_saturatedHit_power_bound_any gives exponent54/25+epsilon for each
  epsilon>0, with a constant depending on epsilon.

Individual logs: /tmp/first_hit_lower_cutoff.log, /tmp/first_hit_eighth_tail.log,
/tmp/first_hit_cube_bridge.log, /tmp/first_hit_saturated_early.log,
/tmp/first_hit_saturated_grid.log, /tmp/first_hit_saturated_medium.log,
/tmp/first_hit_saturated_main.log, /tmp/first_hit_saturated_survivor.log,
/tmp/first_hit_saturated_logpower.log. Two local cube-bridge proof failures
(a natural power comparison and numeral normalization) were repaired before
the successful build and clean audit. No unverified hypothesis is hidden in
these unconditional bounds, and no numerical LP certificate is imported.

This improves the substantive first-hit exponent, not just the auxiliary
power slack. It does NOT reach2. The previously noted continuous Selberg
model diagnostic still suggests a limiting exponent above2 even with sharper
normalizers, and is not a formal barrier for all sieve methods. No missing
uniform arithmetic cancellation, cover amplification, or truncated lower-tail
estimate was proved in the accompanying review. No target proof was submitted.

## Fourteen-prime rounded certificate transferred to Lean (VERIFIED)

Original erdos_970 STILL UNSOLVED. New source files with built oleans:
- Submission/Rounded600Data.lean: explicit 72 terms (constant plus 71
  nonconstant terms), signed integer coefficients, prime-support checks.
- Submission/Rounded600.lean: exact integer rounded main term 22, a symbolic
  factorization of the polynomial, its pointwise survivor-indicator bound,
  and the actual interval-count conclusion at_least_twenty_two.

For the FIXED prime set {2,3,5,7,11,13,17,19,23,29,31,37,41,43}, every residue
phase leaves at least22 survivors in [0,600). The factorization, writing Xp
for the Boolean hit indicator, is
 (1-X2)(1-X3) *
 [ (1-X5)(1-X7-X11-X13-X17-X19) - X23-X29-X31-X37-X41-X43 ].
It is proved symbolically, without enumerating all 16384 Boolean patterns.
The floor/ceiling arithmetic is an integer computation checked by
`decide +kernel`; the cast to the real-valued sieve API is explicit.

This transfers the positive external LP dual certificate, not its minimizing
population (which violated omitted constraints). In particular, no claim
that22 is the optimum under ALL rounded-moment constraints is made. These
files do not depend on Spec.lean or its unresolved theorem; final printed
axioms are only propext, Classical.choice, Quot.sound. Logs:
/tmp/rounded600_data.log and /tmp/rounded600.log. Intermediate failed compiles
are superseded by the final clean build. No numerical LP was rerun.

CRITICAL SCOPE: this fixed-prime finite certificate does not transfer to all
fourteen-prime sets, and supplies no uniform-in-k quadratic estimate. The
strongest unrestricted auxiliary result remains the saturated first-hit
k^(54/25)*log(k+2)^(104/25) bound. Reviewing phase consistency, existing
mixed-pattern examples, overlap packing, and the low-tail obstructions
produced no new unrestricted estimate in this continuation.

Spec.lean remains unchanged, with its sole original sorry and SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No proof of erdos_970 or of its exact negation has been obtained or submitted.

## Weakened soft endpoint criteria and exact initial slope (VERIFIED)

Original erdos_970 STILL UNSOLVED. Three new source files compile with built
oleans; final axiom audits use only propext, Classical.choice, Quot.sound.
No changes to Spec.lean or its original statement/imports/sorry.

1. WeakSoftEndpointReduction.lean
   - countLaplace_le_of_endpoint_rate iterates an arbitrary fixed rate for
     the particular prime set. No universal endpoint premise is assumed.
   - CriticalSoftEndpointBound(c,t) is the EXPLICIT UNPROVED condition
       [c*log(k+2)/(k+1)]*countLaplace(P,t,m) <= endpointLaplace(P,t,m)
     for all |P|<=k and m. With c,t>0, it implies CriticalVoidBound with
     coefficient c*(1-exp(-t)), hence exactly the original quadratic target.
   - DensityPowerSoftEndpointBound(c,t,B) instead uses rate c*density(P)^B,
     where B is fixed. Mertens converts it to PolylogVoidBound; any positive
     c,t would again settle the target. The endpoint premise is retained.
   - density_power_softEndpoint_zero proves the rate density^(B+1) at t=0.
     This does NOT provide a positive parameter; the decay factor is zero.

2. SoftEndpointDerivative.lean
   - endpointSlope(P,m) = m*density(P)^2 - E[S_m*Y_m].
   - Exact expansion as sum over Q subset P of pairWeight(P,Q) times
       m/prod(Q) - floor(m/prod(Q)).
   - 0<=endpointSlope<=density(P), uniformly in interval length.
   - Exact HasDerivAt results for countLaplace and endpointLaplace at0,
     then for tiltedEndpoint=endpointLaplace/countLaplace at0. The quotient
     derivative is endpointSlope; both numerator and denominator are included.

3. SoftEndpointLocal.lean
   Write N=prod(P). The full-divisor term proves
       (m mod N)/N^2 <= endpointSlope(P,m).
   In fact endpointSlope(P,m)=0 iff N divides m.
   Thus if N does not divide m, the actual tilted endpoint probability is
   strictly greater than density(P) eventually as t tends to0 from the right.
   This is a genuine theorem for actual sieve phases, not an independent-row
   approximation or an arbitrary synthetic process.

CRITICAL GAP: the last neighborhood depends on P AND m. No uniform positive
parameter, higher-derivative control, or critical endpoint rate has been
proved. Pointwise continuity/positive initial slope must not be exchanged
with a uniform quantifier over prime sets and interval lengths. The
insertion identity still retains an uncontrolled concentration term. The
new conditional theorems do not constitute a proof of their hypotheses.
The strongest unrestricted bound remains k^(54/25)*log(k+2)^(104/25).

Logs: /tmp/weak_soft_endpoint.log, /tmp/soft_endpoint_derivative.log,
/tmp/soft_endpoint_local.log. Intermediate errors were repaired; all final
builds and audits are clean. CheckSoftDerivative.lean and CheckSoftSlope.lean
are scratch API queries and are not imported; the latter has an intentionally
unresolved Real.slope_def_field query. No new numerical search was performed,
and no active worker remains. No proof or exact negation of erdos_970 has
been obtained or submitted. Spec.lean SHA256 remains
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.

## Budget-uniform positive soft parameter (VERIFIED, NO SETTLEMENT)

Original erdos_970 STILL UNSOLVED. New files compile with built oleans;
all final axiom audits contain only propext, Classical.choice, Quot.sound.

1. FullCountDiscrepancy.lean
   - fullPolynomial is the full powerset inclusion-exclusion polynomial.
   - Its value is the exact survivor indicator, its mean is density(P),
     and its coefficient L1 cost is 2^|P|.
   - fullPhaseResidues transports normalized actual phases to the existing
     finite-sieve-polynomial API.
   - intervalCount_full_discrepancy:
       |S_m(r)-m*density(P)| <= 2^|P|.
   - intervalCount_phase_difference:
       |S_m(r)-S_m(s)| <= 2^(|P|+1).
     Both hold for all interval lengths and actual phases.

2. BudgetSoftEndpoint.lean
   - endpointLaplace_ge_of_count_range: if A<=S_m(r)<=B in every phase,
       exp(-t*(B-A))*density(P)*countLaplace <= endpointLaplace
     for t>=0. The range loss is retained exactly; no averaged variance is
     substituted for a deterministic range bound.
   - endpointLaplace_ge_full_cost inserts the full inclusion-exclusion range.
   - budgetEndpointParameter(k)=log(2)/2^(k+1) is strictly positive.
   - budget_softEndpoint: at this parameter, for every |P|<=k and EVERY m,
       (density(P)/2)*countLaplace <= endpointLaplace.
   - budget_exponential_void supplies the resulting unconditional void bound
       coveredFraction(P,m) <=
       exp(-(density(P)/2)*(1-exp(-budgetEndpointParameter(k)))*m).

CRITICAL SCOPE: This removes dependence of the small parameter on the
particular primes and interval length, but only by allowing exponential
shrinkage in the cardinality budget. The resulting decay rate is on the
scale density(P)*2^(-k), far below the critical log(k)/k rate needed by the
quadratic reduction. It does not improve the strongest unrestricted
k^(54/25)*log(k+2)^(104/25) bound and does not prove a fixed positive-parameter
endpoint estimate. Existing parity-discrepancy results also caution against
expecting a uniformly small count range at every interval length; they do
not exclude a sharper nonlinear Gibbs argument.

No adequate uniform positive-parameter remainder or conditional tilted-count
estimate was obtained. No new numerical experiment was run. Logs:
/tmp/full_count_discrepancy.log and /tmp/budget_soft_endpoint.log. Initial
compile errors were repaired; final builds and axiom audits are clean.
Spec.lean remains unchanged, with its original statement, sole import and
sole sorry (line2177), SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No proof or exact negation of erdos_970 has been obtained or submitted.

## Normalized soft endpoint counterexample (VERIFIED AUXILIARY RESULT)

Original erdos_970 STILL UNSOLVED. This continuation closes the old phase-space
transport omission in GapHazardExample and disproves extending the positive
initial slope to global monotonicity. It does NOT disprove the target or a
smaller-constant endpoint estimate at one fixed positive parameter.

New source files with built oleans and only permitted final axiom dependencies:

1. HazardPhaseTransport.lean
   - reflectedPhaseEquiv is an explicit equivalence from the old FullPhase
     (Fin231 x Fin101 x Fin103 x Fin107) to GapAverages.Phase for
     {3,7,11,101,103,107}. It uses the exact core CRT injectivity, tail residue
     reflection, and equal finite cardinalities. No 257-million-state scan.
   - Reflection changes the old interval1..9 and left endpoint0 to [0,9)
     and right endpoint9, matching the Laplace API exactly.
   - reflected_count_zero iff Covers, and reflected_endpoint is the exact
     indicator of Endpoint. Full survivor counts are also reflected explicitly.

2. SoftEndpointHazardLimit.lean
   - countLaplace_pos for genuine prime sets and all real parameters.
   - For every fixed P,m, countLaplace tends to coveredFraction as t->infinity;
     endpointLaplace tends to coveredEndpointFraction. This is finite positive
     Laplace convergence, not a tail/concentration hypothesis.
   - Actual normalized probabilities for the six-prime example are exactly
       coveredFraction(P,9)=48/257130951,
       coveredEndpointFraction(P,9)=24/257130951.
   - tilted_endpoint_limit: tiltedEndpoint(P,9,t)->1/2 < density(P).
   - exists_positive_unit_endpoint_failure and tilted_endpoint_not_monotone.
   - strict_improvement_then_worsening: for the SAME prime set and interval,
     the tilted endpoint is >density for all sufficiently small positive t
     (using the verified positive initial slope) and <density for all
     sufficiently large t. Thus global monotonicity is genuinely false.

3. SoftEndpointExponentialRemainder.lean
   - Integrality gives S>=1 on nonzero-count phases.
   - For t>=0, countLaplace<=coveredFraction+exp(-t), and likewise
     endpointLaplace<=coveredEndpointFraction+exp(-t).
   - explicit_unit_endpoint_failure proves
       NOT SoftEndpointBound 1 (log(10000000000)).
     All final numerical comparisons are exact rational Lean calculations.
     No numerical root search, unchecked solver, or native_decide was used.

CRITICAL SCOPE: these are auxiliary obstructions to c=1 at the displayed
parameter and to global monotonicity, not the negation of erdos_970. They do
not rule out a smaller positive endpoint constant, a fixed density-power
rate, the weaker critical rate, or a uniform sufficiently small parameter.
No adequate positive-parameter tilted covariance estimate was obtained.
The strongest unrestricted bound remains k^(54/25)*log(k+2)^(104/25).

Audit: Submission/SoftEndpointHazardAudit.lean,
/tmp/soft_endpoint_hazard_audit.log. Individual final logs:
/tmp/hazard_phase_transport.log, /tmp/soft_endpoint_hazard_limit.log,
/tmp/soft_endpoint_exponential_remainder.log. Intermediate compilation errors
were repaired. CheckHazardTransport.lean and CheckLaplaceLimit.lean are scratch
API files with some unresolved queries and are not imported by the proofs.
No active worker remains. Spec.lean is unchanged with its original sole sorry
and SHA256 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed proof or exact negation of erdos_970 has been submitted.

## Dyadic Laplace shortcut tested and obstructed (VERIFIED AUXILIARY RESULT)

Original erdos_970 STILL UNSOLVED. Spec.lean was not edited. The Gibbs
resampling review retained the private-position term: at a zero-count phase
upward resampling changes do not vanish, so a lower-tail entropy argument
cannot discard that term by substituting current survivors.

Investigated the genuinely weaker alternative to pointwise unit endpoint
control: F(2m,t) <= F(m,t)^2. This is false when quantified over every positive
t. New files, both compiled with oleans and clean printed axioms:
- Submission/DyadicLaplaceData.lean
- Submission/DyadicLaplaceObstruction.lean
Namespace Erdos970.GapAverages.DyadicExample.

An explicit Fin231-to-Phase{3,7,11} equivalence uses the elementary coprime CRT
injectivity and equal cardinalities. It transfers the actual interval counts,
not a synthetic histogram. Kernel computations over naturals give:
  64^16 * F(26,log64) = 362124420/231,
  64^30 * F(52,log64) = 146912027010/231.
The exact comparison
  231 * 146912027010 * 64^2 > 362124420^2
proves dyadic_laplace_failure and not_uniform_dyadic_laplace.
All final printed axioms are propext, Classical.choice, Quot.sound. No
native_decide is used. Logs /tmp/dyadic_laplace_data.log and
/tmp/dyadic_laplace_obstruction.log. The initial sum-rewrite error in the
latter was repaired; the final build is clean.

The motivated external diagnostic used cyclic reduced-residue counts and
integer arithmetic. At m26 and modulus231 the count histograms are
  26: {12:20,13:100,14:89,15:18,16:4},
  52: {24:2,25:8,26:51,27:104,28:58,29:6,30:2}.
The leading-coefficient comparison 231*2 > 20^2 already predicts failure as
t tends to infinity. At z=exp(-t), the normalized dyadic difference factors
as -(z-1)^2*(16*z^6+176*z^5+910*z^4+4262*z^3+5897*z^2+2028*z-62).
Only the explicit log64 comparison, not this full factorization, was needed
by the Lean theorem.

CRITICAL SCOPE: This does not disprove a dyadic inequality at ONE sufficiently
small positive parameter. Exact tests at z=1/2 and z=2 on a few small prime
sets found no failures in the tested ranges; these are diagnostics, not
proofs. Scripts /tmp/check_dyadic_laplace.py, /tmp/check_dyadic_minima.py,
/tmp/check_dyadic_upper.py. No worker remains active. CheckDyadic*.lean are
scratch API queries, some intentionally failing, and are not proof imports.

No adequate uniform small-parameter Gibbs comparison was proved. The best
unrestricted bound remains the previous k^(54/25)*log(k+2)^(104/25) result.
Spec.lean retains its original conjecture, sole import, and sole sorry. No
complete target proof or exact-negation theorem has been submitted.

## Quarter-period fixed-parameter obstruction (VERIFIED)

Original erdos_970 STILL UNSOLVED; Spec.lean has not changed. Investigating
whether the dyadic shortcut could survive at one fixed small parameter found
a structured failure at t=log2. This is still an auxiliary question, NOT the
original conjecture.

For the five-prime set P={3,7,11,19,23}, N=100947, m=25236, exact external
integer calculation gives
  2^11887 F_m(log2)=33897666/N,
  2^23774 F_(2m)(log2)=13280119881/N,
and N*13280119881 >33897666^2 (ratio about1.16669).
The six-prime set adding31, m=(prod(P)-1)/4, gave a ratio>218 diagnostically;
that six-prime example is NOT being transferred to Lean. All primes in these
sets are3 mod4, motivating the quarter-period and aligned rounding errors.
No claim for arbitrarily small positive parameters has been proved.

Symbolic files already compile with permitted axioms:
- CyclicSieveCount.lean: exact cumulative integer inclusion-exclusion,
  cyclicPhaseEquiv, actual cyclic_count and cyclic_laplace.
- KernelNatQuotient.lean: proved binary search quotient with ordinary-div
  fallback; quotient_eq_div is a kernel theorem, not a native axiom.
- QuarterLaplaceDefs.lean: 16 positive and16 negative divisor terms,
  fastPrefix, fastCount, and chunked weight definitions.
- QuarterLaplaceModel.lean: identifies that formula with actual interval
  counts and establishes the scaled_laplace identity.
- QuarterLaplaceBounds.lean: termwise rounding gives fastCount25236<=11887
  and fastCount50472<=23774, for EVERY start, without enumerating starts.
- QuarterTracker.lean: a finite integer state machine; strictNat is an
  identity with a proved equation, used only to force intermediate numeric
  evaluation. run_succ and run_add are proved.
- QuarterTrackerCorrect.lean: specState and run_initial_weights identify
  the state machine's two accumulated weights with actual cyclic sums.

The finite arithmetic is being checked as1009 runs of100 steps and a final
47-step run. Every checkpoint is an explicit nine-natural State and is
independently checked by decide+kernel. No external value is trusted. The
checks are split over QuarterTrackerPart0.lean through Part100.lean (ten
proofs/file, last file nine plus tail), with Elab.async=false for memory.
QuarterTrackerData.lean composes them using run_add; it does NOT recompute a
100947-step reduction. QuarterTrackerBridge.lean transfers its result to the
scaled weight sums, and QuarterLaplaceObstruction.lean contains the final
small exact rational comparison. These final three files are NOT YET BUILT
at the time of this entry; do not claim their conclusion is kernel checked
until their clean builds and axiom audits are completed.

Active build: /tmp/build_tracker_parts.py, two worker processes. PID is in
/tmp/tracker_parts_build.pid; progress /tmp/tracker_parts_build.log, each
part's /tmp/quarter_tracker_part_<i>.log and .exit. At last check parts0..27
were clean. When all101 parts finish, build in order: QuarterTrackerData,
QuarterTrackerBridge, QuarterLaplaceObstruction. Check exact timestamps and
logs; old /tmp/quarter_tracker_data.exit=137 records an obsolete failed
monolithic attempt and must not be confused with the eventual new build.

Performance lessons: direct full-period inclusion-exclusion evaluation and
large state reductions exceeded the10GiB effective memory budget. Tiny
independent transition lemmas work. Low Lean -M limits (3000 or4000) fail
while merely loading FormalConjecturesUtil, even on '#check Nat'; those
failures were NOT evidence of an arithmetic algorithm problem. Current
workers have no -M override. All current proof code remains axiom-clean.
Obsolete unsuccessful divisor-enumeration certificate files and scratch
queries have been moved to Scratch/QuarterOld and are not imported by the
current route. Logs for the successful symbolic proofs are
/tmp/cyclic_sieve_count.log, /tmp/kernel_nat_quotient.log,
/tmp/quarter_laplace_model.log, /tmp/quarter_laplace_bounds.log,
/tmp/quarter_tracker.log, /tmp/quarter_tracker_correct.log.

No target proof or exact-negation theorem has been obtained or submitted.
The strongest unrestricted bound remains k^(54/25)*log(k+2)^(104/25).


Completion audit for the quarter-period obstruction:
All101 QuarterTrackerPart files completed with exit0. The three subsequent
files QuarterTrackerData, QuarterTrackerBridge, QuarterLaplaceObstruction
compiled successfully. full_period uses only propext and Quot.sound; the
semantic and analytic results use only propext, Classical.choice, Quot.sound.
The final scale-square script had a redundant rfl, and the strict inequality
cancellation used the wrong side lemma; both are repaired. Final logs:
/tmp/quarter_tracker_data.log, /tmp/quarter_tracker_bridge.log,
/tmp/quarter_laplace_obstruction.log, each with matching exit0 files.
No worker remains. dyadic_log_two_failure and not_dyadic_at_log_two are now
kernel checked for the actual normalized phase model, not a surrogate.
The original conjecture and its negation are STILL UNPROVED. Spec unchanged.

## Post-quarter direct-cover review (NO NEW TARGET ESTIMATE)

The original erdos_970 is still UNSOLVED. Re-read OptimalCoverCore,
OptimalCoreExchange, MultiPrimeExchange, IncrementReduction, the prior
largest-prime count hierarchy, and the overlap reductions. No new Lean
assertion was added in this review.

The optimal-core exchange inequalities remain necessary conditions; they do
not prove that a cheaper replacement exists. The two-private-point property
and the earlier cap p<=h(c-1)*(S+1) do not close a quadratic budget induction.
The smaller-core count inequality supplied by optimality is not a positive
sieve-density lower bound. No such substitution was made.

Also considered whether sparse-tail concentration after exposing a small-prime
core could exploit collision information. The old difficulty persists: a core
cutoff at a fixed sublinear power gives subcritical phase-tail exponents;
moving the cutoff to order k lacks the required uniform lower core count.
Neither an averaged conditional variance nor an informal independence model
provides that count or rules out one exceptional covering phase. These are
unproved directions, not claimed impossibility theorems for other methods.

The quarter-period dyadic log-two obstruction has completed its clean builds
and axiom audit, as recorded above. It is auxiliary only. Spec.lean is unchanged,
with original statement/import and its sole sorry at2177. No target proof,
exact-negation theorem, or purported completed submission has been produced.

## Finite prime thinning and dyadic VOID obstruction (VERIFIED)

The original erdos_970 is STILL UNSOLVED. Four new files compile with built
oleans; their final axiom audits contain only propext, Classical.choice,
Quot.sound. No numerical search or untrusted computation is used in the new
transfer argument.

1. PrimeDilution.lean
   Uses Mathlib's elementary half-unit prime-reciprocal block, not PNT.
   For every B>=4, constructs a finite set R of primes >=B such that
       63/64-1/B <= prod_R(1-1/p) <=63/64,
       sum_R 1/p <=1.
   Proves the finite product and power inequalities, including
       0 <= prod_R(1-1/p)^s - prod_R(1-s/p)
          <=s^2 sum_R(1/p)^2
   when s<=p for every p in R. This is NOT an assertion of exact independent
   thinning by one prime.

2. FiniteThinningMoments.lean
   Defines joint(P,A) as the actual phase mean of survival at every point in A.
   Independent residue coordinates give its exact prime-factor product.
   For disjoint P,R and A subset [0,p) for every p in R,
       joint(P union R,A)=joint(P,A)*prod_R(1-|A|/p).
   Proves exact powerset expansions for coveredFraction and countLaplace at
   log64. All finite counts and normalizations refer to the existing Phase
   model, not to an abstract surrogate distribution.

3. FiniteThinningApproximation.lean
   If R has the preceding dilution bounds, B>=max(4,m), and is disjoint from P,
       |V_(P union R)(m)-F_P(m,log64)| <=2^m*(m^2+m)/B.
   The prime-set joint moments lie in [0,1]; the full inclusion-exclusion cost
   2^m is retained. exists_padding_approx chooses ONE finite added prime set
   for all lengths m<=M, with any specified positive error tolerance.

4. DyadicVoidObstruction.lean
   Transfers the previously kernel-checked three-prime Laplace counterexample
   P={3,7,11}, m26, t=log64, to a genuine finite prime set Q with
       V_Q(52)>V_Q(26)^2.
   exists_dyadic_void_failure and not_uniform_dyadic_void therefore disprove
   UNRESTRICTED dyadic submultiplicativity for zero-survivor probabilities,
   not merely for positive-parameter Laplace transforms.

Logs: /tmp/prime_dilution.log, /tmp/finite_thinning_moments.log,
/tmp/finite_thinning_approximation.log, /tmp/dyadic_void_obstruction.log.
All four final builds and axiom audits are clean. The first file has one
harmless unused-variable warning. CheckThinning.lean is a scratch API query
with intentional unknown-name errors and is not imported by the development.
No worker remains active.

CRITICAL SCOPE: This is not a disproof of Erdős970. The finite added prime set
may have an enormous cardinality compared with26. In particular this does
NOT refute a dyadic void estimate restricted to m>=|P| (or m>=C|P|).
Such a restricted estimate could still be relevant: start from the verified
second-moment bound at m=k and iterate only at lengths at least k. No proof
of that restricted estimate was obtained, and no conditional estimate was
silently promoted to a theorem.

Spec.lean is unchanged (SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9), with its
original import, exact conjecture statement, and sole sorry at2177. No proof
or exact-negation theorem for the target has been obtained or submitted.

## Deterministic recurrence review after finite thinning (NO SETTLEMENT)

Revisited RecursiveSieve, RecursiveSieveTransfer, IntervalRecursiveSieve,
CardinalityBootstrap, the repeated-block diagnostics, and the quantum
refinement/dilation results. No new uniform positive-envelope estimate was
obtained. The numerical reference thresholds were not extrapolated to all
budgets. The at-most-quadratic quantum dilation budget is a length multiplier,
not a bound for the Jacobsthal function. Smaller-cardinality induction premises
exclude the terminal cardinality; no circular use of the terminal bound was
made. No new numerical run or Lean theorem resulted from this review.

The four finite-thinning files and their unrestricted dyadic void obstruction
remain verified auxiliary results. They do not negate the original conjecture,
nor do they exclude a void estimate restricted to long intervals relative to
the prime budget. No such restricted estimate has been proved.

Spec.lean is unchanged and still has its original erdos_970 statement and sole
sorry at2177. No completed target proof or exact negation has been submitted.

## Long-interval dyadic reduction (VERIFIED, EXPLICITLY CONDITIONAL)

Original erdos_970 remains UNSOLVED. New file LongDyadicVoidReduction.lean
compiles with built olean, and all final printed axioms are only propext,
Classical.choice, Quot.sound. Log /tmp/long_dyadic_void_reduction.log.

LongDyadicVoidBound(A) assumes, for every finite prime set P and m>=|P|,
    V_P(2m)<=A*V_P(m)^2.
This estimate is NOT proved. Unlike unrestricted dyadic submultiplicativity,
it is not negated by the finite-padding counterexample established above.

Verified ingredients and conditional conclusion:
- long_dyadic_iteration: for |P|<=k, A>=0, and the hypothesis,
    A*V_P(2^j*k) <=(A*V_P(k))^(2^j).
- eventually_scaled_void_base: unconditionally, for any fixed A>=1 and all
  sufficiently large k, uniformly over |P|<=k,
    A*V_P(k)<=exp(-log(k+2)/2).
  This uses only the existing variance inequality and prime-set Mertens lower
  bound. It does not assume the new doubling estimate.
- long_dyadic_tail: combines the preceding assertions with the explicit
  hypothesis to obtain exp(-2^j*log(k+2)/2).
- eventually_quadratic_of_long_dyadic: choose 2^j between64k and128k,
  normalize a hypothetical cover to polynomially bounded primes, and beat
  its full phase entropy. The result is h(k)<=128*k^2 eventually.
- quadratic_bound_of_long_dyadic: patches the finite initial budgets and
  concludes exactly the original existential real quadratic bound, still
  conditional on LongDyadicVoidBound(A) for one fixed A>=1.

No independent proof of the restricted doubling estimate, no new unrestricted
upper exponent, and no superquadratic cover family were obtained. The
conditional theorem must not be used as if its hypothesis had been established.
The direct reference-site check again failed DNS resolution; no outside result
was imported. CheckLongDyadic.lean is a scratch API file with unknown identifiers,
not a dependency of any verified result. No worker remains active.

Spec.lean is unchanged, with original statement/import and sole sorry at2177.
No completed target proof or exact-negation theorem has been submitted.

## Restricted doubling hypothesis follow-up (NO NEW PROOF)

The LongDyadicVoidBound hypothesis was re-examined against the verified
second-moment and adjacent-count covariance identities. No nonlinear
zero-event estimate followed. Nonpositive covariance of adjacent COUNTS
must not be used as negative association of their zero events. A fixed-factor
bound on the latter remains unproved even for m>=|P|.

No new Lean theorem or numerical computation resulted. No original-conjecture
proof or superquadratic family was obtained. Spec.lean still has its original
statement and sole sorry; the restricted doubling reduction remains explicitly
conditional and has not been applied without its premise.

## Further sieve remainder review (NO SETTLEMENT)

Re-read the common-kernel support barriers, exact Boolean tail cost,
FirstHitDisjointCost, and the saturated first-hit survivor criterion. No new
uniform remainder estimate at quadratic length was proved. The established
coefficient-support disjointness prevents obtaining cross-index cancellation
merely by collecting monomials. Interval smoothing alone does not control
large composite moduli whose CRT class can meet the interval once. No
uniform arithmetic cancellation or pointwise-to-average replacement was
assumed. These observations are not a barrier theorem for all sieve methods.

No new Lean file or numerical run resulted. The best unrestricted verified
bound remains k^(54/25)*log(k+2)^(104/25), not quadratic. Spec.lean retains the
unchanged conjecture and sole sorry; no target proof or disproof was submitted.


## Cardinality-sensitive first-hit remainder: logarithmic saving (VERIFIED)

Original erdos_970 remains UNSOLVED. Two new source files compile with built
oleans; all final printed axioms are only propext, Classical.choice, Quot.sound.
No new numerical diagnostic or counterexample search was used.

FirstHitCardinalityCost.lean retains the actual reference-prime reciprocal sum
in the coefficient cost instead of bounding it by a harmonic sum. For t<=k,
with the same verified first-hit cutoffs,
  sum_i |D_i|^2 <=4 exp(L)*(log log(k+2)+reciprocalConstant).
The existing cardinality-uniform Mertens theorem proves this bound. The
arbitrary-prime transfer is reassembled with this cost; its main-term slack
and all hypotheses remain the same verified ones, not new conjectures.

FirstHitLogLogPower.lean uses a positive explicit envelope
  (1+|reciprocalConstant|)*(1+log log(k+3))
for that reciprocal factor, k>0. The interval length is now of order
  L exp(L)*(1+log log(k+3))
rather than L^2 exp(L). Choosing L=L0+(54/25)log(nthPrime k) as before gives
  exists_saturatedHit_loglog_bound:
    exists C>0, forall k>0,
      h(k)<=C*k^(54/25)*log(k+2)^(79/25)*(1+log log(k+3)).
This is the NEW STRONGEST unrestricted bound in this development. It saves
one logarithmic factor up to a log-log factor. The power54/25 is unchanged
and remains larger than2, so the result does NOT imply the target.

Logs: /tmp/first_hit_cardinality_cost.log, /tmp/first_hit_loglog_power.log.
The cost proof had a sum-image rewrite direction error, repaired before its
clean build. Its remaining unreachable-ring warning is harmless. The final
log-log extraction compiled and passed its axiom audit. No worker remains.

Spec.lean is unchanged, with its original import, exact erdos_970 statement,
and sole sorry at2177. No target proof or exact negation was submitted.

## Post-logarithmic cardinality and phase review (NO SETTLEMENT)

The original erdos_970 remains UNSOLVED. No new Lean theorem was obtained in
this continuation. Re-read the long-interval dyadic reduction, exact core-tail
sieve, reciprocal-sparse exponential bound, smaller-cardinality and repeated-
block bootstrap, optimal-core exchanges, and Boolean upper-weight reductions.

No new bridge between the sparse-tail estimates and arbitrary covers was
proved. After conditioning on core survivors, tail residue counts need not be
floor/ceiling balanced. The unconditional sparse-tail exponential-moment bound
cannot simply be applied to those conditional populations. Nor does the
negative covariance of adjacent survivor counts prove a doubling inequality
for zero-count events. The LongDyadicVoidBound premise remains unproved.

Reviewed global rephasing, largest-prime insertion, and simultaneous tail-row
bounds as possible positional improvements over independent CRT remainders.
No improving exchange, uniform increment, or adequate simultaneous-row bound
was established. The smaller-cardinality bounds were not applied at their
excluded terminal cardinality. No numerical search or computation was started.

The strongest verified unrestricted bound is still the one recorded at the
header: k^(54/25)*log(k+2)^(79/25)*(1+log log(k+3)). Its exponent exceeds two;
no constant change or limiting argument turns it into the requested bound.
Spec.lean was left unchanged, with its exact original conjecture, sole import,
and sole sorry. No target proof or exact negation has been submitted.

## Bounded-multiplicity power refinement (VERIFIED, STILL RESTRICTED)

The original erdos_970 is STILL UNSOLVED. New file
Submission/BoundedMultiplicityPower.lean compiles and has a built olean.
All three final printed axiom audits contain only propext, Classical.choice,
Quot.sound. Log: /tmp/bounded_multiplicity_power.log.

Namespace Erdos970.BoundedMultiplicity:
- product_gt_of_cap: if every position of a length-m interval has at most d
  hits, then every (d+1)-element subset of the selected primes has product >m.
  This is an actual CRT statement, not an independent-population assumption.
- small_core_card_le: if a^(d+1)<=m, at most d selected primes are <=a.
- exists_sparse_power_cutoff: for every fixed 0<beta<=1 with log(1/beta)<1,
  there are fixed D>=2 and epsilon>0 such that any set of <=k primes has
  reciprocal tail <=1-epsilon above D*k^beta, uniformly for every k>0.
  All log-log and cardinality-tail errors are retained and absorbed into D.
- core_tail_linear: with at most d core primes and that reciprocal gap,
  m <= (d+1)*2^d*(k+1)/epsilon. The full core inclusion-exclusion cost is kept.
- exists_power_bound: when beta*(d+1)>=1, covers of multiplicity at most d
  satisfy m<=C*k^(beta*(d+1)); C may depend on fixed d,beta.
- log_eight_thirds_lt_one: exact rational log-series certificate, kernel checked.
- triple_cover_three_halves: choose beta=3/8,d=3 to obtain O(k^(3/2)).
- quadruple_cover_fifteen_eighths: beta=3/8,d=4 gives O(k^(15/8)).

This improves the earlier quadratic triple-cover estimate and adds a
subquadratic quadruple-cover estimate. It DOES NOT improve the unrestricted
upper bound at the header. Arbitrary covers in the conjecture have no fixed
multiplicity cap. No constant-factor or suitable polynomial-cost conversion
of arbitrary covers to these classes was proved. The already verified
constant-factor conversion obstruction for multiplicity TWO was rechecked;
it must not be overstated as an obstruction for every larger cap.

Initial compile errors were ordinary lambda-binder/coercion and arithmetic
normalization issues. They were repaired before the clean build and final
axiom audit. No sorry, admit, native_decide, or new axiom occurs in the file.
No numerical cover search or background worker remains.
Spec.lean is unchanged, preserving its exact statement, sole import, and sole
sorry at2177. No completed target proof or exact negation has been submitted.

## Unrestricted-weight review after multiplicity refinement (NO SETTLEMENT)

The original conjecture remains UNSOLVED. Re-read RadialProfileBarrier,
KernelSupportEnergyBound, PrimeSupportMassBarrier, the signed and Boolean
kernel-cost criteria, and the coupled global-weight examples. The existing
common-profile barriers were not overlooked: optimizing the radial profile
alone does not reach the quadratic threshold in that scheme. The nonradial
support-mass statement still requires its explicit support and tail premises;
it is not a barrier to every sieve method.

No uniform global Boolean coverage-polynomial estimate at m=C*k^2 was
obtained. The kernel-verified coupled-versus-first-hit separations use equal
marginals, not distinct-prime marginals, and cannot simply be transferred as
such. Also considered positive parity-box corrections to the independent
population; these form a strictly restricted class, as already verified in
ParityBoxObstruction. No argument treating those corrections as a universal
representation of every empty-free population was used.

No new Lean theorem or numerical run resulted from this review. The previous
BoundedMultiplicityPower results remain verified but restricted, and the best
unrestricted bound at the header is unchanged. Spec.lean was not altered:
original statement, sole import, and sole sorry at2177 are all preserved.
No completed target proof or exact negation has been submitted.

## Multi-position and shared-row review (NO SETTLEMENT)

The original erdos_970 is STILL UNSOLVED. Reviewed mixed-pattern rescaling,
joint deletion bounds, shared inverse row geometry, and using several nearby
candidate positions in one sieve certificate. No new Lean theorem or adequate
uniform quantitative estimate resulted. Exact one-prime exclusions across
different positions are valid, but independently bounding the rescaled rows
does not retain their shared phases. No independence or nonlinear association
of those rows was assumed. A fixed collection of offsets, by itself, did not
supply a remainder/main-term inequality at m=C*k^2.

No new computational scan or background worker was started. The verified
bounded-multiplicity estimates and the unrestricted bound at the header are
unchanged. Spec.lean still has the original statement, sole import, and sole
sorry at2177. No target proof or exact-negation theorem has been submitted.

## Sublinear-power dyadic loss reduction (VERIFIED, STILL CONDITIONAL)

The original erdos_970 remains UNSOLVED. New file
Submission/PowerLossDyadicVoidReduction.lean compiles with a built olean.
All four final printed axiom audits contain only propext, Classical.choice,
Quot.sound. Log: /tmp/power_loss_dyadic.log. No sorry, admit, native_decide,
or new axiom occurs in the file.

PowerLossDyadicVoidBound(A,alpha) is an explicitly UNPROVED hypothesis:
  for all prime sets P and all m>=|P|,
  V_P(2m) <= A*(|P|+2)^alpha*V_P(m)^2.
For fixed A>=1 and 0<=alpha<1, this weaker hypothesis still implies the
exact original quadratic conclusion. The loss need not be constant.

Verified ingredients:
- eventually_power_scaled_void_base: unconditionally, for A>0, alpha<1,
  eventually in k, uniformly for |P|<=k,
    A*(k+2)^alpha*V_P(k) <= exp(-(1-alpha)*log(k+2)/2).
  This uses the actual variance inequality, the cardinality-uniform Mertens
  density lower bound, and log(x)=o(x^eta). No doubling assumption is used.
- local_dyadic_iteration: iteration with a fixed local budget and multiplier.
- power_loss_dyadic_tail: conditional tail at lengths 2^j*k with exponent
    -(1-alpha)*2^j*log(k+2)/2.
- eventually_quadratic_of_power_loss_dyadic: for every fixed natural D with
  56<(1-alpha)*D, the dyadic hypothesis implies h(k)<=D*k^2 eventually.
  The full normalized-prime phase entropy is retained.
- quadratic_bound_of_power_loss_dyadic: patches finite budgets and concludes
  exactly the original existential real quadratic type, STILL CONDITIONAL.
- power_loss_zero_of_long_dyadic: the earlier constant-loss hypothesis is the
  alpha=0 special case.
- eventually_quadratic_of_sqrt_dyadic: even alpha=1/2 gives the eventual
  explicit constant128.

The simultaneous-hit/phase-alignment and bounded-multiplicity conversion
ideas were also reviewed, but no unrestricted bridge was proved. No proof of
the new doubling hypothesis, even for alpha=1/2, has been obtained. It must not
be promoted to an unconditional lemma. The strongest unconditional bound at
the header is unchanged, as are the earlier restricted multiplicity bounds.
No numerical cover search or computation worker remains active.

Spec.lean is unchanged, with original statement, sole import, sole sorry at2177,
and SHA256 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No original-conjecture proof or exact-negation theorem has been submitted.

## Initial first-hit model obstruction (VERIFIED, NOT A TARGET DISPROOF)

The original erdos_970 remains UNSOLVED. New file
Submission/FirstHitModelBarrier.lean compiles with a built olean. All four
final printed audits contain only propext, Classical.choice, Quot.sound.
Log: /tmp/first_hit_model_barrier.log. No sorry, admit, native_decide, or
new axiom occurs in that source. Its scratch CheckFirstHitModelBarrier.lean
has deliberate unknown-identifier API checks and is not a dependency.

This upgrades part of the historical continuous-normalizer numerical warning
to a rigorous analytic inequality, without assuming a uniform arithmetic
asymptotic or claiming a universal sieve barrier.

Namespace Erdos970.FirstHitModelBarrier:
- gamma_lower: Euler's constant >143/250, using the exact harmonic127
  lower bound and log128=7*log2.
- exp_gamma_lower: exp(Euler's constant)>177/100, using a finite Taylor sum.
- initial_profile_le_parabola: on 1<=u<=2,
    2u-1-u log u <= u-(u-1)^2/4.
- reciprocal_lower_le and reciprocalLower_integral: integration yields
    integral_1^2 1/(2u-1-u log u) >= (log2)/2+3/8.
- truncated_critical_excess: for E>=177/100,
    2*(E*(log2+integral_1^2 1/(2u-1-u log u))-3/2)-2 >1/125.
- model_initial_integral_lower: applies to a positive continuous G on[1/2,2]
  with G(u)<=u on[1/2,1] and G(u)<=2u-1-u log u on[1,2].
- critical_model_margin_negative: under those EXPLICIT model hypotheses,
  for E>=177/100 and every T>=0,
    2-2*(integral_(1/2)^2 (E/G(u)-1)+T) < -1/125.
- critical_gamma_model_margin_negative: the same with E=exp(Euler's constant).

Scope: this rules out a positive critical margin in this specified continuous
first-hit model, even before the nonnegative remaining tail. It is NOT a
proof that all sieves, all global Boolean certificates, or all possible
normalizer supports satisfy the model hypotheses. No arithmetic finite-prime
asymptotic identification was smuggled into the theorem. In particular this
is NOT a disproof of the original quadratic conjecture.

A theoretical diagnostic integral was evaluated in mpmath while selecting the
analytic envelope, not used as a proof dependency. At E=exp(gamma), the exact
initial-model expression is approximately2.1289233 before subtracting the
critical budget2. The final Lean proof uses only rational bounds, derivatives,
and exact interval integrals, not that floating-point value.

The greedy encoding and prime-insertion routes were also reviewed. No new
unrestricted extension/increment estimate followed. Consecutive old survivors
removed by a new prime may be one modulus apart; the present old-gap bound
does not control the sum of these gaps. The local reference search found no
applicable Jacobsthal theorem; DNS remains unavailable. No worker remains.

Spec.lean is unchanged: original statement, sole import, sole sorry at2177,
SHA256 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
The strongest unrestricted bound at the header is unchanged. No completed
proof or exact-negation theorem for the original target has been submitted.

## Shared-position and prime-marginal follow-up (NO SETTLEMENT)

The original erdos_970 remains UNSOLVED. Revisited SoftExposureTree,
SoftExposureLowTail, SoftQuadraticLowTail, LowCountCylinder,
FilteredExposureBarrier, CoverPhasePacking, JointDeletionBound, and the
coupled global Boolean certificates. No new Lean theorem or sufficient
unrestricted positional estimate was obtained in this continuation.

The exposure obstruction was kept explicit: if a retained core is below the
uniform partial-count depth and its filtered deletion budget is below that
count floor, the cover is already deterministically impossible. Enlarging
that core to evade the condition also enlarges its retained entropy; the
existing stretched-exponential tail does not beat it. No circular bootstrap
using the terminal cardinality, and no independence of shared residue rows,
was assumed.

The previous prime-marginal LP diagnostics were inspected rather than rerun.
For the sampled small prime sets they show equality within numerical error,
not a proof of equality for all primes. The verified strict separations still
use equal marginals. They cannot be transferred to distinct prime marginals
by the domination theorem, which only transfers successful sufficient bounds
in the appropriate direction. No uniform prime-marginal global certificate
at m=C*k^2 was found. The new FirstHitModelBarrier theorem was not overstated
as a barrier to all global Boolean or positional methods.

Possible near-quadratic refinements through sharper normalizer tails and
linear-sieve weights were considered, but no claim that exponent2+epsilon
implies an absolute exponent2 bound was made. No new numeric cover search or
solver run was started. A direct-IP DNS-over-HTTPS reference-access fallback
also timed out at both1.1.1.1 and8.8.8.8; no external result was retrieved.

Spec.lean remains unchanged, with exact original statement, sole import,
sole sorry at2177, and SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No background worker remains, and no target proof or exact-negation theorem
has been submitted. All previously verified auxiliary results retain their
stated restricted or conditional scope.

## Budget-aware one-hit dilution follow-up (NO SETTLEMENT)

The original conjecture is STILL UNSOLVED. Re-read the rounded-certificate
obstruction, interval-aware recursion, coupled rows, and long-interval
power-loss doubling reduction. No missing unconditional premise was found.

Reviewed the exact leading coefficient for adjoining t single-hit primes
above 2m. If a core phase has s survivors, the leading coefficient as the
new prime reciprocals tend to zero at comparable rates is (t)_s, not t^s.
Consequently, if the minimum core counts at m and 2m are s and 2s, with
frequencies f and g in period N, the leading dyadic ratio is
  N*g/f^2 * (t)_(2s)/(t)_s^2.
The long-interval cardinality constraint requires t<=m-|P|. This depletion
factor cannot be dropped in trying to transfer a Laplace counterexample.
No uniform theorem about the displayed ratio has been proved.

A targeted external exact-integer diagnostic, /tmp/long_dyadic_leading.py,
checked that necessary leading-coefficient mechanism for a few specified
small cores and lengths below 201. It found no ratio above one. This is NOT
a proof of long doubling, is NOT exhaustive over prime sets or lengths,
and is NOT a new Jacobsthal bound. No diagnostic output is a Lean dependency.

No new Lean theorem or adequate unrestricted estimate was obtained.
Spec.lean remains unchanged, preserving its exact statement, sole import,
and sole sorry. No completed proof submission or exact-negation theorem has
been produced. No computation worker remains active.

## Smaller-budget and bounded-overlap bridge review (NO SETTLEMENT)

The original conjecture remains UNSOLVED. Reviewed CardinalityBootstrap,
CardinalityBlockBootstrap, optimal-core exchanges, HighMultiplicityPacking,
QuadraticOverlapReduction, and BoundedMultiplicityPower. No quantitative
renormalization recurrence for the unrestricted Jacobsthal function was
proved. The repeated-block profit estimates do not by themselves close a
quadratic induction.

No conversion of arbitrary covers to multiplicity three or four with a
suitable controlled prime budget was found. The proven high-overlap estimates
still leave the moderate-mass term. The double-cover conversion obstruction
was not generalized to caps three or four without proof.

A simple continuous selected-pair integral was evaluated externally while
checking a possible bounded-multiplicity refinement; it yielded no target
estimate and is not a Lean proof dependency. No new Lean theorem, new
unrestricted bound, or counterexample family resulted from this review.
No worker remains active. Spec.lean is unchanged and retains its original
conjecture and sole sorry. No complete proof has been submitted.

## Eighteen-prime global moment diagnostic (NO SETTLEMENT)

Original erdos_970 remains UNSOLVED. A single new method-comparison diagnostic
was run, rather than a search for actual interval covers. The first eighteen
prime marginals gave recursive root 1280.0067141256077. A synthetic population
LP restricted to atom products <=1638418 gave threshold1280.0067141255888,
with233 positive atoms; all262144 moment errors passed the floating check.
The support restriction is not a restriction on the original conjecture.
Numerical agreement does NOT prove equality of methods in general.

Scripts:
  /tmp/run_global_moment18.py
  /tmp/global_moment_divisor_support.py (pre-existing solver script)
Log/data:
  /tmp/global_moment_divisor_support_18.log
  /tmp/global_moment_divisor_support_18_1638418.npz

A separate Python exact-integer check rounded the233 nonempty atom masses to
common denominator100000000 at total mass1279, corrected the total exactly,
and checked all262144 inequalities by integer cross multiplication:
  abs(momentNumerator*primeProduct -1279*denominator)
    <=denominator*primeProduct.
This data is /tmp/global_moment18_mass1279_exact.json; verification script
/tmp/check_global_moment18_exact.py. This is NOT Lean-checked, NOT an actual
prime-residue interval population, and NOT a conjecture disproof. None of the
solver or diagnostic output is imported into a Lean theorem.

The coupled equal-marginal examples and prime-block obstruction were also
reviewed. They supplied no new unrestricted certificate or arithmetic bridge.
No new Lean theorem or uniform quadratic estimate was obtained. The worker
finished; no solver remains active. Spec.lean remains unchanged, with its
original theorem/import and sole sorry. No completed proof was submitted.

## One-hit occupancy log-concavity and full-period doubling (VERIFIED, NO SETTLEMENT)

Original erdos_970 remains UNSOLVED. Two new files compile with built oleans:
  Submission/OneHitLogConcavity.lean (175 lines)
  Submission/OneHitPopulationDoubling.lean (204 lines)
Namespace Erdos970.OneHitLogConcavity. All final printed axioms are exactly
propext, Classical.choice, Quot.sound. Logs:
  /tmp/one_hit_logconcavity.log
  /tmp/one_hit_population_doubling.log

The coverage probability F(s) for s specified bins under independent one-hit
residue choices obeys the exact recurrence
  F_new(s)=((p-s)*F(s)+s*F(s-1))/p.
For moduli p>=M>=(all considered population sizes), this operator preserves
nonnegativity, monotonicity, F(0)=1, and log-concavity in s. The log-concavity
proof retains the nonnegative square term in an exact polynomial identity.
The resulting theorem is F(a+b)<=F(a)*F(b) for a+b<=M.
IMPORTANT: This is log-concavity in the number of REQUIRED BINS. It is NOT
log-concavity of the distribution of core survivor counts, which was refuted
in an earlier file.

population_eq_occupancy identifies F with the ACTUAL finite phase mean for a
population S inside [0,m), when every modulus p>=m. It uses one-point erasure,
not independent thinning of positions. disjoint_population_coverage proves
  Prob(S union T fully hit)<=Prob(S fully hit)*Prob(T fully hit)
for disjoint S,T in the same one-hit domain. No primality is needed for this
occupancy statement; positive distinct moduli and the size cap suffice.

constant_core_doubling assumes phase-independent core survivor counts s and
2s at lengths m and2m. It gives V_{P union R}(2m)<=V_{P union R}(m)^2 when every
tail modulus is at least2m. full_period_variance_zero and full_period_count
use the existing EXACT positive variance expansion to establish the constant
counts when product(P) divides m. Thus full_period_core_doubling proves the
actual inequality under the explicit restrictions:
  core P prime; disjoint P,R; product(P) divides m; all p in R positive and >=2m.
There is no cardinality restriction in this special theorem. It does not
contradict the previous unrestricted-doubling counterexample, whose small
core count is not phase-independent at its chosen interval lengths.

These restrictions cannot be silently imposed on an arbitrary cover. Neither
a bridge for intermediate moduli nor a relative nonlinear phase-averaging
bound for variable core counts was proved. The result DOES NOT establish
LongDyadicVoidBound or PowerLossDyadicVoidBound and DOES NOT settle Erdős970.
The full-period/one-hit class also admits a direct count bound; this new
negative-dependence fact must not be portrayed as an unrestricted improvement
of the best Jacobsthal exponent.

No conjecture proof or exact-negation theorem has been submitted. Spec.lean is
unchanged, with sole import FormalConjecturesUtil and sole sorry at line2177.
SHA256 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
The last build worker (PID153390) finished; no active worker needs resuming.

## Intermediate-modulus collision and induction review (NO NEW SETTLEMENT)

Continued after the one-hit/full-period doubling result. Re-read the actual
multi-prime exchange, high-multiplicity packing, repeated-block induction,
two-survivor insertion, and optimal-core prime-cap theorems. No simultaneous
row-load estimate strong enough at m=C*k^2 was obtained. In particular:
- bounded pairwise intersections control very high overlaps, not all remaining
  tail loads on an arbitrary sieved core;
- a smaller-budget gap bound does not itself give the missing terminal
  survivor count or an O(k) increment;
- one-hit negative dependence does not extend to classes that can hit both
  populations merely by citing their pairwise collision bounds;
- the full-period core condition cannot be imposed without changing m and
  losing control at the required uniform quadratic scale.

Also reviewed the existing ordering theorem and global Boolean majorant
comparison before considering them again. Increasing-prime order is already
optimal for the stated continuous envelope, not necessarily for every sieve.
The known strict global-majorant improvements use equal, non-prime marginals;
no new distinct-prime or asymptotic gain was proved. No additional numerical
search or Lean worker was launched in this pass.

No new Lean theorem, conjecture proof, or exact negation was obtained.
Spec.lean remains unchanged, sole sorry at2177, and no submission was made.

## Larger-budget global-moment comparison (EXACT DIAGNOSTIC, NO SETTLEMENT)

Original erdos_970 STILL UNSOLVED. No new Lean theorem in this pass.
Before considering dynamic prime orders, checked the previous subset recursion:
/tmp/interval_subset_orders.py ALREADY optimizes the last deleted prime separately
at each length/subset. Its small finite gains and lack of a closing induction
remain as previously recorded. No duplicate subset-order run was started.

New structured method-comparison diagnostic: previous distinct-prime global LP
comparisons used small reciprocal sums (first18 sum=1.713857...), whereas the
known equal-marginal global gains have sum2. Tested beyond that range, without
assuming that total reciprocal mass is a decisive criterion.

1. /tmp/global_harmonic_threshold.py, /tmp/global_harmonic11.log
   Denominators2,...,12 (NOT distinct primes), sum reciprocals2.1032106782.
   Full global Boolean moment LP threshold3415.589873314439. Independently
   optimized every prefix upper-weight LP at the same mass. Their summed
   first-hit objective was3415.589873314439, zero floating gap.
   Runtime about13.45s. This does NOT prove equality for a general marginal class.

2. /tmp/global_sparse60.py and /tmp/global_sparse60_v2.log
   FIRST SIXTY ACTUAL PRIMES, ending281, reciprocal sum2.0059088703115027.
   Reference raw unit-error first-hit recursion root18658.53885693103.
   Sparse row/column formulation, initial7066 small-product moment rows with
   cutoff37318,7428 candidate atom columns. Additional violated upper-moment
   rows were generated from actual positive support, with nonnegative-mass
   subtree pruning; the small-product rows handle all possibly violated lower
   moments. After30 solves,8396 rows and77898 incidence nonzeros:
      epsilon=5.359476471698822e-5
      threshold=18658.538856931013
      positive atoms3809
      no remaining floating moment violations.
   Total runtime135.81s. No pricing MILP was needed or called: a feasible
   population matched the reference threshold directly. Data:
      /tmp/global_sparse_60.npz
   The first attempt used more high-degree random columns and hit its180s LP
   timeout; it gave NO completed certificate. Its logs/source are retained as
   /tmp/global_sparse60.log and /tmp/global_sparse60_v1.py. The successful
   version used fewer initial atoms and HiGHS IPM. Nothing was kernel-trusted.

3. Independent exact-integer check:
      /tmp/check_global_sparse60_exact.py
      /tmp/global_sparse60_mass18657_exact.json
   Rounded atom masses to denominator10^10, set total mass exactly18657,
   verified all3809 nonempty atom weights nonnegative. All nonempty moments
   obey |moment -18657/product(T)|<=1 by integer cross multiplication.
   Two validation routes were used:
   - all4262 small-product moments plus7447 upper-bound recursion nodes;
   - direct accumulation of EVERY subset of every positive atom:8017 distinct
     nonzero moments, maximum atom degree8, plus all4262 small-product moments.
     All omitted moments are zero and have product>18657, so their error<1.
   The second check is entirely finite exact integer arithmetic after the
   rational table is constructed. It does not enumerate the2^60 Boolean cube.

CRITICAL SCOPE: This is a SYNTHETIC WEIGHTED BOOLEAN POPULATION, not an actual
prime-residue interval cover. The exact table has NOT been Lean-checked. It
is NOT a disproof of Erdős970, nor a theorem of global/first-hit equality, nor
an asymptotic obstruction to every sieve. The numerical equality at the
noninteger root remains numerical; the exact population has mass18657.
None of this data or solver output is imported by a Lean theorem.

The larger-budget comparison found no new global-weight gain. Spec.lean is
unchanged, original sole import and theorem type, sole sorry at2177; no proof
or exact-negation theorem has been submitted. All workers have finished.

## Fourier normalization and positive-variance shortcut (VERIFIED, NO SETTLEMENT)

Original erdos_970 STILL UNSOLVED. No conjecture proof or exact-negation
proof has been submitted. Spec.lean is unchanged with its sole import and
sole sorry at2177. SHA256 remains
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.

Four NEW compiled files, with built oleans and final printed axioms only
propext, Classical.choice, Quot.sound:

1. ResidueFourierVariance.lean (202 lines), namespace Erdos970.Resampling.
   Log /tmp/residue_fourier_variance.log.
   - residueFourier(S,p,a) is sum_{x in S} stdAddChar(x*a) on ZMod p.
   - residueFourierEnergy sums its squared norm at NONZERO frequencies.
   - residueFourier_normSq_sum: total Fourier energy is p times the sum
     of squares of the residue-class loads.
   - residueFourierEnergy_eq: nonzero energy E_p = p^2*classVariance(S,p).
     The weight is p^2, NOT p.
   - selected_centeredHits_sq_le_energy: p*(one chosen discrepancy)^2<=E_p.
   - selected_centeredHits_sum_sq_le_energy:
       (sum chosen discrepancies)^2 <= (sum 1/p)*(sum E_p).
   - cover_energy_lower: when mu=sum1/p<=1 and S is covered,
       (|S|*(1-mu))^2 <= mu*(sum E_p).
   - variance_sum_le_energy_div_sq: for all p>=y>0,
       sum V_p <= (sum E_p)/y^2.
   - populationCoveredFraction_fourier_bennett rewrites the existing
     conditional Bennett bound with E_p/p^2, retaining actual conditional
     populations, distinct caps, and all modulus weights.
   These are EXACT identities/transfers. A classical large-sieve inequality
   has NOT been formalized or smuggled in as a premise-free result.

2. PositiveRectangularVariance.lean (80 lines), Erdos970.GapAverages.
   Log /tmp/positive_rectangular_variance.log.
   - positiveRowVariance = residueMean(max(rowCount-totalCount/p,0)^2).
   - UniformPositiveRectangularCubeBound(C) explicitly asserts, for primes
     p above every old prime and ALL n>=p and old phases,
       positiveRowVariance(P,p*n,p,r)^3 <= C*n^4.
   - roughCount_upper_of_positive_variance_cube: iterating ONLY the
     positive zero-row deviations bounds roughCount(P,n) from above by
     n*density(P)+2D whenever p^3*C*n^4<=D^6, p>=8, and the cube bound
     holds at every larger rectangle n*p^j. The limiting density is proved
     using finite inclusion-exclusion for the FIXED core P, not PNT.

3. PrimeCountingLeadingObstruction.lean (195 lines), Erdos970.PrimeLeading.
   Log /tmp/prime_leading_obstruction.log.
   - sum_mul_le_of_prefix_le: Abel comparison for decreasing positive weights.
   - weighted_primeSum_le_of_theta: theta(n)<=c*n+D for all n implies
       sum_{p<=n}log(p)/p <= c*H_n+D.
   - not_eventually_primeCounting_leading: for 0<=c<1, it is impossible
     eventually that pi(n)*log(n)<=c*n. This uses elementary weighted
     Mertens, NOT the prime number theorem.
   - eventually_le_of_power_subsequence: monotone polynomial-subsequence
     bounds with coefficient c imply eventual bounds with any c'>c>=0
     (the theorem actually only needs c'>=0).
   - not_eventually_theta_power: for any fixed positive integer d and
     0<=c<1, theta(t^d)<=c*t^d cannot hold eventually.

4. PositiveRectangularVarianceDisproof.lean (163 lines), Erdos970.GapAverages.
   Log /tmp/positive_rectangular_disproof.log.
   - prime_prefix_density_three_fifths:
       density(primesBelow p) <= (3/5)/log p
     for prime p and log p>=30*firstHitProfileError. It follows from the
     EXISTING cubic normalizer lower bound and profile(3)>=17/10; no sharp
     Mertens-product asymptotic is required.
   - prime_count_power_of_positive_cube: the positive-part cube proposal
     with C>=1 forces, for t large enough,
       pi(t^48)*log(t^48) <= (24/25)*t^48
                              +48*(4C+2)*t^47*log t.
     Choose prime p in (t^30,2*t^30], core all primes below p, n=t^48.
     The iterated positive deviation bound has D=2C*t^47. Below p^2,
     rough survivors are exactly 1 and primes >=p. Thus it gives the
     displayed coefficient below one for prime counts.
   - not_uniformPositiveRectangularCubeBound(C) proves the NEGATION of
     that AUXILIARY proposal for EVERY real C. The lower-order term is
     eventually <=t^48/50, giving theta coefficient49/50 and contradicting
     PrimeCountingLeadingObstruction. This is a fully kernel-checked
     disproof, not the previously discussed unproved Buchstab heuristic.

The positive-part disproof uses a zero phase (so 1 always survives) and
an unrestricted n>=p hypothesis. It is NOT a cover construction, NOT a
counterexample to the original conjecture, and NOT a disproof of every
possible low-population-restricted or p-dependent variance estimate.

Analytic review before these files (NOT new formalized theorems):
- The classical additive large sieve would give schematically
    sum_{p<=Q} p^2 V_p <= (m+Q^2)|S|,
  hence on Y<=p<=2Y, sum V_p <= (m+4Y^2)|S|/Y^2.
  Mathlib search found no ready large-sieve theorem. The precise Parseval
  normalization is now checked, but the large-sieve bound itself is not.
- A naive fixed-block, common-cap Bennett assembly with a union bound over
  prefix phases retains a critical-constant loss: multiplicative block
  ratio tau produces tau/log(tau)>=e. The rough excess-loss coefficient
  near the critical cutoff is about2e, against lower-sieve slope about2.
  This is only an asymptotic diagnostic of that assembly, NOT a general
  impossibility theorem. Nonuniform caps/tilts/global exposure were reviewed
  but yielded no closing estimate.
- LargestPrimeIncrement and its higher-count implications remain unproved.
  No duplicate prime-gap or subset-recursion scan was run.

The new files contain no sorry. CheckResidueFourier.lean and
CheckPrimeLeading.lean are scratch API queries with intentionally unknown
names; they are not imported by any proof. All Lean builds have finished.

## Full-centred high-moment shortcut DISPROVED (VERIFIED, NO SETTLEMENT)

Original erdos_970 STILL UNSOLVED. Spec.lean is unchanged, same original
statement/import and sole sorry at2177. SHA256 remains
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.

After checking the full-cover exchange/CRT constraints, the nonlinear
core-tail average, positional packing, and old high-moment discussion,
no new uniform cover-excluding inequality was obtained. No old cover search,
LP, recursive-order scan, or numerical worker was repeated.

The old high-central-moment caution at lines5035ff was only an on-paper
PNT/sharp-Mertens obstruction for the first k primes and order greater than2k.
The following NEW results are elementary and kernel-checked, and address
arbitrary prime sets and order exactly twice the actual cardinality.
They do NOT settle the original conjecture.

1. QuadraticCountMomentObstruction.lean (190 lines), Erdos970.GapAverages.
   Log /tmp/quadratic_count_moment.log; built olean.

   UniformQuadraticCountMoment(C) is the explicit proposal
     for every k>0, prime set P with |P|<=k, and m>=k^2,
       E_P |S_m - m*density(P)|^(2k) <= (C*k*m)^k.
   The right side deliberately OMITS density(P), so is MORE LENIENT than
   the usual Gaussian-shaped (C*k*m*density(P))^k proposal.

   - value_le_phaseMean_mul_product extracts a single phase's contribution.
   - primesBelow_product_le_four uses the elementary primorial<=4^y bound.
   - moment_count_discrepancy: for t>=1, core P=primesBelow(64*t^6),
     |P|<=t^6, and t^12<=m<=4096*t^12, the proposal forces
       |roughCount(P,m)-m*density(P)| <= 4^32*64*C*t^9  (C>=1).
     The moment order is2*t^6. The core's whole phase product is at most
     4^(64*t^6), so its contribution can be extracted at constant root cost.
   - eventually_small_prime_core: |primesBelow(64*t^6)|<=t^6 eventually,
     using only prime-counting density tending to zero.
   - prime_recurrence_of_quadratic_moments compares m=t^12 and4096*t^12.
     Both are below the square of the SAME core cutoff. Rough counts are
     exactly prime counts plus1, and the density cancels. The result is
       4096*pi'(t^12)-pi'(4096*t^12)
          <= (4097*(4^32*64*C)+262080)*t^11.
     (The t^9 error is deliberately enlarged to t^11.)
   - not_uniformQuadraticCountMoment(C) proves this proposal FALSE for
     EVERY real C, using the existing elementary power-saving prime-counting
     recurrence obstruction along t=2^j. No PNT is used.

2. CountMomentPadding.lean (211 lines), Erdos970.GapAverages.
   Log /tmp/count_moment_padding.log; built olean.

   - population_large_deletion_budget: if S is in [0,m) and every new
     modulus is>=m, adjoining R loses at most |R| survivors, in EVERY phase.
   - joined_count_bounds and joined_mean_bounds preserve this same interval
     [0,|R|] for the loss of the count and for the loss of its mean.
   - joined_centered_abs_le: an old absolute centred deviation is at most
     the corresponding joined deviation plus |R| (not an independence claim).
   - centered_moment_padding, for arbitrary natural d:
       M_d(P,m) <= 2^d*(M_d(P union R,m)+|R|^d),
     where M_d is the actual phase average of the absolute centred moment.
     This uses the exact independent phase-space union equivalence.

   UniformExactQuadraticCountMoment(C) uses the ACTUAL k=|P|>0:
     for every prime set P and m>=|P|^2,
       E_P |S_m-m*density(P)|^(2|P|) <= (C*|P|*m)^|P|.
   - exact_count_moment_to_budget: for C>=1, this exact-cardinality premise
     would imply UniformQuadraticCountMoment(8*C). Pad P to k primes with
     k-|P| fresh primes>=m; the additive padding error is absorbed using
     k^2<=m. All new moduli are genuinely distinct primes.
   - not_uniformExactQuadraticCountMoment(C) disproves the exact-cardinality
     proposal for EVERY C as well.

Combined audit: Submission/CountMomentObstructionAudit.lean;
/tmp/count_moment_obstruction_audit.log. Every printed axiom list contains
only propext, Classical.choice, Quot.sound. Both new proof files have no sorry.

SCOPE: The proposed uniform statement ranges over m>=k^2. The contradiction
uses the two quadratic multiples1 and4096 before padding. No theorem that
EACH prescribed fixed multiple separately refutes the proposal was claimed.
These results concern FULL-CENTRED absolute moments. They do NOT refute
moments truncated below a small fraction of the mean, other lower-tail
statistics, every fixed-order moment bound, or Erdős970. The first-k-prime
near-critical-order issue is also not silently resolved by the arbitrary-set
padding construction.

The original task still requires an unrestricted quadratic survivor bound
or genuine superquadratic consecutive covers. Neither has been obtained.
No submit_proof call was made. All workers have finished.

## Endpoint conditioning and insertion recheck (NO SETTLEMENT)

The original erdos_970 remains UNSOLVED. No Lean source was changed in this
pass, and no new theorem or numerical diagnostic was produced.

Checked WeakSoftEndpointReduction, QuarterLaplaceObstruction,
SoftEndpointHazardLimit, BudgetSoftEndpoint, SoftEndpointDerivative, and the
later finite-thinning results. The quarter example obstructs dyadic Laplace
submultiplicativity at log 2, not every fixed sufficiently small parameter.
CriticalSoftEndpointBound and DensityPowerSoftEndpointBound remain explicit
unproved hypotheses. Conditioning on endpoint survival changes whole residue
rows; the untilted variance estimates do not control those changes under the
Gibbs weight. No such substitution was made.

Rechecked IncrementReduction, IncrementCountConsequences, and
LargePrimeCountReduction. The largest-prime increment implies a global
higher-count hierarchy. Neither the existing local isolation examples nor
reflection of adjacent gaps proves or disproves that hierarchy. Earlier
primorial and odd-prime adjacent-gap scans were NOT repeated.

Also rechecked the overlap reductions. "Double cover" in
DoubleCoverQuadratic is the UPPER multiplicity restriction H<=2, not the
assertion H>=2. It cannot be used to infer plentiful private positions in
an arbitrary cover. BoundedMultiplicityPower retains an explicit cap.

Spec.lean is unchanged, with the original statement/import and sole sorry.
No purported completed proof or exact-negation theorem was submitted.


## Normalizer-sensitive first-hit remainder (VERIFIED, NO SETTLEMENT)

The original erdos_970 remains UNSOLVED. Four new files compile with built
oleans. Their final printed axiom audits contain only propext,
Classical.choice, Quot.sound. No sorry/admit/native_decide/new axiom occurs
in these files. The original conjecture is not a dependency of the results.

1. FirstHitSharpTransfer.lean
   - ordinaryCoefficient_canonical_eq identifies the two coefficient APIs.
   - firstHitCoefficient_cost_eq gives exactly
       1 + sum_i kernelCost(canonical_i)^2.
   - survivor_of_dominating_first_hit_cost transfers reference marginals
     with that actual cost, instead of replacing every coefficient by one.
     Its numerical certificate inequality remains an explicit hypothesis.

2. FirstHitNormalizedCost.lean
   - primeNormalizer_strict_log_lower: for prime p and R>0 with
     log R >= (log p)/2, the strict-prefix normalizer is >= (log p)/4.
     This uses a harmonic lower bound at min(R,p), strict-prefix removal,
     and cutoff monotonicity; no asymptotic hypothesis is needed.
   - prime_canonical_cost_le_of_subset extends the already verified
     exp(2)*R/G coefficient bound to supports contained in divisorSupport.
   - prime_inv_log_square_sum_le bounds sum_P 1/(p log(p)^2) by the absolute
     constant 4+16*(WeightedMertens.boundConstant+1). The prime 2 endpoint
     is included explicitly; the tail uses inverseLogPrimeInterval at n=1.
   - saturated_reference_normalized_cost: total squared reference costs
     <= A*exp L, with fixed A=64*exp(4)*inverseLogSquareConstant.
     Indeed each term is <=64*exp(4)*exp(L)/(p log(p)^2).

3. FirstHitNormalizedSurvivor.lean
   - The verified saturated main-term slack plus
       200*L*(1+A*exp L) < m
     implies IsJacobsthalBound k m, provided the cutoff contains the first
     k primes. Reference-to-actual transfer uses the sharp cost theorem.

4. FirstHitNormalizedLogPower.lean
   - exists_normalizedHit_logpower_bound proves, unconditionally,
       exists C>0, forall k>0,
       h(k) <= C*k^(54/25)*log(k+2)^(79/25).
   - This removes the prior log-log factor. It is NOT a quadratic bound.

Logs:
  /tmp/first_hit_sharp_transfer.log
  /tmp/first_hit_normalized_cost.log
  /tmp/first_hit_normalized_survivor.log
  /tmp/first_hit_normalized_logpower.log
Intermediate compile errors were repaired. The cost file has only two
harmless unnecessarySeqFocus warnings in its final build.

Before this construction, the budget-aware one-hit issue was reviewed.
The falling-factorial depletion factor cannot be dropped when the number
of added primes is at most the interval length. Earlier diagnostics were
not repeated, and no restricted dyadic theorem was claimed.

POSSIBLE NEXT REFINEMENT (NOT YET FORMALIZED): use two different reference
cutoffs. For p<=exp(L/100), use firstHitCutoff (L/2) p; for larger p use the
old firstHitCutoff L p. The small-prime main-term increase can potentially
be bounded by far_normalizer_excess_le and the seventh prime log moment,
with an exact fixed wheel handling bounded primes. The threshold log p<=L/100
makes its leading constant far smaller than the current 1/(200L) slack.
The small-prime squared cost would be O(exp(L/2)); the large-prime cost
could use the inverse-log-square tail above exp(L/100) to give
O(exp(L)/L^2). Since L^2<=8*exp(L/2) for L>=0, the total would have that
latter scale. If assembled, this would yield roughly
k^(54/25)*log(k+2)^(29/25), still NOT the quadratic target. Do not treat this
planned refinement as a theorem; none of its new two-cutoff assembly has
been formalized. The previously verified first-hit model barrier still
prevents simply rounding the base exponent down to two.

Spec.lean is unchanged: original statement, sole import, sole sorry at2177,
SHA256 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No complete target proof or exact-negation theorem has been submitted.
No background solver or Lean build remains active.


## Two-cutoff logarithmic saving completed (VERIFIED, NO SETTLEMENT)

Original erdos_970 STILL UNSOLVED. The two-cutoff idea recorded in the previous
entry has now been assembled into an UNCONDITIONAL bound, not merely a
conditional main-term estimate. The base exponent remains 54/25=2.16.

New compiled files, namespace Erdos970.FiniteSelberg:
- FirstHitTwoScaleDefs.lean (85 lines)
- FirstHitTwoScaleMain.lean (135 lines)
- FirstHitTwoScaleCost.lean (133 lines)
- FirstHitTwoScaleSurvivor.lean (94 lines)
- FirstHitTwoScaleLogPower.lean (105 lines)
- FirstHitTwoScaleAudit.lean (8 lines; audit file)

Definitions:
  twoScaleParameter L p = L/2 if log p<=L/100, and L otherwise;
  twoScaleCutoff L p = firstHitCutoff (twoScaleParameter L p) p;
  twoScaleSmallCut L = floor(exp(L/100));
  twoScaleMainSum is the actual reference first-hit sum over primes below
  the same saturatedHitPrimeCut L 0 as before.

Main-term argument:
- primeNormalizer_le_eulerMass and firstHitMeanExcess_nonneg retain the
  full positive Euler-product baseline.
- twoScaleMainSum_le bounds the new sum by the old sum plus the complete
  small-prime excess at parameter L/2.
- twoScale_small_excess_bound bounds that extra sum by
      1/(10000L) + WeightedMertens.sharpMomentError/L^2.
  The existing eighth-power pointwise tail and seventh prime log moment
  are used with log p<=L/100. A fixed finite wheel is treated exactly, not
  absorbed into an unstated asymptotic error.
- exists_twoScaleMainSum_slack supplies L0>=100 and, for all L>=L0,
      twoScaleMainSum L <= 1-1/(400L).

Cost argument:
- reference_canonical_cost_at_scale extracts the pointwise normalized cost
  for any scale T satisfying 2 log p<=T.
- prime_inv_log_square_tail proves the reciprocal-log-square tail bound
  <=inverseLogSquareConstant/log(a)^2 for all selected primes above a,
  under a>=2 and log(a)>=1.
- The small-prime squared costs sum to O(exp(L/2)). The remaining squared
  costs sum to O(exp(L)/L^2), retaining the actual normalizer denominators.
- exp_half_le_exp_div_square uses only the quadratic lower bound on exp
  to prove exp(L/2)<=8 exp(L)/L^2.
- twoScale_reference_cost therefore bounds the complete squared cost by
      twoScaleCostConstant*exp(L)/L^2,
  where twoScaleCostConstant=10008*normalizedFirstHitCostConstant.

Assembly:
- isJacobsthalBound_of_twoScale uses the verified main slack, sharp
  reference-marginal transfer, and budget
      400L*(1+twoScaleCostConstant*exp(L)/L^2) < m.
- exists_twoScale_logpower_bound proves the NEW BEST unconditional theorem
      exists C>0, forall k>0,
      h(k)<=C*k^(54/25)*log(k+2)^(29/25).
  The extraction retains division by L and uses k+2<=nthPrime(k), rather
  than discarding that logarithmic saving.

Clean final logs:
  /tmp/two_scale_defs.log
  /tmp/two_scale_main.log
  /tmp/two_scale_cost.log
  /tmp/two_scale_survivor.log
  /tmp/two_scale_logpower.log
  /tmp/two_scale_audit.log
Final axiom audits contain ONLY propext, Classical.choice, Quot.sound.
There are harmless unused-variable/unnecessarySeqFocus warnings in two
files, no remaining errors. Intermediate failed builds were repaired.
CheckTwoScale.lean is an API scratch file, not a dependency.

LIMITATION: This modification shortens cutoffs only for log p<=L/100. It
changes the far small-prime range, not the initial u in [1/2,2] profile
appearing in FirstHitModelBarrier. That verified obstruction cannot be
removed merely by these improved costs or by rounding 54/25 down to two.
No unrestricted dyadic/endpoint estimate or new positional cover constraint
sufficient for the exact target has been proved in this pass.

Spec.lean remains unchanged, with its original statement, sole import, and
sole sorry at2177. SHA256:
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed proof or exact-negation theorem of erdos_970 was submitted.
No Lean build, solver, or diagnostic worker is left running.

## Smaller-budget and optimal-core continuation after two-cutoff bound (NO SETTLEMENT)

Original erdos_970 STILL UNSOLVED. Rechecked CardinalityBootstrap,
CardinalityBlockBootstrap, OptimalCoverCore, OptimalCoreGapCap, and
OptimalCoreExchange. No new Lean theorem was produced in this pass.

The smaller-cardinality count lower bound j+1-|P| is still at most the
remaining prime budget in a proposed induction. Repeated blocks improve
that count but retain their proved profit/length cost. These facts are not
an unrestricted quadratic induction step. The already documented dynamic
child-feedback issue was not silently replaced by the fixed-cost terminal
redundancy theorem.

Optimality supplies two private positions per retained prime, injectivity
of unused primes on the remaining population, and prime caps involving
h(|P|-1)*(survivors+1). None proves the existence of an improving exchange
or a quantitative sufficient supply of survivors. In particular, a positive
survivor population in every optimal core was not assumed.

Reviewed possible refinements through Boolean coefficient merging and
cutoff profiles. No new uniform arithmetic cancellation estimate was
proved. The already verified two-cutoff result retains base exponent54/25;
no assertion that better logarithmic factors imply exponent2 was made.
No numerical scan, optimizer, or background computation was launched.

Spec.lean remains unchanged with its original statement/import and sole
sorry at2177. No completed target proof or exact-negation theorem was
submitted. Best unconditional theorem remains exists_twoScale_logpower_bound
in FirstHitTwoScaleLogPower.lean, with power54/25 and logarithmic power29/25.

## Complete-coverage and private-spacing continuation (NO SETTLEMENT)

The original erdos_970 remains UNSOLVED. No new Lean theorem was asserted in
this review, and Spec.lean was not changed. Its sole sorry is still at line2177.

Rechecked EssentialCoverOrder, EssentialCoverProbability, CompetingCoverFibers,
CompetingCoverVariance, PrimeCoverResampling, JointDeletionBound,
OptimalCoreExchange, OptimalCoreGapCap, UniqueGreedyCoverOrder, and the
separated-pattern/overlap results. In particular:

- Greedy factorial/permutation encoding is ALREADY proved; it is not a new
  exclusion of complete covers. Private normalized representatives can even
  force a unique order, as the existing examples show.
- The exact single-prime insertion fibre retains the concentration term.
  Aggregate candidate-prime restrictions do not bound it adequately for one
  prescribed prime; singleton old populations remain an explicit exception.
- Deleting a prime from a full cover leaves its private positions in one
  residue class. Two such positions give the existing gap-based prime cap
  (and parity can double that cap). This is not a lower density estimate for
  the erased-prime survivor set.
- Joint deletion/count identities, optimal exchange inequalities, and
  two-cover CRT packing still require stronger information about the actual
  smaller-core survivor populations. No improving quadratic recurrence was
  established.
- Lower-tail resampling cannot discard the private-position contribution.
  The true zero-survivor example in PrimeCoverResampling still has a nonzero
  conditional resampling second moment. No replacement of conditional row
  data by unconditional averages was used.

Also considered small-prime-core/tail decompositions and spatially coupled
cover constraints. The elementary bounds reviewed do not yield the missing
uniform low-count estimate at quadratic interval length. This is a report of
an unsuccessful approach, not a theorem ruling out other methods.

The best verified unrestricted estimate is unchanged:
  h(k) << k^(54/25) * log(k+2)^(29/25),
from FirstHitTwoScaleLogPower.lean. Since54/25>2, it does not imply the target.
No target proof, exact-negation theorem, or completed submission was produced.

## Exact recursive-envelope shape (VERIFIED, NO SETTLEMENT)

New file Submission/RecursiveEnvelopeShape.lean compiles and has a built olean.
Log: /tmp/recursive_envelope_shape.log. Its four final axiom audits contain
only propext, Classical.choice, Quot.sound. No sorry, admit, native_decide, or
new axiom occurs in this file. CheckRecursiveShape.lean is a nondependency API
scratch file with deliberately failing queries.

Namespace Erdos970.RecursiveSieve. Results hold over any linearly ordered field
with valid marginals 0<=q_i<=1 and nonnegative input mass x:

- prefixDensity_first_hit: exact algebraic density identity.
- linearEnvelope_density_bounds:
    L_k(x) <= x*prod_(i<k)(1-q_i),
    U_k(x) >= 1+x*prod_(i<k)(1-q_i).
  In particular every upper child is at least1.
- linearEnvelope_lower_eq_max: the evaluator's pruning branch x<=k+1 is
  mathematically redundant under these hypotheses; its unpruned lower
  expression is then nonpositive.
- linearEnvelope_lower_second_order: the EXACT second-order recurrence
    L_k(x) = max(0,
      x*(1-sum_(i<k) q_i)-k-1
      +sum_(j<i<k) L_j(x*q_i*q_j)).
  This retains the root unit error. The earlier floating-point implementation
  used this form, but this identity is now kernel checked independently.
- linearEnvelope_lower_convex: L_k is convex on [0,infinity).
- linearEnvelope_lower_scale: c*L_k(x)<=L_k(c*x) for c>=1 and x>=0.
- linearEnvelope_lower_monotone: L_k is nondecreasing on [0,infinity).

Initial compile issues were an implicit Fin-sum rewrite and an untyped
intermediate tactic expression. They were repaired before the successful
build. Remaining warnings are harmless unused typeclass-section variables.

Scope: these exact identities and shape properties justify analysis and
scaling of existing certificates for a FIXED budget. They do not prove a
uniform certificate at m=C*k^2, do not compare different budgets, and do not
upgrade the previous numerical threshold diagnostics to asymptotic theorems.
No squared-prime uniform positivity estimate was established in this pass.
The original conjecture and its negation remain unproved.

The best unrestricted bound remains the two-cutoff bound at the header.
Spec.lean is unchanged, with the original statement/import and sole sorry.
No completed target proof or exact-negation theorem has been submitted.


## Density-normalized recursive sources and within-model redundancy (VERIFIED)

The original erdos_970 remains UNSOLVED. This batch was developed in the previous
context; the final untyped-lambda error in RecursiveSourceRedundancy.lean has now
been repaired. Its build and all four final axiom audits are clean. The other
seven files had already compiled. All final audits use only propext,
Classical.choice, Quot.sound. None of these new files uses sorry, admit,
native_decide, or a new axiom.

New development files:
- BoostedMixedAffine.lean: exact virtual-hit survival ratio for mixed patterns;
  affine lower sources transfer with the ratio prod_B(1-q')/prod_B(1-q).
- MixedCardinalityAffine.lean: already-valid budget-j length-g bounds give the
  affine survivor source ((j+1-|B|)/g)*n-(j+1-|B|), and its CRT mixed form.
- ReferenceCardinalitySource.lean: actual source transfer to reference primes
  WITH a density discount, including an explicit smaller-quadratic hypothesis.
- DensityNormalizedCardinality.lean: fill only missing reference primes, average
  their phases, and obtain a density-normalized source. No disjointness between
  added reference primes and required-hit primes is needed after rescaling.
- UndiscountedReferenceSource.lean: cancellation of the exact boost survival
  factor. The uniform gain is j+1-2|B|, NOT j+1-|B|. The second charge is retained.
- SeededRecursiveSieve.lean: a genuinely recursive, source-augmented first-hit
  sieve and its soundness theorem at every reachable prefix/intersection node.
- SeededReferenceTransfer.lean: end-to-end arbitrary-prime IsJacobsthalBound
  criterion from positive first-prime seededEnvelope, with every source bound
  an explicit hypothesis. This is not a proved uniform positivity statement.
- RecursiveSourceRedundancy.lean: positivity at prefix j yields
      (j-i)+L_j(x) <= L_i(x), i<=j.
  Convex scaling then shows that double-core affine sources whose own bounds
  have positive certificates in the SAME plain envelope are dominated by it.
  The seededLinearEnvelope equals the plain envelope recursively under this
  domination hypothesis. This is not blanket redundancy of arithmetic sources.

Logs: /tmp/boosted_mixed_affine.log, /tmp/mixed_cardinality_affine.log,
/tmp/reference_cardinality_source.log, /tmp/density_normalized_cardinality.log,
/tmp/undiscounted_reference_source.log, /tmp/seeded_recursive_sieve.log,
/tmp/seeded_reference_transfer.log, /tmp/recursive_source_redundancy.log.

Still missing: uniform positivity at m=C*k^2, or a genuine superquadratic cover
family. The numerical seededLinearEnvelope has not yet been identified formally
with the set-indexed seededEnvelope. No assertion about the old integer interval
bootstrap follows without additional hypotheses. No new numerical worker was
launched. Spec.lean is unchanged and still contains its original sole sorry.


## Exact union sources, density scaling, and full same-model closure (VERIFIED)

Original erdos_970 STILL UNSOLVED. Eight new mathematical development files and
one combined audit file compile, with built oleans. All final printed axiom
audits contain only propext, Classical.choice, Quot.sound. Intermediate errors
were repaired. No sorry/admit/native_decide/new axiom occurs in these new files.

1. UnionNormalizedCardinality.lean
   - survivor_union_floor_lower keeps EXACTLY
       floor(m/g)*(j+1-|P union Q|) <= density(Q minus P)*survivorCount(P,m).
   - survivor_union_affine_lower is its affine version.
   - density_union_cross identifies density(P)*density(Q minus P) with
     density(Q)*density(P minus Q).
   - mixedCount_union_normalized_affine_lower rescales required-hit
     progressions and retains the inverse density(P minus Q) factor.
   All statements assume an already valid IsJacobsthalBound j g.

2. UnionReferenceSource.lean
   - unionSourceGain(p,v,B,j) =
       (j+1-|image(p,B) union image(v,B)|) / density(image(p,B) minus image(v,B)).
   - prime_mixed_union_normalized_source and union_reference_cardinality_lower
     transfer the exact gain through virtual OR hits, with no density loss.
   - If p=v, unionSourceGain_self gives j+1-|B|, not j+1-2|B|.
   - These are improved CONDITIONAL source formulas, not new unconditional
     positive numerical certificates.

3. RecursivePositiveScaling.lean
   - linearEnvelope_positive_scale:
       c*L_k(x)+(c-1)*(k+1) <= L_k(c*x), for c>=1 and L_k(x)>0.
     The negative root intercept is retained, beyond ordinary convex scaling.
   - affineSource_le_of_plain_positive: at i<=j, a source length g with
     L_j(g)>0 dominates any max(0,t/g*(x-1)-t) with 0<=t<=j+1.
   - affine_seeded_eq_plain_of_plain_certificates is the recursive equality.

4. SeededEnvelopeBridge.lean
   - seededLinearEnvelope_congr: only marginals below k are accessed.
   - seededLinearEnvelope_eq_seededEnvelope bridges the real scalar and
     set-indexed recurrences exactly.
   - seededReferencePositive_iff_linear connects the existing arbitrary-prime
     reference criterion to scalar evaluation.
   - seededReferencePositive_iff_plain_of_plain_certificates transfers the
     previous double-core redundancy theorem to the set-indexed criterion.

5. UnionSourceRedundancy.lean
   - density_card_lower: a-|R| <= a*density(R) if all primes in R are >=a.
   - unionSourceGain_le_budget: the exact gain is <=j+1 if every missing actual
     prime is >=j+1.
   - unionSource_le_of_plain_certificate applies the positive scaling theorem
     in this range. The large-prime assumption is REMOVED in file8 below;
     this intermediate theorem remains valid but is not the final scope.

6. UnionSeededTransfer.lean
   - unionBlockSource defines the overlap-aware affine source at a prefix.
   - survivor_from_union_sources: end-to-end sound set-indexed recursion for
     arbitrary actual/reference prime lists, with explicit valid-source and
     positive-envelope hypotheses.
   - survivor_from_linear_union_sources is the scalar-form version.
     It is a criterion, NOT a proved uniform quadratic positivity theorem.

7. RecursiveDensityScaling.lean
   - prefixDensity_antitone and prefixDensity_sum.
   - positive_linearEnvelope_density_mass_gt: positivity implies
       x*delta_k > k+1.
   - linearEnvelope_positive_density_prefix_gap:
       (j-i)+x*(delta_i-delta_j)+L_j(x) <= L_i(x), if i<=j and L_j(x)>0.
   - positive_prefix_density_ratio:
       (j+1)*delta_i <= delta_j*(L_i(g)+i+1).
   - affineSource_le_of_local_positive: a positive local branch dominates any
     affine source whose gain is <=L_i(g)+i+1.

8. PrimeDensitySourceRedundancy.lean
   - firstPrimeMarginal is the reciprocal sequence of initial primes.
   - firstPrimeDensity_le: initial primes minimize density among prime sets
     with cardinality <=j. This follows by sorted-prime domination.
   - firstPrimeDensity_prefix_image identifies the finite prefix image density.
   - firstPrime_unionSource_le_of_plain_certificate: FULL exact-union source
     domination, WITHOUT the large-missing-prime assumption. If the gain is
     nonzero, union cardinality<=j and hence density(union)>=delta_j. Since
     density(union)=delta_i*density(missing), the density-sensitive prefix
     comparison bounds the retained inverse-density gain by L_i(g)+i+1.
   - firstPrime_union_seeded_eq_plain_of_plain_certificates: genuinely recursive
     equality for the exact overlap-aware sources, uniform in the actual prime
     list. Every source length must have a positive certificate in the SAME
     plain first-prime envelope. No source-budget choice restriction is added.
   - extended_firstPrime_union_seeded_eq_plain puts this equality in the exact
     finite-marginal interface used by the arithmetic transfer criterion.

9. RecursiveUnionAudit.lean imports the complete batch and prints nine key
   axiom audits; final build is clean. Log: /tmp/recursive_union_audit.log.

Other logs follow the snake-case filenames in /tmp, notably
/tmp/union_normalized_cardinality.log, /tmp/union_reference_source.log,
/tmp/recursive_positive_scaling.log, /tmp/seeded_envelope_bridge.log,
/tmp/union_source_redundancy.log, /tmp/union_seeded_transfer.log,
/tmp/recursive_density_scaling.log, /tmp/prime_density_source_redundancy.log.
Harmless linter warnings remain in a few files. The last repaired issue was a
rewrite of a finite prime set that also changed its cardinality-dependent
index type; restricting the rewrite to conv_lhs fixed it.

SCOPE: This closes the missing scalar/set-indexed bridge and the overlap-aware
same-model redundancy issue. It does NOT show that arbitrary valid arithmetic
Jacobsthal sources, exact integer/floor sources, finite-wheel information, or
other sieve models are redundant. In particular h(0)=1 itself is not a positive
plain-envelope certificate at length1. No uniform quadratic positivity, no
sufficient low-tail estimate, and no superquadratic cover family was obtained.
The strongest unrestricted bound remains the exponent54/25 log-power theorem
at the header. No new numerical worker was launched in this continuation.

Spec.lean is unchanged: sole original import, unchanged conjecture, sole sorry
at line2177, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed target proof or exact-negation theorem has been submitted.


## Common-core adjacent intervals and residue-injective tails (VERIFIED, RESTRICTED)

Original erdos_970 remains UNSOLVED. Seven new mathematical development files
and one audit file compile, with built oleans. All final printed axiom audits
use only propext, Classical.choice, Quot.sound. No new sorry/admit/native_decide
or axiom occurs. Spec.lean is unchanged.

The review first checked the existing common affine row rescaling, compatible
window realization, exact coefficient-merging results, greedy encodings,
conditional Bennett bounds, and multiplicity restrictions. No new sufficient
uniform estimate followed from those alone. In particular the earlier window
realization and first-hit support-disjointness results were not proposed anew.

New files, namespace Erdos970.OneHitLogConcavity:

1. OneHitCoreCorrelation.lean
   Defines coreCoverWeight(P,R,S,r) as the exact probability that independent
   tail residue classes finish the actual core survivor population in S.
   - coreCoverWeight_union_le: pointwise in the SAME core phase, completion of
     disjoint S,T is negatively correlated if all tail moduli are one-hit on
     the ambient interval.
   - population_cover_le_core_correlation keeps the full nonlinear core average.
   - phaseMean_product_le_phase_mass and population_cover_le_core_phase_mass
     give a loss product(P), the FULL number of core phases, not |P|.
   - population_cover_le_core_square_mean retains the two actual square means.

2. PopulationTranslation.lean
   - populationSurvivors_image_add: exact translation with a common affine phase
     equivalence.
   - populationCoveredFraction_image_add: arbitrary finite population coverage
     probability is translation invariant; no one-hit restriction is needed.
   - coreCoverWeight_distribution_image_add: equality of scalar distributions
     of the translated weights. This does NOT factor their joint distribution.

3. OneHitCoreDyadic.lean
   - void_add_le_core_correlation and void_add_le_core_phase_mass, for tail
     moduli >=m+n.
   - void_double_le_core_second_moment: V_(P union R)(2m)<=E_P[coreWeight_m^2]
     if every tail modulus is >=2m.
   - coreWeightVariance and core_weight_second_moment keep the exact identity
       E[coreWeight_m^2]=V_(P union R)(m)^2+Var(coreWeight_m).
   - void_double_le_of_core_relative_variance is CONDITIONAL on the displayed
     relative variance estimate. No uniform estimate for this variance is proved.

4. OneHitMinimumFrequency.lean
   - coreCountFrequency(P,m,s) is the probability of exactly s core survivors.
   - maximum_frequency_second_moment is a general finite-weight inequality.
   - coreCoverWeight_le_minimum uses the exact occupancy distribution and its
     already-proved monotonicity, not independent point thinning.
   - minimum_frequency_mul_void_double_le: if s is a uniform lower core count,
       coreCountFrequency(P,m,s)*V_(P union R)(2m)<=V_(P union R)(m)^2.
     Tail moduli still must be >=2m. The result includes zero frequency without
     division. A positive supplied frequency lower bound yields a dyadic factor.
   - No polynomial lower bound on this minimum frequency has been proved.

5. OneHitResidueInjection.lean
   Extends one-hit occupancy from populations contained in [0,p) to ANY finite
   population on which x |-> x mod p is injective for every selected modulus.
   - sum_avoid_card_of_injective is the exact insertion update.
   - population_eq_occupancy_of_injective and its finset version identify the
     independent-residue model with the same occupancy recurrence.
   - disjoint_population_coverage_of_injective gives negative dependence when
     injection holds on the UNION of the two populations. Separate injection
     on each half is insufficient and is not used.
   - coreCoverWeight_union_le_of_injective checks injection on the actual core
     survivors, at the given common phase, rather than their ambient span.

6. OneHitCollisionRemainder.lean
   - coreCollisionFraction(P,R,S) is the probability of a core phase where at
     least one tail residue map is not injective on the core survivors in S.
   - population_cover_le_core_correlation_add_collisions extends the correlation
     bound to arbitrary tail primes, with this NONNEGATIVE ERROR retained.
   - void_double_le_square_add_variance_add_collisions is fully general:
       V_(P union R)(2m) <= V_(P union R)(m)^2
                            +coreWeightVariance(P,R,m)
                            +coreCollisionFraction(P,R,range(2m)).
     Neither error term is asserted to be small or replaced by an unconditional
     average inside a nonlinear expression.

7. ParityOneHitDyadic.lean
   - residue_injective_of_parity: survivors of one parity class, in [0,2m), are
     injective modulo any odd prime p>=m. Equal residues plus equal parity would
     force congruence modulo2p, exceeding the available span.
   - coreCollisionFraction_zero_of_parity.
   - parity_void_double_le_core_second_moment,
     parity_minimum_frequency_mul_void_double_le, and
     parity_void_double_le_core_phase_mass extend the preceding estimates to
     tail primes >=m (instead of >=2m), provided2 belongs to the core.
   - The fluctuation/frequency/phase-count loss is still present. This is a
     restricted extension, not an unrestricted dyadic inequality.

8. OneHitCoreAudit.lean imports the complete batch and prints eight key axiom
   audits. Its final build is clean. Log: /tmp/one_hit_core_audit.log.

Other final logs:
/tmp/one_hit_core_correlation.log
/tmp/population_translation.log
/tmp/one_hit_core_dyadic.log
/tmp/one_hit_minimum_frequency.log
/tmp/one_hit_residue_injection.log
/tmp/one_hit_collision_remainder.log
/tmp/parity_one_hit_dyadic.log

Technical repairs: typed survivor-subset proofs were needed when rewriting the
occupancy formula through the opaque populationSurvivors definition. In a
Set.InjOn hypothesis, the union was explicitly coerced from Finset to Set to
avoid elaborating a Set union of coerced operands. Parity congruence proofs
required exposing the value of the subtype representing2 before omega.

LIMITATIONS: The core phase product may be exponentially large, and the minimum
count frequency may be tiny. Even with an empty tail the core-weight variance
is the variance of the void indicator; no uniform small relative variance can
be silently inferred from ordinary survivor-count variance. For intermediate
moduli the collision error may also be large. The new general decomposition
therefore does NOT establish PowerLossDyadicVoidBound, the target quadratic
bound, or its negation. No numerical counterexample search or worker was
launched. The best unrestricted upper bound remains the exponent54/25 result
at the header.

Spec.lean retains its original import and exact conjecture, with the sole sorry
at line2177 and SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed proof or exact-negation theorem has been submitted.

## Two-valued core doubling and sharp injectivity cutoffs (VERIFIED, RESTRICTED)

Original erdos_970 is STILL UNSOLVED. Three new mathematical files (403 lines)
and one audit file compile. The ten main printed axiom audits use only propext,
Classical.choice, Quot.sound. No new axiom, sorry, admit, or native_decide occurs
in these mathematical files. No numerical search was run.

1. BalancedCoreDyadic.lean, namespace Erdos970.OneHitLogConcavity.
   - phaseMean_centered_product and phaseMean_affine_covariance give the exact
     finite-mean covariance algebra.
   - affine_adjacent_counts_nonpos transfers the already proved adjacent COUNT
     covariance inequality to affine weights whose slopes have nonnegative
     product. It does not assert general nonlinear negative association.
   - affine_of_two_values: any function of an integer count in {s,s+1} agrees
     with its affine interpolant on that support.
   - two_valued_count_translate preserves the two count values under the SAME
     actual phase translation used for every point of the block.
   - balanced_core_weight_affine identifies the actual occupancy completion
     weight with that affine interpolant, assuming tail primes >=m.
   - balanced_core_correlation_le proves E[F_left*F_right]<=V(m)^2 if the core
     count at m has only those two values. The common affine slope enters as
     its square, so its sign need not be assumed.
   - balanced_void_double_le gives V(2m)<=V(m)^2 with tail primes >=2m.
   - parity_balanced_void_double_le gives the same with tail primes >=m,
     provided 2 is in the core. All count-range hypotheses remain explicit.

2. BalancedCoreLengths.lean.
   Defines TwoValuedCoreCount P m.
   - singleton_two_valued holds for every singleton prime core and every m,
     by the exact floor/ceiling residue hit count.
   - full_period_constant_count packages the already proved constant-count
     fact at full core periods.
   - core_count_succ records the exact zero-or-one increment.
   - full_period_succ_two_valued: if product(P)|m, the count at m+1 is two-valued.
   - full_period_pred_two_valued: if product(P)|(m+1), the count at m is two-valued.
   - singleton_core_void_double_le specializes the loss-free dyadic inequality.
   These are arithmetic applications of the restricted theorem, NOT a way to
   impose two-valued counts on arbitrary cores and quadratic interval lengths.

3. CoreInjectionSharpness.lean.
   - exists_phase_avoiding_zero_and constructs a common core phase leaving
     0 and d alive whenever 2 in P implies 2|d. For each odd core prime choose
     residue1 unless d mod q=1, in which case choose residue2. Parity uses1.
   - exists_core_residue_collision uses actual positions0,d with p|d and
     0<d<2m to produce a failed residue-injectivity phase.
   - uniform_core_injective_iff_of_no_parity: if 2 is NOT in P and p>0,
     injectivity modulo p on [0,2m) core survivors in EVERY phase is equivalent
     to 2m<=p. Necessity uses d=p.
   - uniform_core_injective_iff_of_parity: if 2 IS in P and p is an odd prime,
     that same uniform injectivity is equivalent to m<=p. Necessity uses d=2p.
   - coreCollisionFraction_ge_single_phase retains a lower contribution of
     1/product(P) for any failed phase.
   - coreCollisionFraction_eq_zero_iff identifies zero collision probability
     with uniform phasewise injectivity (all phase weights are positive).
   - coreCollisionFraction_zero_iff_cutoff: for disjoint prime sets P,R, the
     collision remainder on [0,2m) is zero IFF every tail prime is at least m
     when 2 belongs to P, or at least2m otherwise.
   Consequently adding further odd core primes cannot lower the UNIFORM
   zero-collision cutoff. This does not rule out quantitative nonzero-error
   estimates, weighted errors, or methods that handle multiple hits directly.

4. BalancedCoreAudit.lean imports the three mathematical files and prints ten
   clean permitted-axiom audits. Logs:
   /tmp/balanced_core_dyadic.log
   /tmp/balanced_core_lengths.log
   /tmp/core_injection_sharpness.log
   /tmp/balanced_core_audit.log
   Harmless warnings: unused hP in the single-phase nonnegative comparison;
   missing module docstring in the audit-only file. No pending build failure.

STATUS: These results complete the previously suggested two-valued core idea,
including actual arithmetic examples, and establish the exact limitation of
uniform tail injectivity. They do NOT control general intermediate-prime
multiple hits, prove a suitable uniform dyadic loss, or give a superquadratic
cover family. The best unrestricted bound remains
O(k^(54/25)*log(k+2)^(29/25)); no exponent improvement was obtained here.

Spec.lean is unchanged, with its original import, exact target statement,
sole sorry at2177, and SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No proof or exact-negation theorem for the target has been submitted.

## Well-founded source recycling and zero-budget edge case (VERIFIED, MODEL RESTRICTION)

Original erdos_970 remains UNSOLVED. New file GroundedSourceClosure.lean
compiles with an olean. All four main printed axiom audits contain only
propext, Classical.choice, Quot.sound. Log: /tmp/grounded_source_closure.log.
No numerical search or new worker was launched.

The announced investigation was whether hypothetical smaller quadratic bounds
could close a genuinely recursive induction. For the SPECIFIED affine-source
model, the first failed plain budget gives a structural obstruction: every
previous bound obtained through this same mechanism is still plain-certified.
The new file verifies this transitive argument including the formerly omitted
zero-budget and zero-gain edge cases.

Namespace Erdos970.RecursiveSieve:
- unit_affine_source_le_plain_zero: for g>=1, max(0,(x-1)/g-1) is dominated by
  the empty-prefix plain lower branch.
- zero_budget_union_source_le: the exact-union source at j=0 is dominated for
  every prefix. At prefix0 its gain is1; at every positive prefix its gain is0.
  Thus the TRUE arithmetic endpoint h(0)=1 does not escape this affine model,
  even though the plain envelope is not strictly positive at length1.
- union_seeded_eq_plain_of_active_certificates: only positive-budget sources
  whose union cardinality is <=j need a plain positive source certificate.
  Zero-gain nodes need none. This prevents an artificial terminal-budget
  positivity assumption from entering a proposed smaller-budget induction.
- grounded_union_positivity_is_plain: for any positive length family m(k), if
  every positive budget has a positive exact-union seeded certificate using
  only source budgets strictly below it and source lengths m(j), then the
  unseeded first-prime envelope is positive at m(k) for every positive k.
  Actual prime lists and source choices may vary at every stage. The proof is
  strong induction, not an assertion of positivity at quadratic lengths.
- first_failure_not_repaired: if m(K) is a zero plain branch while all positive
  smaller budgets have positive plain branches at their designated lengths,
  every allowed smaller-budget exact-union source recycling has root value0
  as well. The terminal source gain is zero; its source budget is NOT K.

SCOPE: These results do not cover independent arithmetic bounds with no such
same-model derivation, exact floor sources, finite-wheel information, arbitrary
lower-count induction hypotheses, or all possible sieve methods. They do not
prove an asymptotic lower bound for the plain recurrence, and are not a
negation of erdos_970. No claimed recurrence positivity or universal quadratic
induction step was obtained. Further on-paper review of core/tail concentration,
selected-class pair intersections, and bounded multiplicity supplied no new
uniform inequality; no numerical observations were promoted to results.

Best verified unrestricted estimate is still
O(k^(54/25)*log(k+2)^(29/25)). Spec.lean is unchanged, with its original import,
exact target statement, sole sorry at2177, and SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed proof or exact-negation theorem has been submitted.

Additional continuation check after that build: considered an even coarser
reference marginal q_i=1/(i+2), which would imply a quadratic theorem if its
same plain envelope were positive at a fixed multiple of k^2. A small targeted
floating-point recurrence diagnostic (/tmp/integer_marginal_diagnostic.py)
showed rapid growth already at k=5,10; the k=15,20 searches hit their arbitrary
length ceiling10000 and did NOT bracket a threshold. This is only a diagnostic
of a proposed sufficient certificate, not a counterexample search or a Lean
proof. No theorem depends on it. It yielded no usable positivity estimate.
The existing prime-marginal recurrence and all target statements are unchanged.
No numerical worker remains active. The preceding 'no numerical search' entry
refers to the grounded-source proof itself; this subsequent diagnostic is
recorded here separately for completeness.

## Extended first-hit endpoint: unrestricted exponent539/250 (VERIFIED)

Original erdos_970 STILL UNSOLVED. Four new mathematical files (474 lines)
and an audit file compile. All six main printed axiom audits contain only
propext, Classical.choice, Quot.sound. No numerical diagnostic, optimizer,
external computation, or additional axiom is used in these proofs.

NEW STRONGEST VERIFIED UNRESTRICTED BOUND:
  exists_endpoint_logpower_bound :
    exists C>0, forall k>0,
      jacobsthalFunction(k) <= C*k^(539/250)*log(k+2)^(289/250).
This slightly improves54/25=2.16 to539/250=2.156. It does NOT reach exponent2.

1. FirstHitEndpointMain.lean, namespace Erdos970.FiniteSelberg.
   endpointPrimeCut(L)=floor(exp(L/(539/250))). The old endpoint was
   floor(exp(L/(54/25))). endpointMainSum uses the unchanged twoScaleCutoff.
   - endpoint_band_mean_le: on the additional prime annulus, u=(L/log p-1)/2
     lies in[289/500,29/50]. The established integer-cutoff normalizer lower
     bound, with explicit50000*firstHitProfileError<=L, gives the summand bound
       (1/p)/G_p <= (7/4)/(p*log p).
   - endpoint_band_sum_le applies the actual weighted prime interval estimate,
     not a heuristic density integral. Its extra main cost is7/(1000*L), and
     its error is endpointTailError/L^2, where
       endpointTailError=(7/2)*(WeightedMertens.boundConstant+1)*(54/25)^2.
   - exists_twoScale_full_margin preserves the original finite main margin
     saturatedHitMainMargin rather than reducing it to the older1/(400L).
     It retains the shortened small-prime cutoff cost1/(10000L) and both
     O(1/L^2) errors, with an explicit eventual fixed-wheel construction.
   - endpointMainMargin=saturatedHitMainMargin-1/10000-7/1000 is proved greater
     than6/10000 by exact rational arithmetic. For large enoughL the combined
     error is<=1/(10000L), hence exists_endpointMainSum_slack gives
       endpointMainSum(L)<=1-1/(2000L).

2. FirstHitEndpointCost.lean.
   twoScale_reference_cost_of_log_bound: the SAME cost estimate
       sum_i kernelCost_i^2 <= twoScaleCostConstant*exp(L)/L^2
   needs only2*log(p_i)<=L, not the narrower old endpoint. The proof retains
   the small-prime exp(L/2) sum and the large-prime inverse-log-square tail.
   Since539/250>2, every prime at the new endpoint satisfies this premise.

3. FirstHitEndpointSurvivor.lean.
   endpoint_reference_main_le, prime_survivor_of_endpoint, and
   isJacobsthalBound_of_endpoint transfer the new main sum and cost through
   the existing exact dominating-marginal argument to ARBITRARY prime sets.
   Positivity follows when
       m>2000*L*(1+twoScaleCostConstant*exp(L)/L^2).
   No assertion that the first k primes are arithmetically extremal is used.

4. FirstHitEndpointLogPower.lean.
   Set L=L0+(539/250)*log(nthPrime k), m=floor(X)+1 with
       X=2000*(2+twoScaleCostConstant)*exp(L)/L.
   Apply the new survivor bound and the existing nth-prime estimate to obtain
   exists_endpoint_logpower_bound with logarithmic exponent289/250.
   One real constant works for every positive k. There is no unproved
   asymptotic positivity premise in this theorem.

5. FirstHitEndpointAudit.lean prints the six clean axiom audits.
   Logs:
   /tmp/first_hit_endpoint_main.log
   /tmp/first_hit_endpoint_cost.log
   /tmp/first_hit_endpoint_survivor.log
   /tmp/first_hit_endpoint_logpower.log
   /tmp/first_hit_endpoint_audit.log
   Harmless warnings: an unused positivity hypothesis in the pointwise band
   lemma and two inherited unnecessary-sequence-focus warnings in the cost
   proof. All final builds succeed, with no pending worker or repair.

Further check of the proposed ordering route: re-read the existing
ContinuousIntervalOrdering/Sorting and FirstHitDisjointCost results and the
integer-hull/mixed-pattern ordering diagnostics in this log. Decreasing
marginals already dominate for the specified continuous interval recursion;
integer/hull variants do not satisfy the same pointwise theorem. Distinct
first-hit indices have disjoint monomial supports for a fixed order, so no
cross-index cancellation was newly obtained. This review produced no further
uniform target inequality and no claim that all possible order-mixtures or
sieve schemes are ruled out.

LIMITATION: The new estimate spends a finite positive margin to extend the
old endpoint slightly. It does not bypass the previously verified critical
first-hit model obstruction, remove the remaining positive power above2,
or construct a superquadratic cover family. Spec.lean remains unchanged,
with the same import, exact target statement, sole sorry at2177, and SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed proof or exact-negation theorem for the target was submitted.

## Different-order cancellation and one-order separation (VERIFIED, NO SETTLEMENT)

The original conjecture remains UNSOLVED. Two new files compile with clean
permitted-axiom audits:
  OrderMixtureCriterion.lean (general criterion and endpoint restriction)
  OrderMixtureExample.lean (exact three-coordinate example)
Logs: /tmp/order_mixture_criterion.log, /tmp/order_mixture_example.log.

The generic survivor_of_boolean_cover applies to arbitrary nonempty-pattern
majorants, using their MERGED ordinary coefficients and the usual unit-moment
error bounds. coefficientMixture_cover and booleanObjective_mixture_le show
convex mixtures preserve majorization and cannot increase the averaged objective.
orderedHitValue_last_le proves that any single fixed-order hit sum with arbitrary
nonnegative prefix-dependent stage weights cannot decrease when its last bit is
switched on. No normalization or square-kernel assumption is needed for that lemma.

The three exact rational components have coefficients1 on singletons, -3 on the
triple, and on pairs +1 if the final coordinate belongs to the pair and -1 otherwise.
Each is represented in Lean by a genuine normalized nonnegative first-hit sum in
its own order. Their uniform average has pair coefficients1/3. Each component
has L1 coefficient cost9, but the merged mixture has cost7. Its value at the full
pattern is1 while its value at every two-hit pattern is7/3; hence it cannot be
represented by ANY single-order nonnegative prefix-dependent hit sum.

At actual prime marginals[1/5,1/7,1/11] and mass15, the mixture mean is103/231,
its mean-plus-cost objective is1054/77<15, and all three chosen components have
objective>15. mixed_survivor applies this criterion to any population with those
moment bounds. CRUCIAL LIMITATION: the simple union bound already does better
for these marginals; this is not a gain over the best single-order sieve, nor
an asymptotic theorem or a Jacobsthal-bound improvement.

The next investigation asks whether mixtures recover ALL normalized cover
majorants. An on-paper construction allocates each nonempty-pattern excess
F(v)-1 to one hit coordinate j, then adds it at the final stage of an order
ending in j. Uniform averaging over j recovers F. The generic Lean file
OrderMixtureUniversal.lean has been written and its FIRST BUILD is pending;
do not yet treat this universality statement as verified.

An independent targeted exact-rational diagnostic also confirmed that canonical
Boolean-square coefficients need not have alternating signs. For primes
[101,103,107,109,113] and the canonical support of subsets of size<=3, the full
five-coordinate coefficient is
  108877434644698353576 / 11748288937523377849 > 0,
where the alternating sign would be negative. This support is a genuine prime
product cutoff R=113^3: every triple fits and every quadruple exceeds R.
Script: /tmp/check_canonical_sign.py. This is not yet Lean-checked and is only
a sign-structure observation, not a new upper bound.

## Universality of order mixtures and canonical sign counterexample (VERIFIED)

Both investigations from the preceding entry are now kernel-verified. The
original quadratic conjecture remains UNSOLVED; neither result is an asymptotic
bound or an actual cover counterexample.

1. OrderMixtureUniversal.lean, 213 lines, clean axiom audits.
   normalized_cover_is_order_mixture: for ANY F on the Boolean cube Fin(n+1),
   if F(empty)=0, F(singleton)=1 for every coordinate, and F(v)>=1 for every
   nonempty pattern, then F is the UNIFORM AVERAGE of n+1 first-hit sums with
   nonnegative normalized prefix-dependent stage weights. The j-th order is
   the identity with its last coordinate swapped with j. The excess F(v)-1
   is gated by the first true coordinate in the original order, and added
   (scaled by n+1) at the final stage of the corresponding swapped order.
   Earlier stages use the exact empty-prefix indicator. All stage weights
   depend only on earlier coordinates and equal1 at the empty prefix.
   This proves universality for the stated singleton-normalized class, NOT
   that all objective optima satisfy the singleton normalization. It gives
   no cost or sparsity bound for the representation. Thus mixtures enlarge
   the single-order class but sit inside the global Boolean majorant method
   already investigated; representability alone supplies no uniform gain.
   Log: /tmp/order_mixture_universal.log.

2. CanonicalSignExample.lean, 89 lines, all three final theorems compile with
   clean permitted-axiom audits.
   The finite-rational table and the real canonical square agree, with the
   actual divisorSupport prime (113^3) and primes[101,103,107,109,113]. The
   full degree-five Boolean coefficient is the positive rational displayed
   in the preceding entry. The corollary canonical_not_alternating proves
   the negation of the universal alternating-sign assertion for this example.
   Log: /tmp/canonical_sign_example.log.

Spec.lean has not been changed. Its sole original sorry is still present;
there is no proof submission for the target.

## Adjacent-position moment diagnostic (FINITE, NOT A TARGET BOUND)

New diagnostic /tmp/multi_position_threshold.py treats each prime as a categorical
local residue pattern on H adjacent positions. A state permits at most one residue
per prime; primes<=H hit all offsets in that residue. Atoms are restricted to
patterns covering every one of the H positions. Every partial assignment of a
single residue per included prime has ideal moment1/product and absolute error
epsilon; total population is normalized to1. Minimizing epsilon gives the
unit-error mass threshold1/epsilon. This retains local same-prime arithmetic
exclusions absent from the one-position Boolean model. All numbers below are
floating LP diagnostics only, NOT Lean dependencies or exact certificates.

  primes2..13 (k6): H2 threshold51.80137999014, H3 threshold48.32087079981,
    H6 threshold41.92043075082. Raw one-position first-hit root111.00295712182.
  primes2..19 (k8): H2 threshold102.40661476374; raw root213.34711409127.
  primes3..13 (five ODD primes): H2 threshold23.07514983864,
    H3 threshold22.20059142435; raw root25.90068999509.
All solves finished in under3 seconds. An initial JSON int64 serialization error
occurred AFTER successful solves; fixed by int-casting the support count and
reran. No failed solver or background worker remains. Logs and arrays are
/tmp/multi_position_threshold_{k}_{H}[ _from3 ].log/json/npz (no space in paths).

IMPORTANT BASELINE CHECK: the first-six and first-eight H2 values are EXACTLY
within numerical error twice the raw root with prime2 removed. Thus these two
cases reproduce exact parity pre-sieving, not a gain over that baseline. The
odd-prime H2 diagnostic has a simple ten-term dual polynomial, with mean
2836/5005 and raw coefficient cost10. It chooses offset0 when prime3 hits
offset1 and otherwise chooses offset1, with two costly negative terms dropped.
It is only a finite method example, not an optimum theorem or an asymptotic gain.

New arithmetic observation to formalize: among those ten terms, the + and -
coefficients at each of moduli3*5 and3*7 involve DIFFERENT residue classes of
the SAME modulus. Their counts differ by at most1, not2. This reduces that
polynomial's uniform error estimate from10 to8, and would certify a survivor
in20 consecutive positions for any five distinct odd primes dominating
[3,5,7,11,13]. This exact finite transfer is NOT YET FORMALIZED. A general
same-modulus balanced-coefficient error lemma is the announced next step.

The original target remains UNSOLVED, and the strongest verified unrestricted
asymptotic bound is unchanged. Spec.lean remains untouched with its original
sole sorry. The mixture/sign audit is complete in OrderMixtureAudit.lean;
/tmp/order_mixture_audit.log lists only the permitted axioms for all7 checks.

## Shared-modulus error and adjacent-position certificate (VERIFIED, FINITE)

The preceding announced arithmetic transfer is now complete. All three new
mathematical files compile, and their printed dependency audits contain only
propext, Classical.choice, Quot.sound. No new axiom, sorry, admit, or native_decide
is used in these files. The original erdos_970 remains UNSOLVED.

1. ResidueBalancedError.lean (namespace Erdos970.BrunCriterion):
   - count_band_error: if all real counts n_i and the reference x lie in one
     common interval[B,B+1], then
       |sum c_i*n_i - x*sum c_i| <= (sum|c_i| + |sum c_i|)/2.
   - residue_family_error applies this to ANY assignments of residue classes
     modulo the SAME positive d, uniformly in the interval length.
   - residue_balanced_error: zero-sum coefficients pay at most half their L1 cost.
   - residue_count_pair_error: two counts modulo the same d differ by at most1.
   - intersection_count_pair_error retains this bound for two arbitrary CRT
     assignments to the same finite prime support.
   This is a shared-modulus arithmetic fact, not an independence assumption.

2. AdjacentShiftMoments.lean (namespace Erdos970.AdjacentShift):
   - hit/count/pairCount allow different offsets in the same interval.
   - count_error and pairCount_error give the standard unit-moment bounds.
   - pairCount_difference_error bounds by1 the difference between two shifted
     two-prime intersections with the same prime support. The offsets may all
     differ; the phases are otherwise arbitrary.

3. AdjacentShiftExample.lean (namespace Erdos970.AdjacentShift.Example):
   - pointwise_table, kernel-checked over the finite Boolean table, says the
     ten-term polynomial from the diagnostic majorizes1 whenever both adjacent
     positions are covered and the first prime cannot hit both.
   - polynomial_interval_upper proves its actual arithmetic interval sum is
     <=m*density(p)+8, where
       density = 1/p1 + 1/p2 + (1+1/p0)*(1/p3+1/p4).
     The two same-support positive/negative pairs cost1 each rather than2.
     Four singleton terms and two remaining pair terms each cost1: total8.
   - density_le proves density<=2836/5005 whenever the five moduli dominate
     [3,5,7,11,13], with no first-prime-extremality assumption.
   - five_odd_survivor: for ANY injective five-prime list dominating that list,
     and ANY residues, there is j<20 avoiding all five classes. If all20 were
     covered, the19 adjacent windows each have polynomial>=1, whereas their
     sum is <=19*(2836/5005)+8<19, a contradiction.
   This is a FINITE actual prime-class bound. It is not a uniform asymptotic
   improvement, not asserted to be optimal, and not a proof of Erdős970.

Logs: /tmp/residue_balanced_error.log, /tmp/adjacent_shift_moments.log,
/tmp/adjacent_shift_example.log. AdjacentShiftAudit.lean is the combined audit;
/tmp/adjacent_shift_audit.log should show six clean axiom lists. Harmless linter
warnings in two helper proofs do not affect compilation.

The order-mixture batch and canonical-sign counterexample from the earlier
entries are also fully built and audited (OrderMixtureAudit.lean). There are
no open solver runs and no pending repairs. The current methods give new
finite representability/error facts, but no uniform m=C*k^2 inequality and
no superquadratic actual-cover family. The strongest verified unrestricted
upper bound remains O(k^(539/250)*log(k+2)^(289/250)).
Spec.lean is unchanged: original import, exact target statement, sole sorry
at2177, SHA256 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No proof or exact-negation theorem for the original conjecture was submitted.

## Alternating Buchstab refinement engine (VERIFIED; no new uniform bound yet)

BuchstabRefinement.lean, BuchstabRefinementSound.lean, and
BuchstabRefinementAudit.lean compile and have clean permitted-axiom audits.
Namespace Erdos970.RecursiveSieve.Buchstab. The divisor level D rescales to
D*q_i at required-hit branches. lowerStep clips a first-hit complement at0
and may discard branches through an explicit keep predicate. upperMain takes
the minimum of the old upper source and the complement of the new lower
children. upperError takes the MAXIMUM of their corresponding complete error
budgets. The root unit error and every child error are retained.

Verified: main-density invariance; main-term monotonicity; one-node propagation;
refinement_sound for nonnegative weighted populations with unit intersection
errors and an explicit valid upper-sieve source at every reachable node;
survivor_of_refinement, requiring positivity AFTER ALL propagated errors.
No canonical Selberg source has yet been instantiated, and there is no uniform
positivity theorem for this new engine.

## Euler-product limit (VERIFIED)

EulerMassAsymptotic.lean now compiles; /tmp/euler_mass_asymptotic.log has clean
axiom lists. It proves exists_initialEulerMass_log_limit:
  exists C>0, initialEulerMass(n)/log(n) tends to C.
The constant is deliberately not identified. The proof bounds
-log(1-1/p)-1/p between0 and1/(p*(p-1)), telescopes the latter over all integers,
and combines the existing reciprocal-prime interval estimate with completeness.
This allows normalized ratios to cancel the unidentified constant. It does not
itself supply the required weighted-profile prime-sum transfer.

Analytic diagnostics (NOT Lean proofs): /tmp/buchstab_profile_iteration.py gives
ideal model critical roots decreasing toward2 under alternating refinement.
/tmp/buchstab_coarse_iteration.py suggests one refinement of existing coarse
normalizer bounds is positive at s=2.1. /tmp/buchstab_rational_grid.py gives an
EXACT Python Fraction rectangle calculation: mesh1/50 at s=21/10 has margin
>0.0357, or normalized lower profile>0.0170. The profile transfer, rectangle
inequalities, and any rounded integer certificate are NOT implemented in Lean.
These computations are not dependency axioms and do not prove a survivor.

BuchstabRefinementCost.lean is presently under development: intended uniform
fixed-depth error bound C*(1+Z)^(2*n)*D^a, where the marginal power sums are <=Z
and retained lower nodes and all upper children have level>=1. Check its latest
build log before treating this as verified. The original quadratic conjecture
is still UNSOLVED and Spec.lean has not changed.

## Buchstab source, power costs, and precise sectors (VERIFIED)

The formerly pending BuchstabRefinementCost.lean now compiles. In namespace
Erdos970.RecursiveSieve.Buchstab, upperError_le_rpow and
refined_lowerError_le_rpow prove the complete error bounds
 C*(1+Z)^(2*n)*D^a and C*(1+Z)^(2*n+1)*D^a,
under exactly the stated marginal-power and retained-level hypotheses.
BuchstabPrimeCost.lean supplies a uniform Z for every a>1 using the convergent
integer p-series; primeKeep uses the square of the NEXT prime and satisfies
all retained-level premises for any strictly increasing prime sequence.

WeightedSelbergSource.lean generalizes the canonical upper-square estimate to
arbitrary finite weighted populations, nonintegral expected mass, and unit
intersection errors. At divisor cutoff floor(sqrt D), its error is <=D for
D>=1. All required hits can therefore be conditioned upon.

BuchstabSelbergSource.lean connects this source at EVERY reachable conditional
node. Its selbergCutoff=max(1,floor(sqrt D)) is defined even below level1;
selbergCost is nonnegative everywhere and <=D above level1.
conditional_selberg_upper checks disjointness of prefix coordinates and required
hits and uses only the original intersection hypotheses.
survivor_of_selberg_refinement is a rigorous unconditional-source criterion;
its main-positivity inequality AFTER the entire power cost remains explicit.
It is not yet a bound on jacobsthalFunction.

EulerMassScaling.lean proves precise logarithmic scaling, with no new numeric
constant assumption. scaledEulerMass_ratio_limit says
 M(floor(exp(tL)))/M(floor(exp(uL))) -> t/u for t,u>0.
The exact first-hit density telescoping gives density_annulus_telescope.
Consequently firstHit_sector_limit proves
 M(floor(exp(vL))) * sum_{exp(tL)<p<=exp(uL)} 1/(p*M(p^-))
   -> v/t-v/u,
where the prime endpoints are correctly rounded. This avoids a fresh weighted
prime-sum estimate for every profile piece.

All five files compile and their printed axiom audits are clean. Logs:
/tmp/buchstab_refinement_cost.log, /tmp/buchstab_prime_cost.log,
/tmp/weighted_selberg_source.log, /tmp/buchstab_selberg_source.log,
/tmp/euler_mass_scaling.log. A constructive Decidable-instance mismatch for
finite-prefix avoidance was repaired by a pointwise case split, not by any
axiom. No submission file change or proof submission has been made.

The analytic route still needs rigorous base-profile domination, prime-sector
profile transfer (including the infinite tail), and positive grid bounds.
One finite refinement can plausibly improve the current exponent toward2.1,
but this alone would STILL NOT prove the exact quadratic conjecture. No new
unrestricted exponent has yet been assembled. The best bound in the header
remains the strongest verified one.

## Canonical profile interfaces and first uniform lower tail (VERIFIED)

Further development files compile with only permitted axioms:

- BuchstabLevelMonotonicity.lean: all refined upper main terms are antitone
  in divisor level, all refined lower terms monotone. The canonical base lies
  above the independent prefix density. These are MAIN-term statements only;
  they do not erase or monotonize the separate error budgets.
- BuchstabScaledSource.lean: base(k,D)=selbergBase(k,4D), so its cutoff
  floor(sqrt(4D)) dominates ceil(sqrt D) for D>=1. Full propagated error is
  4*(1+reciprocalPowerConstant a)^(2*n+1)*D^a. Its survivor criterion retains
  this factor4. The original floor source is unchanged.
- BuchstabBaseProfile.lean: buchstabBaseRatio(p,s) uses the ceiling cutoff
  ceil(exp((s/2)*log p)) and the actual strict Euler mass. Verified middle
  envelope E/firstHitFullProfile(s/2), E=90009/50000, on1.1<=s<=6 under the
  established log/Euler thresholds; saturated bound E*(290999/500000) for
  s>=5.4; relative tail 1+(9/217)*(8/s)^8 for s>=8. The relative tail cancels
  the Euler mass BEFORE using any absolute Euler estimate.
- BuchstabPrimeCoordinates.lean: nthPrime/primeMarginal; exact prefix image,
  sum, density, and normalizer identities; scaled_base_le_normalized_profile
  connects the arithmetic profile to the indexed source, and the density-
  weighted sums become exactly the arithmetic first-hit measure.
- BuchstabDefectCoordinates.lean: exact density-centered formulas for the
  lower and upper main steps and their excess/deficit sufficient inequalities.
- BuchstabSectorSums.lean: finite step-sector sums have the exact limit implied
  by EulerMassScaling; eventually_step_profile_upper transfers a finite
  sector majorant with arbitrary positive slack. It DOES NOT handle the
  infinite small-prime tail by itself.
- BuchstabPrimeTail.lean: scaledPrimeCutoff/excess, exact zero contribution on
  a fixed initial wheel once exp L>=W*wheel(W)^2; indexed/arithmetic equality;
  pointwise ninth-tail estimate and sharper thirteenth-tail coefficient
  6*(26/3)^8/(217 L^8) times log(p)^7/p.
- BuchstabTailMoments.lean: sum either pointwise tail over ANY prime subset
  below R, preserving log(R)^7/7+2*sharpMomentError*log(R)^6. The small wheel
  and both log thresholds are explicit.
- BuchstabLowerTail.lean: defines referenceUpper and referenceLower for the
  scaled source. referenceLower_zero_tail_finite proves
     rho(k)*(1-(4/525)*(9/s)^8) <= referenceLower 0 k (exp(s*log nthPrime(k)))
  for s>=9, under explicit wheel, log, and Euler hypotheses.
  exists_referenceLower_zero_tail supplies ONE absolute prime threshold
  valid for EVERY real s>=9. The moment error is absorbed using
  log(nthPrime k)>=280*sharpMomentError; no limit with varying s is assumed.

The latest BuchstabInitialNodes.lean build is being checked. Its intended
exists_referenceUpper_zero_grid connects the entire rounded initial grid to
actual referenceUpper0 values at exp((j/50)*log p), uniformly for55<=j<=600.
Only two routine errors (tactic scoping and explicit Rat.cast_le) remained
and were just repaired; CHECK /tmp/buchstab_initial_nodes.log before treating
that file as verified.

## Rounded finite refinement grid (VERIFIED ARITHMETIC ONLY)

The finite grid is now actually kernel checked, not merely Python Fraction
arithmetic. Files:
  BuchstabGridData.lean
  BuchstabGridBaseCheck.lean
  BuchstabGridBaseBounds.lean
  BuchstabGridLocalChecks.lean
  BuchstabGridCertificate.lean
All final builds/audits are clean. No native_decide, new axiom, or sorry was
used. Logs /tmp/buchstab_grid_{data,basecheck,basebounds,localchecks,certificate}.log.

CURRENT parameters (these supersede the earlier diagnostic parameters):
  scale H=1,000,000; mesh N=50; terminal j=600 (s=12).
  E=90009/50000; tail B=3/50 (enlarged from9/217).
  Base nodes: 2E/s for s<=2; rational chord interpolation of firstHitGridUpper
  on2<=s<=5.4; saturated E*(290999/500000) for5.4<=s<8;
  1+B*(8/s)^8 for s>=8.
  Initial-integral tail = B*8^8/(7*12^7), rounded upward.
  Lower-tail coefficient C=8B/63=4/525.
  Lower-deficit integral tail is deliberately enlarged to
    (3/2)*C*9^8/(7*12^7), rounded upward.
  This extra3/2 allows the elementary Euler ratio6/5 and coarse denominator
  factor13/12 in the still-pending small-sector deficit integration.
  Each positive lower node loses ten units (1e-5); refined upper nodes add
  ten units, unless the old base is smaller. Every rectangle increment is
  rounded upward. First positive lower node is108 (s=2.16).
  Final integer margin at s=21/10 is14797/1e6 before dividing by2.1, so the
  arithmetic certificate safely retains normalized lower value1/200.

refined_grid_budget proves, EXACTLY over reals,
  initialIntegral(600)/H + sum_{55<=j<600}(upperNodes(j)/H-1)/50
      < 4179/2000 = (21/10)*(1-1/200).
This is still an ARITHMETIC PROFILE certificate, not yet an actual sieve
positivity theorem. The finite middle-sector and two small-sector transfers
must still be assembled.

Data representation lesson: flat arrays of601 entries caused excessive kernel
reduction memory, even with proof chunks and -j1. The six main tables are NOW
functions Nat->Nat using balanced index branches and leaf arrays of<=16
entries. They keep the SAME exact integers and default to0 past600. This
reduced the complete local check to about14 seconds. profileValues and
profileNumerators remain small arrays of18 entries.
The generator is /tmp/generate_buchstab_integer_grid.py. The local certificate
is split into61 kernel-checked blocks of10 indices. Base bounds are checked
as NATURAL cross-products, then converted symbolically to rational inequalities.
An important cast lesson: `(j%10 : ℚ)` is NOT the desired cast of Nat.mod;
use `((j%10 : ℕ) : ℚ)` explicitly. The corrected current files do so.

The original erdos_970 is STILL UNSOLVED. Even successful positivity at s=2.1
would only yield a new exponent above2, not the exact quadratic target.
No new unrestricted Jacobsthal bound has yet been assembled. Spec.lean is
unchanged with the original sole sorry and SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.

## Continuation: actual tail and real-budget builds checked

The following now compile and audit with only propext, Classical.choice, and
Quot.sound:
- BuchstabInitialNodes.lean: actual initial upper-source grid, one uniform prime
  threshold for all nodes55..600.
- BuchstabTailAlgebra.lean: normalized truncated-moment conversion and explicit
  initial/deficit terminal allowances.
- BuchstabInitialTail.lean: actual initial small-prime excess tail <=T0/s,
  uniformly for s>=1, after a fixed wheel and moment error.
- BuchstabDeficitTail.lean: lower-deficit prime coordinates, exact fixed-wheel
  vanishing, and pointwise thirteenth-cutoff moment bound.
- BuchstabLowerDeficitSum.lean: actual normalized lower-deficit tail <=T1/s,
  uniformly for s>=1. Its pending build has PASSED.
- BuchstabGridBudgets.lean: real telescoping budgets for all three arrays,
  ten-unit node slacks, and refined_grid_budget_strong <1043/500=2.086.

No actual full refined-grid positivity has been claimed yet; the prime-bin
partition and finite-sector transfers remain to be assembled. The target
quadratic conjecture remains UNSOLVED, and exponent2.1 positivity would NOT
settle it.


## Actual finite Buchstab refinement and unrestricted growth (VERIFIED)

The arithmetic grid has now been fully transferred to actual sieve main
terms and then to interval survivors. New files, all compiled and audited:

1. BuchstabGridSectors.lean
   - gridPrimeCut, gridPrimeBin, exact root/terminal cut identities;
   - log and child-level inequalities;
   - exact bin telescoping and strict-prefix <= tail + bins;
   - eventually_grid_sector_upper: finite step majorants transfer to
     sum(c_j/50)/s plus any positive slack.

2. BuchstabGridTransfer.lean
   - primeUpperExcess and its indexed/summed identities;
   - nonnegative excess and deficit; upper excess decreases with refinement;
   - monotonicity transfers actual node bounds throughout each bin;
   - all bin primes eventually exceed any fixed threshold;
   - exists_grid_total_bound assembles a SEPARATELY SUPPLIED tail with finite
     sectors. It compares strict and inclusive Euler normalizations instead
     of silently equating them.

3. BuchstabGridMain.lean
   - all refined upper depths reuse the initial excess tail by monotonicity;
   - exists_referenceLower_zero_grid: actual first lower grid, uniform threshold;
   - exists_referenceUpper_one_grid: actual first refined upper grid;
   - exists_referenceLower_one_positive:
       rho_k/200 <= referenceLower1(k,exp((21/10)*log(p_k)))
     above one absolute threshold. The node transfers spend only half of
     their ten-unit rounding slack. The root spends1/1000 finite-sector slack
     against the verified2.086 integral budget. Both small-prime tail budgets
     remain charged. This is ACTUAL MAIN POSITIVITY, not just model arithmetic.

4. BuchstabDominatingTransfer.lean
   - liftSet_prod for subsets of the finite prefix;
   - survivor_from_dominating_refinement adds independent virtual OR hits.
     Weighted nonnegativity, unit moment errors, finite-prefix products, and
     decoding back to actual interval positions are all proved.
     NO first-prime extremality assertion is used.

5. BuchstabIntervalSurvivor.lean
   - referenceLower_antitone_prefix when the larger prefix is kept;
   - prime_survivor_of_refined_main for arbitrary P.card<=k;
   - isJacobsthalBound_of_refined_main with full error
       4*(1+reciprocalPowerConstant(a))^3*D^a, a>1.
     The main-positivity comparison is STRICT after the complete error.

6. BuchstabGrowth.lean
   - eventual_refined_prime_growth for every b>21/10, using a=b/(21/10),
     D=p_k^(21/10), and the existing Euler upper bound;
   - absorb_finitely_many_bounds is a general explicit finite-sum absorption;
   - nthPrime_log_upper uses the existing quantitative nth-prime estimate;
   - exists_refinedBuchstab_logpower_bound:
       forall b>21/10, exists C>0, forall k>0,
       h(k) <= C*k^b*log(k+2)^(b+1);
   - exists_refinedBuchstab_power_bound:
       forall epsilon>0, exists C>0, forall k>0,
       h(k) <= C*k^(21/10+epsilon).
     Constants depend on b/epsilon. No limiting-constant argument is made.

7. BuchstabCompleteAudit.lean imports the complete chain and audits five main
   results (check its log if resuming while build is pending).

Individual logs /tmp/buchstab_{grid_sectors,grid_transfer,grid_main,
 dominating_transfer,interval_survivor,growth}.log are clean.
All new mathematical files total831 lines. They use only propext,
Classical.choice, and Quot.sound; none uses sorry, admit, or native_decide.

STATUS: The strongest unrestricted bound has improved, but the ORIGINAL
QUADRATIC CONJECTURE REMAINS UNSOLVED. Classical one-position sieve positivity
above2 does not supply positivity below the first-prime square scale. No
actual superquadratic covering family or uniform C*k^2 bound has been found.
Spec.lean remains unchanged, with its original sole sorry and SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed proof or exact-negation theorem has been submitted.


## Finite-prefix linear error and exact base21/10 (VERIFIED)

The continuation reviewed the largest-prime increment, optimal-cover exchanges,
long-interval dyadic void reduction, and same-modulus adjacent-position work.
No missing quadratic estimate was proved. In particular, negative adjacent
COUNT covariance still does not control nonlinear complete-coverage events.
The existing diluted Laplace counterexample does not by itself refute the
long-interval power-loss criterion. No new numerical search was launched;
a tiny exact count check only reconfirmed the old three-prime example has
minimum counts12 and24 at lengths26 and52, so there is no min-count exponent
gain available in the dilution limit (min counts are superadditive).

New compiled files, all with clean permitted-axiom audits:

1. BuchstabLocalCost.lean
   lowerErrorStep_le_linear_local, upperError_le_linear_local, and
   refined_lowerError_le_linear_local restrict all prefix hypotheses to k<=K.
   No infinite reciprocal summability is assumed. Define
     prefixReciprocal p K = sum_{i<K}1/p_i.
   Then for k<=K, D>=0, every refinement depth n has complete lower error
     <=4*(1+prefixReciprocal p K)^(2n+1)*D.
   Every kept child-level premise remains in the proof. The max of the full
   upper error budgets is retained exactly.
   prefixReciprocal_loglog applies the existing arbitrary-prime Mertens bound.

2. BuchstabLinearTransfer.lean
   survivor_of_scaled_linear_refinement and
   survivor_from_dominating_linear_refinement carry the new linear error
   through the full weighted-population and virtual-OR-hit construction.
   A separate reference cap J may exceed the actual population index budget.

3. BuchstabLinearSurvivor.lean
   prime_survivor_of_linear_refinement and
   isJacobsthalBound_of_linear_refinement apply to arbitrary prime sets
   of card<=k, with strict main positivity after error
     4*(1+prefixReciprocal nthPrime k)^3*D.

4. BuchstabLinearGrowth.lean
   The finite reciprocal sum is bounded by the previously verified log-log
   budget. With D=p_k^(21/10), actual root main >=rho/200, and Euler cap9/5,
   the interval length floor(360*log(p_k)*A*H(k)^3*D)+1 beats every error.
   Here A is a fixed positive constant and H(k)=1+log(log(k+3)).
   exists_refinedBuchstab_loglog_bound proves a SINGLE C>0 such that
     h(k)<=C*k^(21/10)*log(k+2)^(31/10)*(1+log(log(k+3)))^3, forall k>0.
   Finite budgets are absorbed explicitly; no limiting constant is assumed.

5. BuchstabLinearAudit.lean audits the complete new chain (check its log if
   resuming while pending). Individual clean logs are
   /tmp/buchstab_{local_cost,linear_transfer,linear_survivor,linear_growth}.log.

This removes an artificial positive POWER allowance from the complete error,
not the substantive sieve threshold above2. It does NOT settle erdos_970.
Spec.lean remains unchanged with its original import, statement, and sole sorry.
SHA256 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed proof or exact-negation theorem has been submitted.

## Quantitative refined counts and exponent19/20 low tail (VERIFIED)

The original erdos_970 remains UNSOLVED. Spec.lean is unchanged.
New compiled files, with only propext, Classical.choice and Quot.sound in
all printed axiom audits:
- Submission/BuchstabCountTransfer.lean
- Submission/BuchstabCountPower.lean
- Submission/BuchstabLowTail.lean
Logs: /tmp/buchstab_count_transfer.log, /tmp/buchstab_count_power.log,
/tmp/buchstab_low_tail.log. The last log now has NO ERRORS and no sorryAx;
the earlier local nonnegativity tactic error has been repaired.

The quantitative transfer preserves the actual weighted survivor count,
not merely existence. The virtual-OR population has count at most the
actual population. At the kept root it gives
  m * referenceLower 1 k D
    - 4*(1+prefixReciprocal nthPrime k)^3*D
  <= actual survivor count
for any prime set P of cardinality at most k. All complete refinement errors
are retained, including the maximum error when choosing between upper mains.

With B = buchstabCountLogConstant = 720*(2+log(160)/log(2)), the theorem
  Erdos970.RecursiveSieve.Buchstab.eventually_prime_count_power
proves: for every fixed b>21/10, eventually in k, uniformly over prime sets
of cardinality <=k, residues, and interval lengths m>=k^b, the survivor count
is at least m/(B*log(k+2)). The eventual threshold may depend on b; no exchange
of pointwise and uniform eventual quantifiers is made.

The theorem
  Erdos970.SoftExposure.eventually_refined_quadratic_low_tail
proves, with fixed natural scale M=8*2^160 and real L=20480*B, eventually in k,
uniformly over prime sets of cardinality <=k:
  lowCountFraction P (M*k^2) (M*k^2/(L*log(k+2)))
    <= exp(-k^(19/20)/64).
It uses the count theorem at exponent40/19, partial depth2*t^76, an
80th-power envelope for k, and the previously verified core-tail exposure
inequality. PartialLower has the strict cardinality premise |Q|<depth.

This is a near-zero probability estimate, NOT exclusion of an individual
exceptional covering phase. The strongest unrestricted upper bound remains
that in the header, with base exponent21/10 and explicit logarithmic factors.

### Resampling-mean continuation (NO SETTLEMENT)

For a fixed retained core with survivor set S, independently resampling the
remaining prime residues gives exact expected survivor count rho_tail*|S|.
A covered phase bounds |S| by the filtered deletion budget, so this suggests
a Markov/cylinder improvement over retaining every point of the old cylinder.
No target proof follows: the soft exposure inequality has an accompanying
factor (1-b/A)^j, which deteriorates as the low-count threshold b approaches
the deterministic partial-count floor A. No adequate estimates overcoming
that loss have been established.

In the ideal near-critical linear-sieve model at equal exponent cutoffs beta,
the resampled mean ratio is beta, whereas the reciprocal tail is log(1/beta).
The potential slack 1-beta is smaller than log(1/beta). This model check is
NOT a universal impossibility theorem for resampling, and NOT a negation of
erdos_970. The mean/cylinder strengthening itself has not been formalized here.

No proof or disproof of the original conjecture has been found, and none of
the auxiliary results is claimed to settle it.

## Exact resampled Markov-cylinder bound (VERIFIED, NO SETTLEMENT)

The original erdos_970 is still UNSOLVED. A submission of the unchanged
Spec.lean did not pass verification, as expected from its remaining sorry.
Do not repeat that submission as though a completed proof had been found.

New verified file: Submission/ResampledLowCountCylinder.lean.
Log: /tmp/resampled_low_count_cylinder.log. The final build has no errors,
and all six printed axiom audits contain only propext, Classical.choice,
and Quot.sound. The earlier multiplication-order and disjointness errors
have been repaired. The olean is built.

Exact statements now formalized (superseding the previous note that the
Markov/cylinder strengthening was unformalized):
- populationSurvivors_mean: for any fixed finite population S, independent
  uniform residues on tail R give mean survivor count |S|*density(R).
- populationLowCountFraction_markov_lower: for b>0, the probability of at
  most b survivors is at least 1-|S|*density(R)/b.
- lowCountFraction_union_markov_lower: a fixed core phase r on Q contributes
  (1-intervalCount(Q,m,r)*density(R)/b) * product_{q in Q}(1/q)
  to the full low-count probability on disjoint Q union R.
- lowCountFraction_union_markov_lower_of_count_le: replace the exact core
  count by any certified upper bound D.
- lowCountFraction_markov_lower_of_core: the retained-subset version Q subset P,
  with tail P\Q and corePhase of an arbitrary original phase.
- lowCountFraction_markov_lower_filtered: if the original phase is covered
  and its core-filtered deletion budget is <=D, then
    (1-D*density(P\Q)/b)*product_{q in Q}(1/q)
      <= lowCountFraction(P,m,b).

This keeps the tail-density gain exactly, without making an independence
assumption between interval positions. The lower bound is useful only if
its coefficient is positive. No upper tail estimate strong enough to
contradict it at the required parameters has been proved. In particular,
the soft-exposure penalty (1-b/A)^j must still be charged.

The failed broad conditional-variance proposal was rechecked: the existing
zero-phase counterexample really excludes that proposal; it cannot be used
as a missing concentration lemma. No suitably restricted replacement was
established. No target proof or exact-negation theorem has been found.
Spec.lean remains unchanged, hash
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9,
with its sole sorry at line2177.

## Exact resampling/exposure redundancy (VERIFIED, NO SETTLEMENT)

The original erdos_970 remains UNSOLVED. Three new files and their oleans
compile with only the permitted axioms:
- Submission/ResampledExposureCriterion.lean
- Submission/ResampledExactBudgetBarrier.lean
- Submission/ResampledAveragedFloors.lean
Logs: /tmp/resampled_exposure_criterion.log,
/tmp/resampled_exact_budget_barrier.log, /tmp/resampled_averaged_floors.log.
All final logs have no errors or sorryAx. Intermediate associativity,
implicit-variable, and sdiff-subset errors have been repaired.

This continuation resolves the previously open possibility that the EXACT
factorial budget, unlike its coarse reciprocal-sum bound, might make the
first-moment resampling/cylinder method stronger than deterministic counts.

Exact necessary expression for a cover with retained Q, full P, partial
floor A, depth j, low threshold 0<b<=A, and filtered deletion upper bound D:
  (1-b/A)^j * (1-D*density(P\Q)/b) * product_{q in Q}(1/q)
    <= budget j P
where budget j P = j! * sum_{|T|=j} product_{p in T}(1/p).
The corresponding strict-reverse criterion is formalized, with every
analytic premise retained explicitly.

The new exact limitation is stronger than the earlier coarse-power check:
- budget_lower_of_remaining_sums proves a^d <= budget d R if every remainder
  R\T after fewer than d deletions has reciprocal sum >=a.
- core_weight_mul_budget_le fixes an ordered retained prefix, giving
  product_Q(1/q)*budget d(P\Q) <= budget(d+|Q|) P.
- budget_lower_of_averaged_floors: if D*density(R)<=b and
  A<=D*density(T) for EVERY T subset R with |T|<d, then
  (1-b/A)^d <= budget d R.
- markov_expression_le_exact_budget: under these averaged floors with
  d=j-|Q|, the entire resampled Markov expression is <= the EXACT budget.
  The large-core case |Q|>=j is separately covered by the existing retained
  prefix bound; the nonpositive Markov coefficient case is also handled.

These averaged floors are not artificial additional assumptions:
- uniform_partial_count_of_phase extends any subcore phase to the full P.
- phaseMean_join_count gives the exact conditional mean
  intervalCount(Q,m,r)*density(T) for disjoint extra coordinates T.
- averaged_partial_floor proves
    A <= intervalCount(Q,m,r)*density(T)
  whenever T subset P\Q and |Q|+|T|<j, from the uniform PartialLower input.
- averaged_partial_floor_of_count_le replaces the actual core count by any
  valid upper bound D.

Consequently strict_markov_budget_requires_violated_floor proves that a
strict resampling/exposure comparison MUST exhibit some T subset P\Q with
|T|<j-|Q| and D*density(T)<A. The last theorem,
no_small_core_count_of_strict_markov_budget, obtains the resulting core-count
contradiction directly from deterministic averaging, WITHOUT the full-phase
soft-exposure probability bound.

SCOPE: this closes the specific FIRST-MOMENT Markov-cylinder plus exact
soft-exposure route. It is NOT a barrier to every resampling argument, every
conditional concentration bound, or every sieve method. It is NOT a proof
or disproof of erdos_970. No improved unrestricted growth bound is claimed.
The header's exponent21/10 bound remains the strongest verified one.

Spec.lean remains unchanged, with its original sole sorry at line2177.
No further incomplete proof submission was made during this continuation.

## Post-resampling ordering review (NO NEW THEOREM OR SETTLEMENT)

The original erdos_970 remains UNSOLVED. No edit to Spec.lean was made.
Revisited GreedyCoverOrder, UniqueGreedyCoverOrder,
SortedGreedyAnchorObstruction, GreedySortingObstruction, and the existing
private-cover reoptimization example before pursuing an ordering argument.

The exact reduction permits arbitrary permutations. Existing finite results
rule out first-prime extremality for sorted greedy endpoints and an adjacent
swap loss of at most two. Unique residue-preserving orders exist at unbounded
length/budget ratios, but that construction does NOT have unbounded
length/budget-squared ratio. None of these auxiliary counterexamples excludes
a suitable quadratic-scale amortized comparison. No such comparison, no
uniform increasing-order endpoint estimate, and no valid tensor amplification
of prime covers was established in this review.

Also considered biased/local resampling and cover-sensitive conditional
concentration on paper. These are outside the exact first-moment redundancy
theorem, but no sufficient entropy or conditional fluctuation estimate was
obtained. Do not promote any of these tentative estimates to a proved lemma.
No numerical counterexample scan, proof submission, or claimed new uniform
bound resulted from this continuation. The original sole sorry remains.

## Normalizer-sensitive refinement: log-log squared bound (VERIFIED)

The original erdos_970 remains UNSOLVED. The strongest unrestricted bound
has improved to
  h(k) << k^(21/10)*log(k+2)^(31/10)*(1+log(log(k+3)))^2.
The exact base exponent is still21/10, not2.

New verified files with built oleans:
- WeightedSelbergSharpSource.lean
- BuchstabSharpSource.lean
- BuchstabSharpCost.lean
- BuchstabSharpTransfer.lean
- BuchstabSharpGrowth.lean
All final printed axioms contain only propext, Classical.choice, Quot.sound.
Logs /tmp/weighted_selberg_sharp_source.log and
/tmp/buchstab_sharp_{source,cost,transfer,growth}.log have no errors/sorryAx.
The new source's early binder/associativity errors were repaired before audit.

The weighted Selberg source now charges the SQUARE OF THE EXACT ORDINARY
COEFFICIENT NORM, not support-cardinality squared. sharpSelbergCost is this
actual squared norm at the old cutoff; scaledSharpSelbergCost uses4*D as before.
It is never greater than the old source error and is bounded by
  (exp(2)*cutoff*selbergBase)^2.
The main source is UNCHANGED. Monotonicity of the complete error in source
cost is proved. The upper refinement still charges the MAXIMUM of incurred
errors when its main terms are minimized.

For the actual first-prime reference sequence, if p_i<=E, the strict-prefix
normalizer bound at sqrt(4E) gives
  scaledSharpSelbergCost(i,E) <=64*exp(4)*E/log(p_i)^2.
At every retained lower node the child level is at least its child prime;
this condition is proved, not dropped. The convergent prime sum
sum 1/(p log(p)^2) then bounds the INITIAL lower error by B*D with an
ABSOLUTE constant B=4+64*exp(4)*inverseLogSquareConstant, removing the old
reciprocal-prefix factor. One complete refinement consequently costs
  B*(1+prefixReciprocal(nthPrime,k))^2*D,
rather than a cubed factor. All branches and constant moment errors remain
charged, including discarded lower branches and the upper maximum.

Arbitrary-prime transfer uses the same independent virtual OR hits as before,
with the sharp weighted source. No first-prime extremality is assumed.
The existing verified positive main at divisor exponent21/10 then gives
  exists_refinedBuchstab_sharp_loglog_bound
in namespace Erdos970.RecursiveSieve.Buchstab. Finite small budgets are
absorbed by the already verified explicit finite-sum construction.

Possible next refinement (NOT YET PROVED): split the deepest base indices at
J approximately log(k)/100. At indices<=J the exact kernel norm is bounded
by2^J, independently of the divisor level. Above J, the inverse-log-square
tail is O(1/log(J)^2), which may cancel the two reciprocal-prefix factors.
For D=p_k^(21/10), the small-index term k^2*(J+1)*4^J is plausibly o(D).
A complete finite split estimate and its asymptotic transfer still need proof;
no O(D) complete-error theorem or log-log-free growth bound is claimed here.

Spec.lean remains unchanged with its original sole sorry. No completed target
proof or exact-negation theorem has been found or submitted in this continuation.


## Small-prefix split: log-log-free unrestricted bound (VERIFIED)

The original erdos_970 remains UNSOLVED. Four new files compile with built
oleans and clean audits (propext, Classical.choice, Quot.sound only):

- BuchstabSplitCost.lean: exact sharp Selberg cost <=4^k at every level.
  With H_J=1+(J+1)4^J and T_J=64 exp(4) I/log(J)^2, the COMPLETE depth-one
  lower error, uniformly for prefixes k<=K, is at most
    H_J(1+K^2)+K+T_J D(1+Z_K^2).
  The base cost, the upper refinement's incurred-error maximum, and all
  child costs are retained. The inverse-log-square prime tail controls
  indices above J; the early finite prefix is charged by cardinality.
- BuchstabSplitLevel.lean: choose J=floor(L/100)+3. For L>=1000000 and
  K<=exp(L), the early part is <=exp((21/10)L) and the tail multiplier is
  bounded by an absolute constant. split_complete_error gives the actual
  complete error <=splitLevelConstant*exp((21/10)L), uniformly for k<=K.
  Quantitative absorption uses exp's quadratic Taylor lower bound, not an
  unproved asymptotic cancellation or discarded small-prime cost.
- BuchstabSplitTransfer.lean: arbitrary-prime transfer with any uniform
  exact sharp error budget. No first-prime extremality is assumed.
- BuchstabSplitGrowth.lean: reuses the verified actual reference main
  positivity, Euler density lower bound, nth-prime upper bound, and finite
  small-budget absorption. exists_refinedBuchstab_split_bound proves
    exists C>0, forall k>0, h(k)<=C*k^(21/10)*log(k+2)^(31/10).

Logs: /tmp/buchstab_split_cost.log, /tmp/buchstab_split_level.log,
/tmp/buchstab_split_transfer.log, /tmp/buchstab_split_growth.log.
No pending build. No numerical counterexample search was used.

This removes logarithmic-iteration losses but DOES NOT prove quadratic
order. Spec.lean remains unchanged, sole import and sole sorry preserved,
SHA256 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed target proof or exact-negation theorem has been submitted.


## Four actual refinements: unrestricted exponent51/25 (VERIFIED)

Original erdos_970 remains UNSOLVED. The new unrestricted bound is
  h(k) <= C*k^(51/25)*log(k+2)^(76/25)*(1+log(log(k+3)))^8
for one C>0 and every k>0. Exponent51/25=2.04 improves the preceding2.1
power but remains strictly larger than2. No limiting argument has supplied
an absolute quadratic constant.

New compiled sources and built oleans:
- BuchstabIteratedGrid.lean: reference lower monotonicity in depth,
  depth-indexed prime deficits, general actual tail/sector transfer, and
  UpperGridValid / LowerGridValid with general lower/upper grid steps.
  The upper grid now begins at index50 (s=1), not55, so exponents below2.1
  are supported. Positive lower nodes retain the essential s>=2 guard.
- BuchstabFourGridData.lean: exact integer tables for three more rounds,
  starting from the already verified depth-one grid. The five new initial
  upper nodes at indices50..54 are bounded by the OLD actual lower-deficit
  budget, not by extending the old source estimate outside its domain.
- BuchstabFourGridChecks.lean: kernel-checked local recurrences, terminal
  allowances, seed comparisons, and final upper-integral value2027199 at
  index52. Checks use decide+kernel; no native evaluation is trusted.
- BuchstabFourGridBudgets.lean: telescoping real sum bounds and root budget
  <10149/5000. Initial tail4014/1e6 and deficit tail1962/1e6 are retained.
- BuchstabFourGridMain.lean: actual finite-grid iteration. Final theorem
  exists_referenceLower_four_positive gives rho/250 at exponent51/25,
  above one uniform prime threshold. The prime-sector allowance1/1000 is
  still present in this main-term positivity proof.
- BuchstabDepthSharpCost.lean: upperError_add and
  sharp_lower_depth_le_linear. Exact depth-(n+1) lower error <=
  B*(1+Z)^(2*n+2)*D. This reuses the complete depth-one upper cost, not
  just the error of whichever main term was selected.
- BuchstabDepthSharpTransfer.lean: arbitrary fixed-depth transfer with an
  arbitrary exact sharp error budget uniform over shorter prefixes.
- BuchstabFourGrowth.lean: assembles the complete error, main, Euler bound,
  nth-prime estimate, virtual-hit domination, and finite budget absorption.
- BuchstabFourAudit.lean: all final dependencies are only propext,
  Classical.choice, Quot.sound.

Logs: /tmp/buchstab_iterated_grid.log, /tmp/buchstab_four_data.log,
/tmp/buchstab_four_checks.log, /tmp/buchstab_four_budgets.log,
/tmp/buchstab_four_main.log, /tmp/buchstab_depth_sharp_cost.log,
/tmp/buchstab_depth_sharp_transfer.log, /tmp/buchstab_four_growth.log,
/tmp/buchstab_four_audit.log. No pending build.
The generator /tmp/generate_buchstab_four.py produced the data but its
initially generated Checks source needed routine Fin.val simplifications;
the current compiled source contains those fixes. Do not overwrite it
without carrying the fixes over. /tmp/buchstab_four_data.json records the
integer tables for inspection, but is not a trusted proof dependency.

During the same review, several possible interval/phase approaches were
reconsidered (high lower-tail moments, prime insertion, greedy orders,
conditional row sums, and bilinear remainders). No new cover-excluding
estimate at quadratic length was obtained. No independence of conditional
rows, uniform Gaussian full-centred moments, or first-prime extremality was
assumed. Refinement-grid improvements alone have not crossed the critical
power, and no such crossing is claimed.

Spec.lean is unchanged, exact original theorem/import and sole sorry at2177
preserved; SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed original proof or exact-negation theorem has been submitted.


## Smooth-support cost: all log-log losses and two log powers removed (VERIFIED)

The original erdos_970 remains UNSOLVED. The new unrestricted theorem is
  exists C>0, forall k>0, h(k)<=C*k^(51/25)*log(k+2)^(26/25).
It has a single constant, applies to arbitrary selected prime sets, and
retains every incurred refinement error. It does NOT imply h(k)=O(k^2).

New compiled files with built oleans:

1. SelbergSmoothCost.lean
   w(p)=(p+1)/(p-1), 1<=w<=3. If every selected prime<=Y and logY>=1, then
     sum_{Q:prod(Q)<=R} prod_{p in Q} [w(p)*exp(logp/logY)] <=exp(20)*R.
   Proof uses the ALREADY VERIFIED divisor_cost_sum_le_product with
     b(p)=w(p)*exp(logp/logY)-1,
   not a plain Rankin Euler product that would lose a factor logY.
   The correction sum is<=2 and the tilted extra sum<=18, since
   exp(t)<=1+2t on[0,1] and sum logp/p<=3logY.
   Splitting products at sqrtR then gives the exact weighted-support bound
     sum w(Q) <=(exp2+exp20)*R*exp(-logR/(2logY)).
   The light half is charged by exp2*sqrtR, not discarded.

2. SelbergSmoothKernel.lean
   Applies that sum bound to the exact canonical kernel cost, dividing by
   the actual normalizer. No source main term is changed.

3. BuchstabSmoothSource.lean
   Chooses Y=p_k+1 so logY>=1 even at k=0, and logY<=2logp_k.
   With the existing scaled cutoff R and D>=p_k:
     sharpCost <=64*C_smooth^2*D*exp(-logD/(4logp_k))/logp_k^2.
   For EVERY natural a, an exponential Taylor estimate gives
     sharpCost <=smoothLeafConstant(a)*D*log(p_k)^a/log(D)^(a+2),
   where smoothLeafConstant(a)=64*C_smooth^2*(a+2)!*4^(a+2).
   All statements include the exact canonical source norm.

4. BuchstabSmoothCost.lean
   Define smoothLevelShape(k,D)=D*logp_k/log(D)^3.
   - sum_{i<k} logp_i/p_i <=6logp_k.
   - 1<=12*smoothLevelShape whenever D>=p_k.
   - Every ACTIVE child has D/p_i>=p_i, hence log(D/p_i)>=logD/2.
   - The complete child sum costs at most48*B*shape; adding the unit error
     costs at most60*B*shape. The upper step keeps the incurred-error max.
   - upperError_le_shape has constant C*3600^n, and the final complete
     lower error <=60*smoothLeafConstant(1)*3600^n*shape.
   There is no logarithmically growing prefix sum in this estimate.

5. BuchstabSmoothGrowth.lean
   - smooth_cost_uniform_prefix: full transfer budget for every j<=k.
   - smooth_shape_exp_le: at D=exp(s logp), s>=1, shape<=D/logp^2.
   - eventual_smooth_prime_growth: h(k)<=C*p_k^(51/25)/logp_k eventually.
   - exists_smoothBuchstab_bound: h(k)<=C*k^(51/25)*log(k+2)^(26/25).
   Reuses the verified actual depth-four main rho/250 and Euler comparison.
   The natural interval length is floor(450*A*D/logp)+1; the full cost is
   A*D/logp^2. The ceiling/floor unit is charged explicitly.
   Conversion uses p_k<=160*k*log(k+2) and log(k+2)<=2logp_k, followed by
   finite-small-budget absorption. No asymptotic uniformity is assumed.

6. BuchstabSmoothAudit.lean
   All final printed dependencies are only propext, Classical.choice,
   Quot.sound. No sorry/admit/native_decide/new axiom in these new files.

Logs: /tmp/selberg_smooth_cost.log, /tmp/selberg_smooth_kernel.log,
/tmp/buchstab_smooth_source.log, /tmp/buchstab_smooth_cost.log,
/tmp/buchstab_smooth_growth.log, /tmp/buchstab_smooth_audit.log.
No pending builds or numerical search. The source build emits a harmless
ring normal-form suggestion but no error; the final axiom audit is clean.

The next missing step is still a genuine quadratic-scale argument. A fixed
exponent51/25 cannot be absorbed into the constant, and improved logarithmic
costs do not justify taking a limit to exponent2 with a uniform constant.
An unguarded refinement or arithmetic remainder improvement was discussed
but not proved; no positivity or error estimate for such a modification
has been silently assumed.

Spec.lean remains unchanged: exact original theorem/import, sole sorry2177,
SHA256 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed original proof or exact-negation theorem has been submitted.

## Long-interval occupancy continuation after smooth cost (NO SETTLEMENT)

Original erdos_970 remains UNSOLVED. Re-read OneHitLogConcavity,
OneHitCoreDyadic, OneHitCollisionRemainder, ParityOneHitDyadic,
BalancedCoreDyadic, GapVarianceSubadditive, PowerLossDyadicVoidReduction,
and the earlier exact falling-factorial dilution review.

The adjacent-count covariance theorem remains genuinely second-order. It
does not imply negative covariance of nonlinear completion probabilities.
The affine reduction applies to two-valued core counts, not arbitrary cores.
For medium primes, a single residue may hit both blocks. The existing
collision remainder and core-weight variance cannot be discarded or bounded
by an independence assertion. No uniform sublinear-power dyadic loss was
obtained. The one-hit regime is also not automatically the hard regime of a
normalized cover, whose primes may all be much smaller than the interval.

No new Lean theorem or numerical search was made in this continuation.
The previously audited smooth Buchstab bound remains
O(k^(51/25)*log(k+2)^(26/25)); its exponent is strictly greater than two.
It does not settle the conjecture, and no superquadratic covering family
has been constructed. No incomplete proof was resubmitted.

Spec.lean is unchanged: sole import FormalConjecturesUtil, unchanged target
at line2175, sole sorry at2177, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No build or search worker is pending.

## Truncated lower-tail and count-bootstrap continuation (NO SETTLEMENT)

Original erdos_970 remains UNSOLVED. Re-read QuadraticCountMomentObstruction,
CountMomentPadding, PopulationLowCountBennett, ConditionalSurvivorBennett,
PhaseUnionBennett, ResampledExactBudgetBarrier, ResampledAveragedFloors,
CardinalityBootstrap, CardinalityBlockBootstrap, GroundedSourceClosure, and
the historical exact-integer/quantum bootstrap diagnostics.

A suitably sub-mean truncated high-moment estimate is NOT refuted by the
existing full-centred moment obstruction, but no such estimate was proved.
Conditional Bennett bounds still retain the actual old-population variances
and class caps inside the nonlinear phase average. The aggregate large-sieve
idea does not justify discarding that average or retaining only core entropy.

Quantitative count induction was reconsidered. Smaller-budget positivity
alone gives too weak a terminal count. Stronger count-density hypotheses need
a genuine propagation proof. Reusing lower-count sources obtained from the
same convex recursive envelope does not automatically improve that envelope;
exact floor sources are not covered by the affine-source redundancy theorem,
but the earlier integer diagnostics provide no closing quadratic induction.
No terminal-budget hypothesis was assumed and no unproved source inserted.

A local Mathlib NumberTheory search found no applicable Jacobsthal theorem.
No new mathematical Lean file, numerical search, target proof, or disproof was
produced. Spec.lean remains unchanged with its original sole sorry at2177;
SHA256 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No worker is pending and no incomplete proof was resubmitted.

## Private-position and optimal-exchange continuation (NO SETTLEMENT)

Re-read OptimalCoreExchange, OptimalCoreGapCap, HighMultiplicityPacking,
and BoundedMultiplicityPower. The retained-prime gap cap, private-position
spacing, and exact multiple-replacement inequalities do not presently supply
an O(k) insertion increment or a closing quadratic count inequality. High-
overlap packing does not control all moderate overlaps, and no conversion
to a uniformly bounded-multiplicity cover was proved. No such premise was
assumed. No new Lean theorem or diagnostic was produced; original erdos_970
remains unsolved, Spec.lean unchanged, and no worker is pending.

## Adjacent-certificate scaling review (NO SETTLEMENT)

Re-read the actual ten-term AdjacentShiftExample certificate and shared-
modulus error proof, along with the completed multi-position diagnostic
baselines. Its finite error saving is valid, but the direct fixed-prefix
extension retains a reciprocal-prime sum that is not uniformly below one.
No scalable replacement certificate or quadratic induction was obtained.
The previously run finite LP cases were not rerun or treated as asymptotic
evidence. No new Lean theorem was added. Original erdos_970 and Spec.lean
remain unchanged and unsolved; no proof was submitted and no worker remains.

## Exact long-doubling diagnostics at the budget boundary (NO SETTLEMENT)

Two NEW external exact-integer diagnostics completed. They are NOT Lean
proof dependencies, NOT an asymptotic theorem, and NOT an original-conjecture
counterexample search. Original erdos_970 remains UNSOLVED.

1. /tmp/long_dyadic_gap_exact.py; log/json with the same stem.
   For prefixes of [2,3,5,7,11,13,17,19,23] and every one-prime omission
   from that list, enumerated the reduced-residue gap histogram over the
   complete prime product Q. Checked the identity sum_g g*count(g)=Q.
   Used exact T(m)=sum_g max(g-m,0)*count(g), so V(m)=T(m)/Q.
   Checked Q*T(2m)<=T(m)^2 for every m>=|P| with possibly nonzero T(2m).
   No violation was found. Largest ratio in these cases was about0.4282674
   (first nine primes, m10). This is a finite external computation only.

2. /tmp/long_dyadic_boundary_exact.py; log/json with the same stem.
   Cores: first eight primes, first nine primes, and [2,3,7,11,19,23].
   For every |P|<=m<=100, added exactly t=m-|P| fresh primes. Their first
   prime starts at scale*max(2m,max(P)+1), for scales1,4,64, and subsequent
   primes are consecutive. Thus all tail primes are >=2m and the ACTUAL
   total cardinality is m, meeting the long-interval boundary exactly.
   Enumerated the two actual core count histograms at m and2m. The exact
   one-hit numerators obey a_new(s)=(p-s)*a(s)+s*a(s-1), with common
   denominator product(tail primes); no independent thinning was used.
   Compared the resulting dyadic ratio by Python integer cross products.
   No violation was found. Maximum ratios were about0.4805703,0.4805703,
   and0.2669115 respectively, all at m10 and scale1. Runs finished; no
   counterexample artifact was created and no worker is pending.

These finite tests neither prove LongDyadicVoidBound nor its power-loss
variant. Quantitative one-hit depletion would still need a proof and would
not by itself control medium-prime collisions or nonlinear core averages.
No new mathematical Lean theorem, target proof, or disproof was produced.
Spec.lean is unchanged with its original sole sorry at2177. No incomplete
proof was submitted.

## Ordered-chain depth-uniform power cost (VERIFIED, NO SETTLEMENT)

New development file: Submission/BuchstabOrderedCost.lean.
Its olean is built; log /tmp/buchstab_ordered_cost.log. All three final axiom
prints contain only propext, Classical.choice, Quot.sound. No pending worker.

The ordered-prefix idea now has an actual Lean proof. Define
  orderedPowerProduct(q,a,k) = product_{i<k}(1+q_i^a).
The exact first-hit telescoping identity is
  1 + sum_{i<k} q_i^a*orderedPowerProduct(q,a,i)
    = orderedPowerProduct(q,a,k).
For a>=0, C>=1, nonnegative marginals, the original level-validity hypotheses,
and source cost(k,D)<=C*D^a for D>=1, both the complete upper error and the
complete refined lower error are bounded by
  C*D^a*orderedPowerProduct(q,a,k),
UNIFORMLY IN ALL REFINEMENT DEPTHS. Inactive branches remain zero; active
branch level hypotheses, unit costs, and the upper-error maximum are all kept.
The product is <=exp(sum_{i<k}q_i^a). Hence a power-sum bound Z gives
  refined_lowerError <= C*exp(Z)*D^a
with no dependence on depth or prefix length.

Prime specialization:
  prime_refined_lowerError_le_depth_uniform
uses precisely the old prime power-cost assumptions and proves
  refined_lowerError <= exp(reciprocalPowerConstant(a))*D^a
for every a>1 and every depth. This improves the OLD scalar power-cost bound
(1+reciprocalPowerConstant(a))^(2*n+1)*D^a. It does NOT establish a depth-uniform
version of the sharper smooth logarithmic cost bound. Do not replace the
3600^n in BuchstabSmoothCost by an absolute constant on this basis.

The main-term and quadratic-scale obstacles remain. The actual main-term
positivity still requires an exponent strictly above two; the power cost
still uses a>1. The best verified unrestricted Jacobsthal growth result is
unchanged: O(k^(51/25)*log(k+2)^(26/25)). No limiting argument supplies the
uniform constant in the original quadratic conjecture.

Original erdos_970 remains UNSOLVED. Spec.lean was not edited: original
statement, sole import, sole sorry at2177, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed proof or exact-negation theorem was submitted.


## Ordered prime product, explicit zeta pole, and actual-source transfer (VERIFIED)

Original erdos_970 remains UNSOLVED. New development files compile and all
final printed axioms are only propext, Classical.choice, Quot.sound.

1. Submission/BuchstabOrderedZeta.lean
   - orderedPrimeProduct_le_zeta expands the finite product over prime subsets,
     uses injectivity of their natural-number products, and compares the sum
     with reciprocalPowerConstant(a). It does NOT use exp(zeta(a)).
   - reciprocalPowerConstant_le proves zeta(a)<=1+1/(a-1), a>1, by finite
     antitone integral comparison and the convergent p-series tail.
   - prime_refined_lowerError_le_zeta_mul: for source cost<=C*D, C>=1,
       complete lower error <= C*(1+1/(a-1))*D^a
     for every depth, prime prefix, and nonnegative D. The guards, units,
     and upper-error max remain those of the original verified recurrence.
   - prime_refined_lowerError_le_log_mul chooses a=1+1/log D AFTER fixing D>1:
       complete lower error <= C*exp(1)*D*(1+log D).
     The exponent remains strictly greater than one; no endpoint continuity
     argument or interchange of quantifiers is used. C=1 variants are included.

2. Submission/BuchstabOrderedSharp.lean
   - sharp_refined_lowerError_le_log_uniform instantiates the preceding bound
     with the ACTUAL scaledSharpSelbergCost and its proved source bound4D:
       complete lower error <=4*exp(1)*D*(1+log D).
     This is uniform in depth and arbitrary strictly increasing prime lists.
     The source's factor4 is explicitly retained.

Oleanns built. Logs /tmp/buchstab_ordered_zeta.log and
/tmp/buchstab_ordered_sharp.log. CheckOrderedZeta.lean is an API scratch file
with intentional unknown-name queries and is not a proof dependency.

A NEW external continuous-operator diagnostic was also run:
  /tmp/ordered_cost_operator.py and /tmp/ordered_cost_operator.log.
It is NOT a Lean proof, not an original-conjecture counterexample search,
and not a rigorous obstruction for the actual arithmetic cost. It studies
E=D/(log D)^b*phi(s), s=log D/log p, and the limiting ordered two-hit integral
operator with cubic active-child cutoff. For source phi=s^2*exp(-s/4), it
iterates max(previous,K previous) over a finite quadrature grid1<=s<=100000.
The root values for b=1 stabilize near45.186; b=2 grow approximately linearly
(about277 at depth8,1132 at32,3547 at100); b=3 grow geometrically. These are
floating diagnostics only. They do not prove that a depth-uniform smooth
cost estimate is impossible. The discrete unit errors are not represented
in this continuous operator and must not be omitted in any actual proof.

No critical-scale main term, adequate arithmetic remainder improvement,
quadratic induction, or superquadratic covering family was established.
The best verified unconditional growth theorem stays
O(k^(51/25)*log(k+2)^(26/25)), not O(k^2).

Spec.lean is unchanged, including its sole original sorry at2177 and import:
SHA256 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed target proof or exact negation has been submitted. No worker
is pending.

## Arithmetic odd-multiplicity restriction (VERIFIED, NO SETTLEMENT)

New development file Submission/OddCoverPeriod.lean, importing only
FormalConjecturesUtil. Its olean is built; log /tmp/odd_cover_period.log.
Every final axiom audit contains only propext, Classical.choice, Quot.sound.
No worker is pending.

Namespace Erdos970.OddCoverPeriod:
- periodic_sum_zero_of_block: for functions valued in ANY additive commutative
  group and positive periods p_i, a zero block of length sum p_i forces their
  sum to vanish everywhere. Proof uses finite differences and induction.
- periodic_sum_constant_of_short_block improves the determining length to
  1+sum(p_i-1), sharing the constant component. It works over the same general
  additive group. The proof uses telescoping differences of finite windows,
  period-window constancy, and induction; it does not assume a field or
  invertibility of the periods in the target group.
- hitMultiplicity(P,r,n) counts actual selected prime residue hits.
- odd_cover_length_le_sum_pred: if P is a set of primes and every n<m has
  ODD hit multiplicity, then
       m <= sum_{p in P} (p-1).
  This includes m=0. Over ZMod2, odd multiplicity makes the sum of periodic
  hit indicators equal1. A longer block would force this equality globally;
  CRT supplies an actual offset avoiding every chosen residue, contradiction.
  The proof uses the actual congruence structure, not an independent-moment
  model or an assumed lower-tail estimate.

CRITICAL SCOPE: arbitrary covers need not have odd hit multiplicity. No
conversion from arbitrary covers to odd-multiplicity covers with controlled
prime budget was proved. The conclusion is a SUM-OF-MODULI bound, not a
quadratic CARDINALITY bound. Even for the first k primes the sum of moduli
retains an extra logarithmic factor. It must not be substituted into the
original conjecture as a bound by an absolute constant times k^2.

No target proof, exact negation, new critical-scale main term, or uniform
quadratic covering exclusion was obtained. The best unrestricted bound is
still O(k^(51/25)*log(k+2)^(26/25)). Spec.lean remains unchanged, with its sole
sorry at2177 and SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No incomplete proof was submitted. No numerical search was run in this round.

## Odd-cover overlap check and finite linear obstruction (VERIFIED, NO SETTLEMENT)

Original erdos_970 remains UNSOLVED. Re-read TripleCoverQuadratic,
BoundedMultiplicityPower and HighMultiplicityPacking. Covers with multiplicity
at most3 already have a verified O(k^(3/2)) bound; no new arbitrary-cover
conversion to that restricted case was obtained. The odd-multiplicity
hypothesis alone does not impose a maximum multiplicity of3.

New file Submission/OddCoverExample.lean, olean built. Log
/tmp/odd_cover_example.log. Both final axiom prints contain only propext,
Classical.choice, Quot.sound. Computations use ordinary kernel-checked decide.

Explicit primes {2,3,5,7,11}, residues r5=1, r11=5, and all other r=0,
cover offsets0..10 with hit multiplicities
  3,1,1,1,1,1,3,1,1,1,1.
Thus odd_cover_eleven is proved and not_exact records the triple hit at0.
not_linear_two_odd_cover disproves the auxiliary assertion that every
odd-multiplicity cover has length<=2*prime_count-1: 11>2*5-1.
It does NOT refute a quadratic bound or any original-conjecture proposition.
This example was derived directly and checked exactly, not found by a blind
numerical scan.

The new example blocks conflating odd covers with exact covers or importing
the exact-cover linear bound into the odd-cover case. The sum-of-moduli
restriction from OddCoverPeriod remains valid but does not supply a quadratic
cardinality bound. No parity-removal or controlled overlap-reduction theorem
was established. The best unrestricted upper bound remains unchanged.

Spec.lean remains unchanged, with its sole sorry at2177 and SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed original proof or exact negation was submitted. No worker pending.

## Arbitrary-index support counting obstruction (VERIFIED, NO SETTLEMENT)

`Submission/IndexSupportCost.lean` imports only FormalConjecturesUtil and
compiles; its olean is built. Namespace Erdos970.IndexSupportCost defines
indexSupport R as subsets of Icc 2 R with product at most R.

* pair_count_le injects ordered pairs a<=N<b<=R/a into two-element supports.
* harmonic_lower proves
    card(indexSupport R) >= R*(harmonic N-1) - N*(N-1)
  when N>=2, R>=N, and every a in Icc 2 N divides R.
* factorial_cutoff_lower uses R=N!*(N+1)^2 to obtain
    card(indexSupport R) >= R*(harmonic N-2).
* not_linear_support_bound proves there is no real C bounding all these
  cardinalities by C*R. The only axioms are propext, Classical.choice,
  Quot.sound. Build log: /tmp/index_support_cost.log.

This invalidates a naive reuse of distinct-prime product injectivity for
arbitrary index-product supports. It does not rule out weighted index schemes
and has no bearing on the truth or falsity of erdos_970. The existing
SelbergPositiveOptimum.cutoff_minimizes already proves nonnegative-cone
optimality of the actual p+1 height cutoff; it was not reproved here.

Spec.lean remains unchanged with its original sorry. No proof or disproof of
the quadratic conjecture was found. No incomplete proof was resubmitted.


## Linear-length stretched void and unrestricted polynomial doubling loss (VERIFIED)

New development files (all oleans built; all audits use only propext,
Classical.choice, Quot.sound):

1. GeneralExposureTail.lean (91 lines), namespace Erdos970.GapAverages.
   log_factorial_upper uses the monotonic Stirling sequence to prove
     log(j!) <= j log j-j+1+(log j)/2.
   generating_core_tail_bound_of_le accepts any positive reciprocal budget.
   coveredFraction_le_general_core proves
     V_P(m) <= exp(|S| log(1+j/delta)+1+(log j)/2+j log delta)
   whenever IsJacobsthalBound(j-1,m), j>0, S subset P, and the reciprocal
   sum over P\S is <=delta, delta>0. No delta<1 is silently assumed;
   exponential saving follows only on specializing to delta<1.
   Log: /tmp/general_exposure.log.

2. ThreeEighthTail.lean (74 lines), namespace Erdos970.WeightedMertens.
   For |P|<=t^80 and one sufficiently large absolute D, the reciprocal
   sum over p>D*t^30 is <=199/200. Uses the existing sharp coefficient
   prime_set_tail and an exact rational-power proof log(8/3)<=99/100.
   Log: /tmp/three_eighth_tail.log.

3. LinearExposureTail.lean (146 lines), Erdos970.GapAverages.
   On k<=t^80<=2^80*k, the verified 5/2 bound gives
     IsJacobsthalBound(t^31-1,k)
   eventually. The core has size <=D*t^30+1, so its logarithmic entropy
   and the Stirling overhead are eventually <=t^31/400. With delta199/200,
   the saving is at least t^31/400. Main theorem:
     eventually_linear_stretched_void:
       eventually k, all prime P with |P|<=k,
       coveredFraction P k <= exp(-k^(31/80)/400).
   Kernel recursion on concrete huge constants was fixed by proving the
   generic theorem eventually_linear_stretched_void_of_constants first,
   then specializing D and B. No kernel checks were disabled.
   Log: /tmp/linear_exposure_tail.log.

4. PolynomialLossDyadicReduction.lean (130 lines), Erdos970.GapAverages.
   eventually_polynomial_scaled_void_base absorbs A*(k+2)^alpha into the
   preceding bound for EVERY fixed alpha>=0 and A>0. It then reuses the
   exact dyadic iteration and bounded-prime phase normalization:
     eventually_quadratic_of_polynomial_dyadic:
       A>=1, alpha>=0, PowerLossDyadicVoidBound A alpha
       ==> eventually k, jacobsthalFunction k<=128*k^2.
     quadratic_bound_of_polynomial_dyadic:
       same hypotheses ==> the exact unchanged conjecture's conclusion.
   Unlike the previous PowerLossDyadicVoidReduction result, there is no
   alpha<1 hypothesis. The PowerLossDyadicVoidBound premise is STILL
   UNPROVED. This is not an unconditional quadratic bound.
   Log: /tmp/polynomial_loss_dyadic.log.

The earlier review of long doubling still applies: adjacent count covariance
is only second-order; nonlinear completion events cannot be declared
negatively correlated. Medium-prime collisions remain uncontrolled. The
new result relaxes the permitted loss, but does not prove any such loss.

The unrestricted growth bound remains
  O(k^(51/25)*log(k+2)^(26/25)).
No genuine proof or disproof of erdos_970 was found. Spec.lean is unchanged,
sole sorry at2177, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No worker is pending and no incomplete proof was submitted.

### Post-reduction two-block rearrangement check (NO TARGET SETTLEMENT)

Considered the stronger claim that adjacent m-blocks minimize joint coverage
among all separations. A targeted exact-integer diagnostic disproved that
stronger assertion even when m>=|P|. For P={2,3,5,7,11,13}, period30030:
  m8: adjacent joint numerator28, separation190 numerator24;
  m9: adjacent8, separation33 gives4;
  m10: adjacent4, separation34 gives0.
Counts were computed from the complete coprimality cycle, with exact sliding
window counts and set-membership autocorrelations. These numbers are NOT
Lean-checked proof dependencies. This does NOT refute void doubling relative
to the average (V(m)^2), or its polynomial-loss version. It only rules out a
pointwise-in-separation rearrangement proof of that version. No cover search
for the original conjecture was performed; no worker remains active.

## Insertion and greedy-reordering follow-up (NO NEW SETTLEMENT)

After the linear-length stretched-void improvement, revisited the exact
GreedyCoverOrder reduction, GreedySortingObstruction, SortedGreedyAnchorObstruction,
IncrementReduction, TwoSurvivorReduction, and SymmetricIsolation. No adjacent
swap scan or cover search was repeated.

The local loss<=2 assertion is already disproved; neither a larger uniform
local bound nor a sufficiently cheap amortized sorting comparison follows
from that example. A proof for increasing greedy orders would also require
an actual stopping-point estimate, not monotonicity under prime replacement
(which is already disproved). No such estimates were obtained. The global
largest-prime insertion increment likewise does not follow from the local
companion property refuted by SymmetricIsolation. No unproved increment or
sorting hypothesis was inserted into a theorem.

The polynomial-loss dyadic reduction remains a genuine conditional route,
but its nonlinear doubling premise was not proved. The new unconditional
linear-length bound remains valid and axiom-clean. No new mathematical Lean
file was added in this follow-up. Spec.lean is unchanged with its original
sole sorry at2177. No completed proof/disproof was submitted and no worker
is pending.

## Sharper linear exposure and fractional doubling reduction (VERIFIED, CONDITIONAL)

SharperLinearExposure.lean (171 lines) improves the unconditional linear-length
void estimate to V_P(k)<=exp(-k^(37/80)/400), eventually and uniformly for |P|<=k.
It uses the smooth Buchstab bound at exposure depth t^37, k~t^80, with the same
core cutoff D*t^30 and reciprocal tail 199/200. Generic constants avoid kernel
recursion. Log /tmp/sharper_linear_exposure.log; axiom audit clean.

SquareCubicDyadicReduction.lean (242 lines) defines the UNPROVED condition
  V_P(2m)^2 <= A*(|P|+2)^alpha*V_P(m)^3, m>=|P|.
For any fixed A>=1 and alpha>=0, this condition implies the exact original
conclusion; indeed eventually h(k)<=k^2. The scaled iteration gives exponent
5 per length factor16, and 16^9<=5^16 combines with 37/80 to give41/40>1.
Log /tmp/square_cubic_dyadic.log; axiom audit clean. This is not an unconditional
proof. The square-cubic premise and any analogous Laplace estimate remain
unproved. Earlier counterexamples to squared-probability doubling do not
by themselves refute the weaker square-cubic condition.

Spec.lean remains unchanged with sole sorry2177. No final settlement.

## Fractional two-block review (NO SETTLEMENT)

Revisited the arithmetic dependence of adjacent blocks after the square-cubic
reduction. Independent residue coordinates do not make the two block coverage
events independent: each small or medium prime can influence both blocks.
The verified pair-count covariance and conditional Chernoff estimates do not
bound the nonlinear joint event. Conditioning on all shared coordinates incurs
an entropy cost too large for the available linear-length stretched-exponential
base. No bound on that cost, no fractional Laplace inequality, and no unconditional
square-cubic void inequality was proved. No conjectural premise was promoted
to a theorem. Spec.lean is unchanged and remains incomplete.

## Deterministic and lower-tail follow-up (NO NEW SETTLEMENT)

Revisited the global insertion/two-survivor formulation, optimal-core exchange
inequalities, and ordered-cover formulation. The existing adjacent-gap scans
already test the proposed insertion consequence for substantial finite families;
these were not rerun. They neither refute nor prove LargestPrimeIncrement.

Checked a possible small-period/sparse-tail improvement of OddCoverPeriod.
The local-to-global recurrence rules out a constant block but supplies no
adequate lower bound on the number of parity defects in a nearly constant
block. Treating its recurrence order as an additive sparse-error budget was
not justified. No quadratic odd-cover claim was added, and no arbitrary-cover
to odd-cover conversion is available.

Also revisited endpoint conditioning of the count distribution. The existing
kernel-checked counterexamples already rule out the naive stochastic-domination
and unit-density-hazard arguments. They do not rule out every weaker tilted
lower-tail estimate, but no such estimate was proved. A Mathlib search found no
direct Jacobsthal/Iwaniec/coprime-interval theorem supplying the missing bound.

No new mathematical Lean file, unproved assumption, or target modification was
made. Spec.lean retains its original sorry at2177 and hash
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No worker is pending and no completed proof/disproof was submitted.

## Near-critical power exposure (VERIFIED, NO TARGET SETTLEMENT)

Two new axiom-clean Lean files compile; their oleans are built:

1. PowerExposureBudget.lean
   log_power_add_two_le and log_power_add_two_rpow_le bound the logarithmic
   source term without replacing it by a whole power of t. The general result
   eventually_smooth_power_envelope proves
     h(t^a) <= t^b/2^b, eventually t,
   for positive integral a with a*(51/25)<b, from the already verified smooth
   Buchstab bound. It uses Mathlib's log-rpow little-o theorem with exponent
   b-a*(51/25)>0. eventually_power_exposure_budget gives the corresponding
   IsJacobsthalBound(t^a-1,k) whenever t^b<=2^b*k.
   Log: /tmp/power_exposure_budget.log.

2. NearCriticalExposure.lean
   Uses a196,b400 and core cutoff D*t^150. The reciprocal-tail lemma is applied
   at t^5, so (t^5)^80=t^400 and (t^5)^30=t^150. An explicit overhead bound
   under78800*(D+2)<=t absorbs the core entropy into t^196/400.
   Main theorems, namespace Erdos970.GapAverages:
     eventually_near_critical_linear_void:
       eventually k, all prime P with |P|<=k,
       V_P(k) <= exp(-k^(49/100)/400).
     eventually_power_length_void:
       for each positive integer r, eventually k,
       V_P(k^r) <= exp(-k^(r*49/100)/400).
     eventually_near_critical_quadratic_void:
       V_P(k^2) <= exp(-k^(49/50)/400), uniformly and eventually.
   This improves the earlier37/80 linear and4/5 quadratic exponents.
   eventually_subcritical_envelope_above_entropy explicitly proves that, for
   every fixed A>0, eventually
     exp(-k*log(k+2)) < exp(-A*k^(49/50)).
   This compares bounds only: it does NOT assert a lower bound on V_P.
   Thus merely enlarging a fixed quadratic interval constant does not make
   this particular estimate exclude a phase atom.
   Log: /tmp/near_critical_exposure.log.

An elaboration timeout from convert on nested powers was resolved with explicit
pow_mul rewrites before applying the reciprocal-tail theorem. No checking was
disabled. Final printed axioms are precisely the permitted three. No worker is
pending. Spec.lean is unchanged, original theorem still unsolved with sorry2177;
no incomplete proof was submitted.

## Continuous refinement proposal and endpoint review (NOT YET VERIFIED)

Proposed model on s>=1:
  (K u)(s) = (1/s) integral_[max(2,s-1),infinity)
                 (1/t) integral_[t-1,infinity) u(v) dv dt,
  g(s)=max(3-s,0)/s, u_(n+1)=g+K u_n.
A hand calculation suggests K(exp(-s)) <= (19/20)*exp(-s): use
  integral_2^infinity exp(-t)/t dt
    <= exp(-2)/3+exp(-3)/12+exp(-4)/12,
from the reciprocal secants on [2,3] and [3,4], then 1/t<=1/4.
The moment identity would be M_(n+1)=2+M_n-U_n, where
  M_n=integral_1^infinity s*u_n(s) ds, U_n=integral_1^infinity u_n(s) ds.
These analytic claims have NOT YET been Lean-proved or transferred to the
actual finite-prime refinement. The primeKeep square cutoff remains essential.

A completed numerical diagnostic /tmp/buchstab_endpoint_rate.py (mesh 1e-4,
cutoff30, 1000 rounds) suggested rapid approach of the coarse positivity
threshold to2: about2.13123 initially,2.001386 at round8,2.00000770 at16,
with a mesh floor near2.00000000250. This is NOT proof evidence or a dependency;
do not rerun it or interpret its floor as positivity at2.

Endpoint review: even exact continuous convergence only yields positivity
strictly above2; the model lower profile vanishes at2. Together with current
source costs, an endpoint-uniform argument still incurs logarithmic losses.
It is not a quadratic theorem. The six-prime unit-density hazard counterexample
already has length9>=budget6, so restricting to lengths above the budget does
not rescue that stronger hazard claim. No nonlinear correlation premise was
proved in this review. Spec.lean remains unchanged and incomplete.

## Continuous Buchstab contraction and finite-depth positivity (VERIFIED MODEL ONLY)

Five new files compile, all printed axioms permitted:
  ContinuousBuchstabKernel.lean       148 lines
  ContinuousBuchstabOperator.lean     139 lines
  ContinuousBuchstabMoments.lean      163 lines
  ContinuousBuchstabIteration.lean    142 lines
  ContinuousBuchstabPositivity.lean   121 lines
Namespace Erdos970.ContinuousBuchstab. Oleans are built (no sorry dependencies).

The previously proposed contraction is now verified by a simpler rational
moment majorant, NOT by the numerical diagnostic or the secant proposal:
  1/(u+2) <= (u^2-6u+16)/32, u>=0,
whose error is u*(u-2)^2/(32*(u+2)). Consequently, for every a>=2,
  integral_a^infinity exp(-t)/t dt <= (3/8)*exp(-a).
This proves kernel_exp_le: K(exp(-s)) <= (19/20)*exp(-s), s>=1.
The operator file proves measurability, absolute-envelope contraction,
linearity under the stated integrability conditions, and monotonicity.

ContinuousBuchstabMoments proves the general shifted triangle Fubini identity,
with absolute integrability supplied explicitly. Its kernel_first_moment says
  integral_1^infinity s*(K u)(s) ds
    = integral_1^infinity (v-1)*u(v) dv
for measurable u bounded in absolute value by C*exp(-s) on s>=1.

For forcing(s)=max(3-s,0)/s, u_0(s)=2000*exp(-s), and
  u_(n+1)=forcing+K u_n,
ContinuousBuchstabIteration proves nonnegativity, decreasing iterates, and
  |u_n(s)-u_(n+1)(s)| <= 2000*(19/20)^n*exp(-s).
ContinuousBuchstabPositivity proves, writing U_n=integral_1^infinity u_n:
  2 <= U_n <= 2+24000*(19/20)^n.
  lowerProfile(n,s) >= (s-2-24000*(19/20)^n)/s, s>=2.
  exists_depth_uniform_positive: for every epsilon>0, one finite n satisfies
    epsilon/(2*s) <= lowerProfile(n,s), for ALL s>=2+epsilon.
  clamped_lowerProfile_two: max(0,lowerProfile(n,2))=0 for EVERY n.
Thus strict fixed-level positivity is genuinely verified, and the endpoint
limitation is also genuinely verified. This is NOT a Jacobsthal theorem.
No prime-sum transfer, quantitative depth-uniform prime error, or quadratic
bound has been proved. Existing unrestricted growth bound remains unchanged.

Build/audit logs: /tmp/continuous_buchstab_{kernel,operator,moments,iteration,positivity}.log.
Spec.lean remains unchanged, sole original sorry2177, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No proof/disproof of the original conjecture has been submitted.

Next investigation: finite-sector transfer supports arbitrary finite partitions
(BuchstabSectorSums), but current grid files hardcode mesh1/50 and cutoff12.
A general truncation can use the existing eighth-power moment tail estimates
with R=floor(exp(L/M)), M>=13, to obtain a tail tending to zero like M^(-7).
This has NOT YET been generalized or connected to the new continuous profiles.

## Final bootstrap review after continuous positivity (NO SETTLEMENT)

Reviewed ContinuousIntervalSeedRobustness, CardinalityBootstrap,
CardinalityBlockBootstrap, and ReferenceCardinalitySource. The fixed-seed
comparison still requires a quadratic-positivity premise. Single-block and
repeated-block smaller-cardinality estimates do not turn the new s>2 model
positivity into an endpoint theorem. No such bridge was established or
asserted. Spec.lean is unchanged and still incomplete. No incomplete proof
was submitted. No worker is pending.

## Arbitrary-exponent finite-prime transfer (VERIFIED, NO QUADRATIC SETTLEMENT)

Ten new development files compile and their oleans are built. Their printed
axioms are only propext, Classical.choice, Quot.sound:
  BuchstabVariableTail.lean                261 lines
  ContinuousBuchstabMonotone.lean           79 lines
  ContinuousBuchstabRectangles.lean         67 lines
  BuchstabProfileSectors.lean              114 lines
  BuchstabProfileTransfer.lean             135 lines
  BuchstabExponentialSource.lean           107 lines
  ContinuousBuchstabDeficit.lean           125 lines
  BuchstabContinuousLowerTransfer.lean     104 lines
  BuchstabContinuousMain.lean              129 lines
  BuchstabArbitraryGrowth.lean             179 lines

1. Variable tails use terminalCut(M,L)=floor(exp(L/M)), M>=13, and
   terminalAllowance(B,M)=9B/(35M^7)+18B*sharpMomentError/(5M^6).
   Both actual primeUpperExcess and primeDeficit tails are at most this
   allowance divided by the root level, uniformly in EVERY refinement
   depth and every root level>=1. The allowance can be arbitrarily small,
   with M also larger than any prescribed threshold. The fixed wheel and
   the explicit Mertens-moment remainder are retained.

2. General real profile sectors replace hardcoded grid nodes. Exact prime
   density telescoping yields each sector's limiting mass. Complete sums
   include the terminal tail, finite-sector slack, and the distinction
   between strict-prefix Euler mass and inclusive initialEulerMass.

3. Nonnegative antitone continuous profiles admit arbitrarily fine finite
   upper rectangle sums. upperEnvelope is antitone, lowerProfile monotone.
   The clipped deficitProfile equals1 below2 and min(1,tail(u_n)/s) above2.
   It is nonnegative, antitone and integrable; its COMPLETE tail divided
   by the root level is bounded by upperEnvelope(n+1). No clipping or
   below-square-cutoff contribution is discarded.

4. BuchstabExponentialSource proves one prime threshold controls every
   s>=1 for the actual source: referenceUpper(0)<=density*(1+2000*exp(-s)).
   Small levels use the logarithmic normalizer lower bound, the middle
   range uses the cubic source estimate, and s>=6 uses the Rankin tail.

5. UpperModelApprox(n) and LowerModelApprox(n) assert actual prime-main
   approximation with arbitrary fixed positive slack, at every fixed
   level in their respective domains s>=1 and s>=2. Lower transfer
   partitions its error into terminal, rectangle, node and sector budgets.
   Upper transfer uses the clipped deficit and the analogous budgets.
   continuous_model_transfer proves BOTH predicates for every fixed n.
   exists_referenceLower_positive_above_two proves: for every fixed s>2,
   some n,N satisfy, for every prime prefix k with N<=p_k,
     density(k)*(s-2)/(4s) <= referenceLower(n,k,exp(s*log p_k)).

6. BuchstabArbitraryGrowth combines that actual main with the existing
   fully charged smooth cost at the chosen fixed depth. It proves
     eventual_prime_growth_above_two: h(k)<=C_s*p_k^s/log p_k eventually;
     exists_growth_above_two: h(k)<=C_s*k^s*log(k+2)^(s-1), all k>0;
     exists_near_quadratic_bound: h(k)<=C_epsilon*k^(2+epsilon), all k>0.
   The last theorem absorbs the logarithm at the intermediate exponent
   s=2+epsilon/2 and then absorbs finitely many budgets. This does NOT
   bound C_epsilon uniformly or prove the epsilon=0 conjecture.

Logs are /tmp/buchstab_variable_tail.log, /tmp/continuous_buchstab_monotone.log,
/tmp/continuous_buchstab_rectangles.log, /tmp/buchstab_profile_sectors.log,
/tmp/buchstab_profile_transfer.log, /tmp/buchstab_exponential_source.log,
/tmp/continuous_buchstab_deficit.log, /tmp/buchstab_continuous_lower_transfer.log,
/tmp/buchstab_continuous_main.log, /tmp/buchstab_arbitrary_growth.log.
Final audit: /tmp/buchstab_arbitrary_growth_final_audit.log.

Endpoint review: merely choosing s closer to2 does not prove a quadratic
bound. The model main vanishes at2, the prime thresholds are existential
and depth-dependent, and the smooth coefficient cost has its stated
3600^n factor. No endpoint improvement or new nonlinear void correlation
bound was proved. The minimal-counterexample/cardinality bootstrap review
also supplied no such bridge. These gaps remain mathematical, not merely
Lean elaboration issues.

Spec.lean is unchanged, sole sorry2177, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No incomplete proof/disproof was submitted and no worker is pending.


## Arbitrary subcritical exposure and relaxed correlation reduction (VERIFIED)

Three new development files compile, with audits using only propext,
Classical.choice, Quot.sound:
  ArbitraryExposureBudget.lean
  ArbitrarySubcriticalExposure.lean
  SubexponentialSquareCubicReduction.lean

1. eventually_subsquare_exposure_budget uses epsilon=1/(a+1) to turn any
   strict integral exponent gap2*a<b into an eventual bound
     IsJacobsthalBound(t^a-1,k), whenever t^b<=2^b*k.
   The fixed near-quadratic constant is absorbed into a positive power of t.

2. general_exposure_core_cost and general_exposure_core_envelope handle
   arbitrary integral exposure/core exponents a,c with c+2<=a. The
   parameterized choice is a=40*j+39, b=80*(j+1), c=30*(j+1).
   The reciprocal tail uses the existing three-eighths Mertens bound at
   t^(j+1), retaining delta=199/200. The finite core overhead is explicitly
   charged, with sufficient threshold400*(a+3)*(D+2)<=t.
   eventually_subhalf_linear_void gives every fixed sigma<1/2.
   eventually_subone_quadratic_void gives every fixed sigma<1.
   These have exponent constant1/400, but NONUNIFORM thresholds.

3. SubexponentialSquareCubicVoidBound C beta is an EXPLICIT UNPROVED premise:
     V_P(2*m)^2 <= exp(C*|P|^beta)*V_P(m)^3, for m>=|P|.
   quadratic_bound_of_subexponential_square_cubic proves the original
   conclusion CONDITIONALLY on this premise, C>=0, and0<=beta<1.
   Proof chooses an integer b with b*beta<b-17/32, uses budget K=t^b and
   seed length m=t^(2*b-1), and chooses the linear seed exponent so that
   m^sigma=t^(b-17/32). The loss is absorbed by this strictly larger power.
   Four doublings amplify by5 at length factor16. Taking j=floor(log_16 t)
   supplies an additional exponent9/16, making total exponent b+1/32.
   This beats the complete normalized phase entropy O(t^b*log t).
   Interpolation from power budgets gives h(k)<=(2^b)^2*k^2 eventually,
   and finitely many exceptions are absorbed. The premise is NOT removed.

4. Reviewed the actual OneHitCoreCorrelation proof: conditioning on shared
   core phases charges the product of all core primes, not merely their
   cardinality. Its one-hit condition requires remaining primes>=2*m.
   It does not imply the new sublinear-power-loss premise for arbitrary
   prime sets. No medium-prime correlation theorem or endpoint estimate
   was obtained. Full-centered high moments are already disproved; no such
   shortcut was used. Truncated low-tail moments remain unproved.

Build/audit logs: /tmp/arbitrary_exposure_budget.log,
/tmp/arbitrary_subcritical_exposure.log, /tmp/subexponential_square_cubic.log.
Spec.lean remains unchanged with the sole original sorry at2177, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No proof or disproof of the original conjecture has been submitted.

## Endpoint structural review after arbitrary exposure (NO SETTLEMENT)

Revisited IncrementReduction, TwoSurvivorReduction, EssentialCoverOrder,
UniqueGreedyCoverOrder, CardinalityBootstrap, CardinalityBlockBootstrap,
ReferenceCardinalitySource, TripleCoverQuadratic, QuadraticOverlapReduction,
and HighMultiplicityPacking. No new implication closing the endpoint was found.

- Largest-prime insertion still needs the global two-survivor gap estimate
  (and, for smaller insertion primes, control of longer merged runs). The
  local isolation and one-prime exchange facts do not supply it.
- The bounded-multiplicity quadratic probe is genuinely positive on average,
  but moderate overlap mass is not controlled for an arbitrary cover. No
  exactification or bounded-multiplicity conversion has been established.
- A prospective stronger count profile with affine slope comparable to
  1/log k might support insertion near its zero threshold. The trivial
  deletion cap m/p does NOT propagate that profile at arbitrary lengths;
  the slope loss is too large. No strong count induction was asserted.
- Considered tensor amplification of a hypothetical cover to try to turn
  near-quadratic estimates into an endpoint theorem. No valid amplification
  with multiplicative cardinality was obtained: the naive construction
  introduces composite moduli or repeated primes, and is not admissible.
- Revisited concentration after conditioning on a small-prime core. Uniform
  class caps and the full core phase entropy retain insufficient losses.
  Neither independence of medium-prime hits nor a smaller entropy cost was
  assumed. A dense lower count at level two would be a new unproved input.

No new mathematical Lean file or numerical counterexample search was needed
for this review. The existing unrestricted near-quadratic bounds and
subcritical void bounds remain valid, but the original conjecture is still
unsolved. Spec.lean remains unchanged with its original sole sorry at2177.
No incomplete proof or disproof was submitted in this continuation.

## Eventual lower growth and quantum comparison budget (VERIFIED)

The following new files compile and their main theorems use only propext,
Classical.choice, Quot.sound:
  EventualLowerAsymptotic.lean
  ContinuousIntervalQuantumActualBudget.lean
  ContinuousIntervalQuantumLogBudget.lean

1. eventually_square_cover_budget extracts a fixed-A square covering with
   prime budget j*log(t) <= (log(4)+2)*t^2, the leading constant independent
   of A. Floor/square-root interpolation and strict monotonicity give
   eventually_any_mul_log_lt_jacobsthalFunction, and hence
   jacobsthal_mul_log_ratio_tendsto_atTop:
     h(k)/(k*log(k)) -> infinity.
   This is compatible with h(k)=O(k^2), and does not prove summability of 1/h(k).

2. actualQuantumDilationBudget is the product over i<k of
   (h(i+1)+1)/(h(i+1)-1). Soundness makes the quantum lower envelope zero
   below h(k). A regular-function comparison then proves that this dilation
   of the ordinary reference envelope dominates every guarded quantum
   trigger schedule, with NO subsequent chord patches. The zero lemma
   itself permits arbitrary chord schedules; the accumulated comparison does not.

3. reciprocal_log_step telescopes reciprocal logarithmic costs. The eventual
   lower growth above implies, for every epsilon>0, a C_epsilon>0 with
     actualQuantumDilationBudget(k) <= C_epsilon*log(k+2)^epsilon.
   quantumReference_log_dilation gives the corresponding envelope comparison,
   uniformly in the trigger schedule. Constants depend on epsilon; no
   bounded epsilon=0 budget or quadratic conclusion was obtained.

Logs: /tmp/eventual_lower_asymptotic.log, /tmp/quantum_actual_budget.log,
/tmp/quantum_log_budget.log. One harmless linter warning occurs in the first.
Spec.lean remains unchanged with its original sole sorry at2177.

A proposed polynomial zero barrier for the ordinary reference envelope was
outlined but NOT PROVED: freeze U_i(y) once i>=ceil(y), obtain a uniform
Euler-density source c*y/log(y+3), and compare finite logarithmic sectors
of subtraction costs against the prefix density. A possible subsequent
bounded effective quantum budget likewise remains unproved. Neither
claim is a result about the actual Jacobsthal endpoint.

## Ordinary polynomial barrier and bounded effective quantum comparison (VERIFIED)

Five new files compile. Their printed main theorem axioms are only propext,
Classical.choice, Quot.sound:
  ContinuousIntervalUpperFreezing.lean
  ContinuousIntervalSectorCosts.lean
  ContinuousIntervalPolynomialBarrier.lean
  ContinuousIntervalQuantumEffectiveBudget.lean
  ContinuousIntervalQuantumBoundedDilation.lean

1. envelope_upper_freezes_sqrt improves the earlier planned cutoff: for
   q_i<=1/(i+2), U_k(y) is constant for k>=ceil(sqrt(y)). The lower argument
   (y+1)q_i-1 is then <=i, where the ordinary lower branch is already zero.
   reference_upper_log_source gives, uniformly in k and y>=0,
     U_k(y) >= exp(-reciprocalConstant-1)*y/log(sqrt(y)+3).

2. Exact prime-counting coordinate bridges identify prefix density with
   1/initialEulerMass(n). Under positivity of L_n(x), the unclipped costs
   telescope, so reference_positive_prime_tail_cost bounds their sum by
   x/initialEulerMass(m). Mertens gives at least (b-a)/2 reciprocal mass
   in each fixed exponent sector 0<a<b<=1, eventually. Uniform freezing
   lower-bounds each corresponding upper cost at exponential length.

3. exists_polynomial_ordinary_zero_barrier proves there exists delta>0 with
     L_k(k^(1+delta))=0 eventually.
   The construction uses finitely many sectors a_j=1-2^(-j-1), with
   delta=2^(-N-1), and the Euler-product limit at exponent1/2. Each sector
   costs at least c*x/(12*L); N is chosen to beat the prefix budget A*x/L.
   This is a limitation of the ORDINARY LOWER ALGORITHM, not a lower bound
   on h(k). It does not show that the algorithm fails at quadratic length.

4. effectiveQuantumDilationBudget charges quantumDilationFactor(trigger_i)
   exactly when the actual pre-patch guard succeeds, and factor1 otherwise.
   quantumEnvelope_effective_dilation proves this exact product dominates
   every unchorded quantum schedule, including arbitrary failed triggers.

5. Combining the existing actual budget o(k^epsilon), canonical domination,
   and the ordinary polynomial zero barrier shows successful triggers grow
   faster than (i+1)^(1+eta), for one eta>0, uniformly in every schedule.
   The effective factor is then <=exp(4/(i+1)^(1+eta)) eventually. The
   p-series is summable; early factors are uniformly<=3. Hence the effective
   product is bounded by one finite constant independent of stage/schedule.
   quantumReference_bounded_dilation compares EVERY guarded quantum schedule
   with ONE FIXED DILATION of the ordinary reference envelope. It explicitly
   excludes subsequent chord patches. No summability of 1/h(k) was assumed.

Logs: /tmp/upper_freezing.log, /tmp/sector_costs.log,
/tmp/polynomial_barrier.log, /tmp/quantum_effective_budget.log,
/tmp/quantum_bounded_dilation.log. Some harmless unnecessarySeqFocus warnings.

The original quadratic conjecture is STILL UNSOLVED. No endpoint positivity
or superquadratic covering construction was obtained. Spec.lean is unchanged,
sole sorry2177, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No complete proof/disproof has been submitted.

## Endpoint-only continuation after bounded quantum comparison (NO SETTLEMENT)

Reviewed the remaining endpoint reductions rather than extending auxiliary
algorithm barriers. No new mathematical implication settling the endpoint
was obtained, and no numerical counterexample scan was run.

- LargestPrimeIncrement still needs a GLOBAL two-survivor estimate (and
  additional control when the inserted prime is smaller than an old gap).
  A local isolation or private-witness argument does not establish it.
- The quadratic overlap probe retains moderate multiplicity mass. Plain
  high-overlap packing cannot discard that term; for large prime prefixes
  the average hit multiplicity itself grows, so a uniformly tiny unweighted
  moderate-mass estimate must not be assumed.
- Considered coding/branching of residue-preserving greedy orders. The
  verified factorial encoding and uniqueness obstructions remain relevant;
  no quadratic-scale lower bound on encoding multiplicity or suitable
  uncrossing theorem was found.
- Conditional lower-tail concentration retains actual class caps and
  variances. Bounding these only by interval length divided by the prime
  does not give enough phase-entropy control. No mean-to-worst-case or
  medium-prime independence step was assumed.
- Checked SelbergSmoothKernel, BuchstabSmoothSource, BuchstabSmoothCost,
  ResidueBalancedError, and the previously established Boolean coefficient
  merging / order-mixture identities. Merging is already accounted for in
  existing exact criteria. No uniform logarithmic improvement of their
  arithmetic remainder at the critical level was proved. The factor
  3600^depth in the complete smooth bound remains, and constants in the
  above-two growth theorem are not uniform at exponent2.
- No Mathlib Jacobsthal theorem supplies the missing endpoint.

The preceding five-file barrier/comparison batch also has a clean combined
axiom audit in OrdinaryQuantumBarrierAudit.lean, log
/tmp/ordinary_quantum_barrier_audit.log (only propext, Classical.choice,
Quot.sound for all nine printed declarations).

Spec.lean remains unchanged with the exact original conjecture and sole
sorry2177, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No proof or disproof has been submitted. No worker is pending.

## Slow exponential continuous cost kernel (VERIFIED; NOT AN ENDPOINT RESULT)

ContinuousBuchstabSlowKernel.lean compiles; kernel_slow_exp_le and
logCostKernel_slow_exp_le have only propext, Classical.choice, Quot.sound.
The decay rate is 2/3, strictly below log 2. An explicit quartic majorant
P(u)=(u^4-20u^3+149u^2-550u+1296)/2592 satisfies 1/(u+2)<=P(u)
for u>=0 because 2592*((u+2)*P(u)-1)=u*(u-2)^2*(u-7)^2.
Its exponentially weighted integral is (143/288)*exp(-2*a/3).
Together with exp(4/3)<19/5 this proves the 19/20 contraction.
logCostKernel is exactly conjugate to kernel by multiplication by s.

This is an ANALYTIC MODEL estimate only. A sharp weighted prime-sum
transfer, small-prefix treatment, all recursive unit costs, and a stronger
smooth source are still missing. Even a successful transfer would only
preserve one logarithmic error saving uniformly in depth. The fixed-level
main term remains zero at level two. No quadratic endpoint follows.
Spec.lean remains unchanged with its sole sorry; no settlement submitted.

## Exact critical continuous mass (VERIFIED)

ContinuousBuchstabCriticalMass.lean compiles with a clean axiom audit.
For the inverse-log-square positive cost kernel
  T F(s) = integral_{t>max(2,s-1)} (t+1)/t^2 *
              integral_{v>t-1} (v+1)/v^2 * F(v) dv dt,
the weight w(s)=1-1/s^2 on s>1 is EXACTLY invariant:
  integral w(s)*T F(s) ds = integral w(s)*F(s) ds.
The proof is Tonelli, using integral_1^{t+1} w(s) ds=t^2/(t+1)
and then integral_2^{v+1} 1 dt=v-1. The formal operator and mass
are ENNReal-valued, so this includes infinite masses without any hidden
integrability assumption. criticalMass_invariant and
no_finite_mass_critical_contraction use only the permitted axioms.
Thus no measurable profile of positive finite critical mass can satisfy
T F <= q F for any q<1. This is a model obstruction, not a theorem about
arithmetic error lower bounds, and certainly not a disproof of erdos_970.
No finite-prime transfer is asserted. Spec.lean is unchanged.
The same critical-mass file now additionally proves
no_finite_mass_critical_supersolution (no finite-mass F can absorb
S+T F when S has positive mass) and criticalCostIteration_mass_growth
(the max-preserving positive recurrence accumulates at least n source
masses at depth n). Both have clean allowed-axiom audits. All these are
statements of the continuous model only.

Continuation audit: ContinuationCriticalMassAudit.lean checks all four new
critical-mass results and the existing actual near-quadratic upper / eventual
lower results. All six depend only on propext, Classical.choice, Quot.sound.
Log: /tmp/continuation_critical_mass_audit.log.
Spec.lean was rechecked independently; its only proof hole is still the
original erdos_970 sorry at line2177. Its import and statement are unchanged,
SHA256 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed proof or exact-negation theorem has been submitted.
Review of sparse-small-core and reciprocal-budget reductions did not remove
their explicit restrictions. No new endpoint implication was established.

## Arbitrary fixed tilt and unconditional slow source (VERIFIED)

SelbergArbitraryTilt.lean and BuchstabTiltedSource.lean compile. Main
printed axioms are only propext, Classical.choice, Quot.sound.
For A>=0 and primes bounded by Y, the tilted divisor weight has mean
at most exp(2+9*(exp A-1))*R (log Y>=1). The resulting smooth-support
bound is
  smoothTiltConstant(A)*R*exp(-A*log R/(2*log Y)),
where smoothTiltConstant(A)=exp 2+exp(2+9*(exp A-1)).
The square-root split EXPLICITLY assumes A<=log Y.
The canonical coefficient norm inherits the bound divided by its exact
normalizer. No main term or source definition is changed.

scaled_sharp_cost_le_arbitrary_tilt transfers this to the actual sharp
source, with rate A/4 when A<=log(p_k). Tilt4 gives rate1 on large
prefixes. The small prefixes are handled by the verified 4^k source bound:
log(p_k)<4 implies k<=81. The physical slow shape
  slowLevelShape(k,D)=D*exp(-(2/3)*log D/log p_k)/log p_k
is >=1 for ALL p_k<=D, using 2/3<log2. Consequently
scaled_sharp_cost_le_slow_profile proves, without a remaining cutoff:
  source(k,D) <= (64*smoothTiltConstant(4)^2+4^81)*slowLevelShape(k,D).
This is an actual source estimate, not merely a continuous model theorem.
It is NOT yet a depth-uniform error bound, and it does NOT imply the
quadratic endpoint. Sharp finite-prime transfer of the two-step operator
is still missing. Spec.lean remains unchanged with the original sorry.
Logs: /tmp/arbitrary_tilt.log, /tmp/tilted_source.log.

## Coefficient-one arithmetic profile transfer (VERIFIED)

New compiled files:
  PrimeSmoothProfileTransfer.lean
  PrimeDecayingExponentialTransfer.lean
  PrimeExpCubeTransfer.lean
  PrimeDoubleOuterProfile.lean
Together with the two arbitrary-tilt/source files, the batch's ten main
results are audited in TiltedTransferAudit.lean with only the allowed axioms.

1. cumulative_differentiable_profile_error packages finite Stieltjes
   summation with endpoint atoms. prime_smooth_profile_error applies it
   on [1/2,log R] with E=smoothProfileError=sharpMomentError+1. Its error is
   E*(abs f(log R)+integral abs f'). The leading integral has coefficient1.
   prime_monotone_profile_upper reduces this to 2E*f(log R) for nonnegative
   increasing profiles.
2. For U=log R, R>=2, a>=4U/3, prime_reciprocalExpSquare_sum_upper gives
     sum_{p<=R} exp(-a/log p)/(p log p)
       <= exp(-a/U)*(1/a+8E/U^2).
   The variation estimate uses an explicit positive derivative majorant,
   not a conjectured prime distribution or a numerical integral.
3. For a>=2U, prime_reciprocalExpCube_sum_upper gives
     sum_{p<=R} exp(-a/log p)/(p log(p)^2)
       <= exp(-a/U)*((a/U+1)/a^2+10E/U^3).
4. doubleOuterProfile(L,u)=exp(-(2/3)*(L-u)/u)/((2/3)*u*(L-u))
   is increasing for 0<u<=L/3. prime_doubleOuterProfile_upper preserves
   its integral and charges 2E times its endpoint value.
   integral_doubleOuterProfile_le_tail proves the exact substitution
   bound by 3/(2L)*integral_{L/U-1}^infty exp(-2t/3)/t.
   integral_doubleOuterProfile_upper then bounds this by
     3/(4L)*exp(-(2/3)*(L/U-1)).
5. BuchstabTiltedSource now additionally proves
   complete_sharp_error_le_four_pow: ALL refinement depths are <=4^k
   at each fixed prefix, retaining every unit and outer maximum. This is
   the finite-prefix estimate, not a uniform logarithmic saving.

NEXT UNFINISHED STEP (on-paper plan, NOT a verified theorem):
Let c=2/3, L=log D, U=log R, 3U<=L. The normalized double descendant
sum, before multiplying by D, should be bounded by
 exp(2c-cL/U) *
  [3/(4L) + 2E/(c*U*(L-U))
            +8E*((cL/U+1)/(cL)^2+10E/U^3)].
This follows by applying the square-profile estimate to the inner prime
sum, then the outer-main and cube-profile estimates to the two terms.
The exact finite-sum bridges to Fin-indexed descendants, all cutoff
inequalities, and this combined bound have NOT yet been formalized.
For V=log p_k, choose R=min(p_k,floor(exp(L/3))). At large V, one can
show V/4<=U<=V and 3U<=L. The continuous main contributes <=19/20 of
slowLevelShape; the other terms should give O(E/V+E^2/V^2) uniformly
for L>=V. Root and child units need a separate small relative bound.
The new 4^k theorem handles the finitely many small prefixes.

Even successful completion would only give a depth-uniform ONE-logarithm
error saving. It would NOT settle the quadratic endpoint: the main-term
barrier at level two remains. No target implication is being asserted.
Spec.lean remains unchanged, sole sorry2177. No proof/disproof submitted.

## Complete arithmetic slow-error contraction (VERIFIED; NOT A SETTLEMENT)

New compiled files:
  BuchstabDoublePrimeCost.lean
  BuchstabDoubleCostContraction.lean
  BuchstabSlowCutoff.lean
  BuchstabSlowDescendants.lean
  BuchstabUniformSlowError.lean
  BuchstabUniformSlowLower.lean
The prior two errors in DoubleCostContraction have been fixed. The combined
UniformSlowErrorAudit.lean checks eight main results; each uses only propext,
Classical.choice, Quot.sound. Log: /tmp/uniform_slow_error_audit.log.

The finite double-prime sum is
  primeDoubleSlowSum R L = exp(2/3)*sum_{p<=R} (1/p)*
    sum_{q<=p} exp(-(2/3)*(L-log p)/log q)/(q log q).
For R>=2, U=log R, 3U<=L it is bounded by
  exp(4/3-(2/3)*L/U) *
    [3/(4L)+8E/U^2+80E^2/U^3],
where E=smoothProfileError. If also 0<V<=L, V/4<=U<=V and
V>=100000E, it is at most (24/25)*exp(-(2/3)*L/V)/V.
The main term uses the continuous 19/20 comparison; all arithmetic errors
fit in the remaining 1/100. No arithmetic remainder is omitted.

slowOuterCutoff k D := min(p_k,floor(exp(log D/3))). For D>=p_k and
V=log p_k>=12, its logarithm is between V/4 and V, and at most log D/3.
Every retained child satisfies p_i<=slowOuterCutoff. At V>=100 the root
plus all retained-child units are at most (1/50)*slowLevelShape(k,D).
This uses only integer-floor bounds and elementary exponential estimates.

slow_double_step_le proves the EXACT bridge for any F bounded by B times
the slow profile on admissible levels:
  1+sum_{i<k} lowerErrorStep(F,i,D/p_i)
    <= 1+R+B*D*primeDoubleSlowSum(R,log D).
It includes failed guards and every incurred unit. Retained grandchildren
are admissible; strict-index rows embed into q<=p, and retained outer
indices inject into primes<=R. No prime distribution assumption is hidden.

Let T=max(100,100000E), K=ceil(exp T),
B=max(slowSourceConstant,4^K). Then
  complete_sharp_error_le_uniform_slow
proves for EVERY n,k,D with p_k<=D:
  upperError primeMarginal (primeKeep nthPrime)
    (scaledSharpSelbergCost nthPrime) n k D
      <= B*D*exp(-(2/3)*log D/log p_k)/log p_k.
For V<T the existing complete 4^k bound applies. For V>=T the 24/25
contraction and 1/50 unit budget close induction on n; the outer maximum
is retained. B is independent of depth, prefix, and level.

The one-prime bridge additionally proves, at a kept lower node,
  sum_{i<k} slowLevelShape(i,D/p_i)
    <= (3/2+24E)*slowLevelShape(k,D).
It uses the square-profile prime estimate with a=(2/3)log D, and includes
the boundary-prime summand as an upper bound. Consequently
  complete_sharp_lower_error_le_uniform_slow
bounds the complete lower error at every depth by
  (3+24E)*B*slowLevelShape(k,D).

SCOPE: These are actual arithmetic uniform-in-depth error estimates, not
just continuous-model results. They preserve ONE logarithmic saving.
At fixed level the earlier fixed-depth smooth bound retains TWO logarithms
but has a depth-dependent constant; the new bound does not improve that
fixed-depth estimate. It supplies no positive main term at level two.
The existing near-quadratic result remains O_epsilon(k^(2+epsilon)), and
none of the survivor reductions turns the new bounds into O(k^2).
Review of the two-survivor and subexponential square-cubic reductions did
not prove their missing global / nonlinear premises. No valid tensor
amplification or new lower-tail correlation bound was established.

Spec.lean was recompiled separately. It is unchanged: sole sorry at2177,
original conjecture at2175, sole original import. SHA256:
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No proof or exact-negation disproof of erdos_970 has been produced or
submitted. No worker is pending.

## Endpoint review after the uniform slow-error bound (NO SETTLEMENT)

Re-examined the nonlinear void-doubling / square-cubic reductions, conditional
one-hit core correlation, Bennett bounds, exact greedy-order encoding, and
shared-core two-cover packing. No missing premise was discharged.

- The permitted one-hit negative-dependence result requires each remaining
  prime to be at least the diameter of the UNION of the populations. Medium
  primes at quadratic interval scales do not meet this hypothesis.
- Conditional Bennett still retains the actual old survivor population,
  its row caps, and its variances. Replacing these by expectations inside a
  nonlinear core average is not justified. The pair-kernel variance theorem
  alone gives no nonlinear void association.
- A gcd-of-shift correction does not rescue unrestricted dyadic association:
  the previously verified 231 / 26 Laplace obstruction has a coprime shift,
  and its large-prime padding is also coprime to that shift. This observation
  does NOT refute the cardinality-restricted long-dyadic premise.
- Greedy-order encoding is exact, but no adjacent-prime swap monotonicity,
  stopping-position bound, or quadratic-scale encoding multiplicity estimate
  was proved. The unique-encoding examples are subquadratic and are not
  counterexamples to a quadratic-scale assertion.
- Geometric and bilinear candidate-set interpretations did not yield a
  usable uniform arithmetic estimate. No prime replacement, tensor
  amplification, or independence claim was assumed.
- Removing the square guard from a finite exact recurrence can recover the
  full inclusion-exclusion main term at large depth; it also incurs costs
  not controlled by the verified guarded slow-profile theorem. It cannot
  be used to remove the endpoint main-term barrier for free.

No new Lean theorem or numerical scan was produced in this review. The
uniform slow upper/lower error results remain audited and available, but
there is still no proof or disproof of erdos_970. Spec.lean is unchanged
with its sole original sorry. No worker is pending.

## Cardinality-scale tail and critical initial-core reduction (VERIFIED)

New compiled files:
  BudgetScalePrimeTail.lean
  BudgetScaleFilteredRows.lean
  BudgetScaleCoreDeficit.lean
  InitialCoreDensityReduction.lean
All nine main results are audited in BudgetScaleCoreAudit.lean; permitted
axioms only. Log: /tmp/budget_scale_core_audit.log. The last file's endpoint
conclusion is CONDITIONAL on an explicitly defined, unproved count premise.

1. budgetScaleTail(x)=(log(log x)+2*(boundConstant+1)+1)/log x.
   prime_set_tail_at_budget proves, for |P|<=k, k>=2, log k>=1,
     sum_{p in P,p>k} 1/p <= budgetScaleTail(k).
   This specializes the coefficient-one Mertens estimate at upper cutoff
   k log k. The cardinality contribution beyond it is <=1/log k.
   budgetScaleTail_tendsto_zero is proved.

2. filteredDeletionBudget_le_constant_rows sums the existing sharp Selberg
   row theorem without losing any rounding or source cost. With core Q
   containing every prime through R, it gives exactly
     budget <= (m/log(R+1))*sum_{p in P\Q}1/p
          + |P\Q|*[1/log(R+1)+(exp(2)*R/log(R+1))^2].
   filteredDeletionBudget_le_budget_scale substitutes budgetScaleTail(k)
   if |P\Q|<=k and every tail prime exceeds k. There is NO upper-size
   restriction on individual tail primes.

3. Set k=t^4, R=t, m>=t^8 and t>=3. Define
     fourthScaleDeletionRatio(t) = budgetScaleTail(t^4)
                                  +1/t^4+exp(2)^2/t^2.
   filteredDeletionBudget_le_fourth_scale bounds the entire actual budget
   by fourthScaleDeletionRatio(t)*m/log t. This ratio tends to zero.
   eventually_filteredDeletionBudget_small makes the quantifiers uniform
   in all finite sets, phases, and every m>=t^8. The source sum t^6 and
   the rounded-unit sum t^4 are both retained and absorbed, not omitted.

4. initialCoreCount(z,m,r) is the number in [0,m) avoiding the selected
   residues for ALL primes <=z, cast to real. Given any cover using at
   most t^4 primes, add the complete core Q=(t^4+1).primesBelow for this
   NECESSARY CONDITION only. The remaining tail still has <=t^4 primes.
   core_count_le_fourth_deletion_ratio and
   eventually_cover_forces_initial_core_deficit prove:
     for every epsilon>0, eventually in t, EVERY such cover of m>=t^8
     forces initialCoreCount(t^4,m,r) <= epsilon*m/log t.
   The added core is not falsely counted as part of the original budget;
   the proof separately charges only the complementary original tail.

5. CriticalInitialCoreDensity(A,c) is the UNPROVED premise
     eventually t, forall r,
       c*(A*t^8)/log t <= initialCoreCount(t^4,A*t^8,r).
   For A a positive integer and c>0,
   eventually_fourth_bound_of_core_density proves h(t^4)<=A*t^8, and
   quadratic_of_critical_initial_core_density proves the exact quadratic
   existential conclusion. The latter uses a proved fourth-power envelope
   and finite-prefix absorption; it does not assume first-prime extremality.

SCOPE AND REMAINING GAP: The arithmetic tail bounds and deep-deficit
necessity are unconditional. CriticalInitialCoreDensity is NOT proved.
It requires critical-scale information for the complete initial prime core,
not fixed-level lower-sieve positivity above level two. The existing
continuous lower main vanishes at level two, and no limiting argument
provides this premise. No covariance-only concentration, nonlinear
conditional averaging, or cancellation beyond proved row estimates was
used. This batch does NOT settle erdos_970.

Spec.lean recompiled independently with its original sole sorry2177.
Import and conjecture statement unchanged; SHA256:
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No completed target proof/disproof submitted. No worker is pending.

## Review of the critical initial-core premise (NO SETTLEMENT)

Re-read BuchstabContinuousMain, BuchstabContinuousLowerTransfer,
ContinuousBuchstabIteration, ContinuousBuchstabPositivity, and the new
InitialCoreDensityReduction. No proof of CriticalInitialCoreDensity was
obtained. The available actual-prime main transfer fixes the level s and
slack before choosing its threshold. Its depth and threshold may depend
on s; using s=2+log(A)/log(z) for fixed A is not justified by that theorem.
The continuous clipped lower model remains zero at the endpoint.

A positive count or a gap bound for a smaller budget alone does not imply
the positive normalized core-density premise. Adjoining one fresh prime
per survivor only yields the corresponding finite count/padding consequence,
not a count proportional to m/log(z). The vanishing tail theorem cannot
supply that missing lower bound. No arithmetic cancellation, high-moment
lower-tail estimate, or character-theoretic claim was proved or assumed.

The critical initial-core reduction remains explicitly conditional. No
new mathematical Lean theorem or numerical scan was produced in this review.
Spec.lean is unchanged with its original sole sorry, and no completed proof
or disproof has been submitted. No worker is pending.

## Population-sensitive variance and nonlinear insertion (VERIFIED, NO SETTLEMENT)

New compiled files:
  PopulationSensitiveRowVariance.lean
  PopulationLaplaceInsertion.lean
All nine printed main results have permitted-axiom audits; no sorryAx.
Logs:
  /tmp/population_sensitive_row_variance.log
  /tmp/population_laplace_insertion.log

The pointwise inequality, for N=intervalCount(P,m,r) and any uniform row cap B,
  rowConditionalVariance(P,m,p,r) <= B*N/p - (N/p)^2,
is now proved. It follows from H_a^2 <= B*H_a and the exact row mean N/p.
The bound is pointwise in the old core phase, not merely averaged. It therefore
gives, for EVERY nonnegative weight w on old phases,
  E[w*V] <= (B/p)*E[w*N] - E[w*N^2]/p^2.
In particular w=exp(-t*N) is allowed. This supplies a genuine Gibbs-weighted
inequality, but with a cap-dependent coefficient; it is NOT the previously
unproved small-variance bound at critical scale. The existing sharp Selberg
row theorem supplies B=((m/p+1)/log(R+1))+(exp(2)*R/log(R+1))^2, with all
rounding and square-source costs retained.

The following actual insertion identities/bounds are also proved:
* phaseSurvivors_extend_eq_avoidClass and intervalCount_extend_eq_sub_row
  identify insertion exactly with deleting one old residue row.
* countLaplace_insert_exact gives
    L_{P+p}(t)=E_r E_a exp(-t*(N(r)-H_a(r))).
* countLaplace_insert_le_transport gives, if B>0 caps every row,
    L_{P+p}(t) <= L_P(t-(exp(t*B)-1)/(B*p)).
  Positivity of the transported parameter is NOT automatic.
* row_deletion_laplace_le_population_quadratic and
  countLaplace_insert_le_population_quadratic preserve the centered Bennett
  expression
    E_r exp(-t*(1-1/p)*N + bennettFactor(t,B)*(B*N/p-N^2/p^2)),
  for t>=0. The nonlinear phase expectation stays outside the exponential;
  no mean-variance substitution or row independence is asserted.

SCOPE: These results are unconditional bounds with explicit caps, not a
closed critical lower-tail estimate. The cap inequality is compatible with
populations concentrated in one residue (where the appropriate abstract
variance bound is sharp). It does not exclude the low-count phases required
by a hypothetical quadratic cover. No iteration proving a positive initial
core count, no endpoint uniform constant, and no target disproof was obtained.

Further mathematical review (not formal results): a positive fixed fraction
in CriticalInitialCoreDensity is stronger than needed. The proved deletion
coefficient requires only a lower count exceeding its explicit
fourthScaleDeletionRatio(t)*m/log(t); asymptotically this is of order
m*log(log(t))/log(t)^2. No such lower bound has been established. Neither
near-quadratic estimates with exponent-dependent constants, nor averaged
conditional variance, justify this missing lower bound. The new weighted
bound removes the invalid averaging step but not the size of the remaining
cap or the nonlinear expectation.

Spec.lean remains unchanged with the original sole sorry. No completed
proof or exact-negation disproof has been submitted. No worker is pending.

## Pointwise critical-cost obstruction without finite-mass assumption (VERIFIED)

New compiled files:
  ContinuousCriticalFirstMoment.lean
  ContinuousCriticalTightness.lean
  ContinuousCriticalPotential.lean
  ContinuousCriticalNoSupersolution.lean
All printed main results have permitted-axiom audits; no sorryAx.
Individual build logs:
  /tmp/critical_first_moment.log
  /tmp/critical_tightness.log
  /tmp/critical_potential.log
  /tmp/critical_no_supersolution.log
Combined audit file: ContinuousCriticalPointwiseAudit.lean.

This closes the INFINITE-MASS POSSIBILITY for the continuous critical
positive-cost supersolution model, but does not settle erdos_970.
Let K=criticalCostKernel, w(s)=1-1/s^2 on s>1, and M(F)=int wF.
The preceding mass theorem gives M(KF)=M(F). Define M1(F)=int s*w(s)*F(s).
The new theorem criticalFirstMass_kernel_le proves, in ENNReal and with no
finiteness assumption,
  M1(KF) <= (1/2)*M1(F)+(5/2)*M(F).
Proof: after two Tonelli swaps, the first inner moment is bounded using
s<=t+1; the remaining integral of t+1 on (2,v+1) is
(v-1)*(v+5)/2. Multiplication by (v+1)/v^2 gives
w(v)*(v+5)/2, proving the drift estimate.

For the cutoff mass M_R(F)=int_{1<s<R} w(s)F(s), the new tightness bounds are
  M(F) <= M_R(F)+M1(F)/R,
  K(F)(2) >= M_R(F)/(R+1),
for the stated positive cutoffs. In particular M(F)=1/2 and M1(F)<=5/2
imply K(F)(2)>=1/44, using R=10.

Take G=1_(1,2) and U_0=0, U_(n+1)=G+K(U_n). The exact source mass is 1/2
and its first moment is <=1. Verified:
  M(U_n)=n/2,
  M1(U_n)<=(5/2)*n,
  U_(n+1)(2)>=n/44.
Thus growth is pointwise at level two, not merely growth of total mass.

The theorem positive_source_supersolution_two_top says: if c is positive
and finite, S(s)>=c on (1,2), and F>=S+KF for every s>1, then F(2)=infinity.
There is NO integrability or finite-total-mass hypothesis on F, and the
finite-scalar kernel homogeneity proof does not even require measurability
of F. In particular no_real_exponential_critical_supersolution excludes
EVERY finite real-valued profile for a source exp(-a*s), a>=0, even if its
critical mass is infinite.

The theorem criticalCostIteration_two_growth retains the OUTER MAXIMUM of
the original positive continuous cost model and proves
  criticalCostIteration S B (n+1) 2 >= c*n/44
under the same compact positive-source condition, for every initial B.

SCOPE: This strengthens the older finite-mass obstruction. It does NOT
transfer a lower bound to the actual arithmetic sieve remainder, does NOT
show that alternative signed or phase-sensitive estimates are impossible,
and is NOT a disproof of the quadratic Jacobsthal conjecture.

Other reviews this turn: Combining the new population-sensitive insertion
bounds with existing low-count estimates still leaves a nonlinear old-phase
expectation. No justified substitution of its unweighted mean was found.
The fixed-depth continuous main transfer is still nonuniform as s tends to
2; the depth-uniform slow error bound does not repair that separate main-term
issue. No polylogarithmic endpoint upper bound or new target lower bound
was established in this turn.

Spec.lean is unchanged with its original sole sorry, import and conjecture
type. No completed target proof/disproof has been submitted; no worker is
pending after the recorded builds finish.

## Return to shared-residue arithmetic (NO NEW SETTLEMENT)

Re-read ResidueBalancedError/AdjacentShift results, FirstHitBooleanCost,
FirstHitSigned, RoundedCertificateObstruction, and the earlier joint-pattern
LP record. No new arithmetic cancellation estimate was established.
The existing same-modulus comparison (two counts differ by at most one)
continues to justify the finite adjacent-shift certificate; it does not
supply a uniform logarithmic saving for growing prime budgets. Maximal-gap
endpoint survival does not justify setting mixed-offset CRT boundary terms
to zero, since those terms use different residue assignments. No such step
was used or assumed.

No new LP scan or mathematical Lean theorem was produced in this review.
The exact conjecture remains unsolved; Spec.lean retains its sole original
sorry at2177 and its unchanged sole import and target type. No completed
proof or disproof has been submitted. No worker is pending.

## Joint-fluctuation and endpoint review (NO NEW SETTLEMENT)

Re-read PopulationSensitiveRowVariance, SubexponentialSquareCubicReduction,
CardinalityBootstrap, GapTailCriterion, ArbitrarySubcriticalExposure,
CompetingCoverVariance and ResidueFourierVariance, together with the recorded
aggregate first-hit and Fourier-normalization investigations.

No missing unconditional quadratic conclusion was found. The available
joint Fourier identity has the p^2 variance normalization; the classical
large-sieve bound discussed in the log is not a new Lean theorem and is too
large for the proposed critical-scale exclusion. Pointwise cap-dependent
Gibbs estimates do not supply the missing small conditional fluctuations.
The explicit square-cubic correlation premise remains unproved. The
subcritical exposure exponents remain below the actual phase entropy.

No new mathematical theorem, numerical search, target proof or disproof was
produced in this review. Spec.lean was not edited and retains its original
sole sorry and unchanged import and target statement. No incomplete proof
was submitted. No worker is pending after the final file check.

## Exceptional partial-floor exposure (VERIFIED, NO SETTLEMENT)

New file: ExceptionalPartialExposure.lean, compiled with a built olean.
Log: /tmp/exceptional_partial_exposure.log.
Namespace Erdos970.SoftExposure. All six printed main results use only
propext, Classical.choice and Quot.sound.

The old soft exposure bound required PartialLower(j,...,A) for EVERY phase.
The new exceptionalPartialFraction is the phase probability that this
partial-floor condition fails. For A>0 and 0<=b<A, verified:

  lowCountFraction(P,m,b)
    <= budget(j,P)/(1-b/A)^j + exceptionalPartialFraction(P,m,j,A).

The stronger undivided inequality charges (1-b/A)^j times the exceptional
probability. The proof splits into good and bad partial-floor phases, uses
the existing tree lower bound only on good phases, and averages the actual
nonnegative tree. No independence of exceptional events is used.

phaseMean_corePhase proves the exact uniform marginal identity for arbitrary
real-valued statistics on a retained prime subset. Using this identity and
an ordinary finite union bound, verified:

  exceptionalPartialFraction(P,m,j,A)
    <= sum_{Q subset P, |Q|<j} strictLowCountFraction(Q,m,A).

Here strictLowCountFraction uses count<A, not count<=A. The combined theorem
lowCountFraction_le_budget_div_add_subcore_sum retains the entire subcore
sum. When j<=|P| its terms are all smaller cardinalities.

SCOPE: This is an unconditional reduction with an explicit exceptional
probability, NOT a new sufficiently small critical-scale lower tail.
The subcore union cost has not been removed or bounded by a mean/independence
shortcut. Available subcritical estimates do not yield a closing recursive
quadratic bound after this cost. No target proof or exact-negation disproof
has been obtained. Spec.lean was not edited and retains its sole original
sorry and exact conjecture/import. No incomplete proof was submitted.

## One-sided resampling continuation (NO NEW SETTLEMENT)

Reviewed SurvivorResampling, PrimeCoverResampling, RowConditionalVariance,
ResampledLowCountCylinder, ResampledAveragedFloors, and the recorded Gibbs
review. The exact upward resampling increment still includes private
positions, and at a zero-count phase their contribution need not vanish.
No pointwise self-bounding or sufficiently small Gibbs variance inequality
was proved. Disjointness of private-position sets alone did not supply the
needed critical-scale bound. Speculative weighted almost-prime/private-count
and multi-shift arguments were not formalized or used as established facts.

No new mathematical Lean theorem or numerical search was produced in this
continuation. ExceptionalPartialExposure.lean remains the latest verified
auxiliary development, with its full exceptional-subcore term retained.
The original erdos_970 remains unsolved. Spec.lean was not edited; its exact
import and conjecture remain, with the original sole sorry at2177. No
incomplete proof was submitted and no worker is pending.

## Linear upper growth for the critical continuous cost model (VERIFIED)

New compiled files with built oleans:
  ContinuousCriticalKernelUpper.lean
  ContinuousCriticalLinearUpper.lean
  ContinuousCriticalDecayUpper.lean
  ContinuousCriticalUpperAudit.lean
Logs: /tmp/critical_kernel_upper.log, /tmp/critical_linear_upper.log,
/tmp/critical_decay_upper.log, /tmp/critical_upper_audit.log.
All seven combined-audit results use only permitted axioms.
Namespace Erdos970.ContinuousBuchstab.

Let K=criticalCostKernel, M=criticalMass, J=criticalFirstMass,
and a=max(2,s-1). Tonelli and monotonicity of (t+1)/t^2 give:
  K(F)(s) <= ofReal(criticalCoefficient(a))*M(F) <= (3/4)*M(F),
  K(F)(s) <= ofReal(criticalCoefficient(a)/(a-1))*J(F),
  K(F)(s) <= ofReal(16/s^2)*J(F), s>1.
These are ENNReal inequalities for measurable inputs and require no mass
finiteness assumption. The inverse-square bound uses the support restriction
v>a-1 as well as the coefficient bound.

IMPORTANT exact maximum identity: for U=criticalCostIteration(S,B), originally
  U_0=B, U_(n+1)=max(U_n,S+K U_n),
positivity and monotonicity prove
  U_(n+1)=max(B,S+K U_n).
Thus the PREVIOUS ITERATE is not added again as a fresh source. Using this
identity with the invariant mass and the verified first-moment drift gives:
  M(U_n) <= (n+1)*M(B)+n*M(S),
  J(U_n) <= (n+1)*(2*(J(B)+J(S))+5*(M(B)+M(S))).
Consequently:
  U_(n+1)(s) <= max(B(s), S(s)+(16/s^2)*(n+1)*
    (2*(J(B)+J(S))+5*(M(B)+M(S)))), s>1,
with ofReal on the real scalar as in the Lean theorem. The uniform 3/4 mass
bound also yields finite values at every finite depth for finite-mass,
finite-valued initial data and source.

For the compact-source potential, the earlier lower bound now has a matching
linear upper bound:
  n/44 <= criticalCompactPotential(n+1)(2) <= 3*n/8.
This is an order-of-growth statement for the continuous positive model only.

SCOPE: These results DO NOT bound the actual finite-prime error by O(n), do
not provide a quantitative finite-prime main transfer near level two, and do
not prove or refute erdos_970. The unrestricted Jacobsthal upper bounds remain
those in BuchstabArbitraryGrowth.lean. No polylogarithmic endpoint upper bound
has been established here. Spec.lean was not edited, and retains the original
sole sorry, import, and conjecture statement. No incomplete proof was submitted.

## Depth-uniform finite-prime main transfer (VERIFIED)

New compiled file: BuchstabDepthUniformMain.lean.
Log: /tmp/buchstab_depth_uniform_main.log. All five printed main results
use only permitted axioms.

Continuous upper-envelope differences obey
  |u_N(s)-u_n(s)| <= 40000*(19/20)^N*exp(-s), N<=n, s>=1,
and lower-profile differences are <=40000*(19/20)^N for s>=2.
Monotonicity in depth then upgrades the fixed-depth prime transfer: for
fixed s>=2 and fixed epsilon>0, one prime threshold works for ALL depths.
Upper-only transfer needs s>=1. These are actual referenceUpper and
referenceLower comparisons with prefix density and the continuous model.
There is NO bound on the threshold as s tends to 2 or epsilon tends to 0.
This does not justify a k-dependent endpoint passage or settle erdos_970.

## Exact finite error kernel and finite potential (VERIFIED)

New compiled file: BuchstabErrorPotential.lean.
Log: /tmp/buchstab_error_potential.log. All six printed main results use
only permitted axioms.

The exact two-step upper-error recurrence is written as
  U_(n+1)=max(base,source+L U_n),
where source includes the unit and every retained outer guard, and L is
the guarded nested finite-prime sum. No units or guards are dropped.
The r-th kernel power at index k vanishes whenever k<2*r. Consequently,
for nonnegative base the actual error is bounded by the finite potential
sum_{r=0}^{floor(k/2)} L^r(base+source), uniformly in depth, and the
actual upper-error recurrence stabilizes after depth floor(k/2)+1.
No quantitative analytic bound for this finite potential, and no bridge
to the continuous linear-cost upper bound, has been established.
Spec.lean remains unchanged with the original conjecture and sole sorry.

## Additive Euler-mass remainder and uniform sectors (VERIFIED)

New compiled files:
  EulerMassRemainder.lean
  EulerMassQuantitativeSectors.lean
Logs: /tmp/euler_mass_remainder.log and
/tmp/euler_mass_quantitative_sectors.log. The six printed main results
use only propext, Classical.choice, and Quot.sound.

The logarithmic Cauchy modulus in EulerMassAsymptotic is quantitative.
Passing it to its limit gives some c with
  |eulerLogPhase(n)-c| <= (2*(WeightedMertens.boundConstant+1)+1)/log n,
for every n>=2. An elementary global exponential difference inequality
then gives positive C,A with
  |initialEulerMass(n)-C*log n| <= A,
for EVERY n>=2. There is no prime number theorem or identification of C.

Quantitative ratios retain both numerator and denominator errors. The
exponential floor has logarithmic error <=1 when t*L>=2, so
  |initialEulerMass(expFloor(t,L))-C*t*L| <= A+C.
Consequently the exact first-hit sector mass, normalized at v, obeys
  |mass(v,t,u,L)-(v/t-v/u)|
    <= 4*(A+C)/(C*a*L)*(1+v/a),
under 0<a<=t<=u, v>=0, L>0, v*L>=2, a*L>=2, and
2*(A+C)<=C*a*L. Crucially, t and u may vary with L: this is a genuinely
uniform sector estimate, not an unjustified substitution into a fixed-limit
theorem. The exact telescope includes the strict prefix in every weight.

SCOPE: This does not yet give a quantitative recursive main-term comparison,
and does not bound the finite-prime error potential by the continuous one.
Even either of those bridges would not automatically overcome the level-two
positivity barrier. No claim of O(k^2) or of a counterexample has been proved.
The best unrestricted upper bound remains the result in
BuchstabArbitraryGrowth.lean. Spec.lean was not edited, and the original
conjecture retains its sole sorry. No incomplete proof has been submitted.

## Endpoint correlation and truncated-moment review (NO NEW SETTLEMENT)

Revisited SubexponentialSquareCubicReduction, InitialCoreDensityReduction,
QuadraticCountMomentObstruction, ExceptionalPartialExposure,
EssentialCoverProbability, PrimeCoverResampling, OneHitCollisionRemainder,
OneHitCoreDyadic, and the recorded fractional two-block diagnostics.

The full-centred moment obstruction does not refute a small-fraction
truncated lower-tail estimate, but no such sufficiently strong estimate
was proved. Pointwise cap-based variance still costs the initial cutoff
scale; choosing the cutoff near the cardinality budget would require the
missing critical initial-core lower count. No averaged variance was moved
inside a nonlinear exponential or completion probability.

The exact one-hit conditional negative dependence still retains the core
completion-weight second moment. For medium primes the residue-collision
term cannot be omitted. Parity's already-verified cutoff improvement does
not eliminate either the core fluctuation cost or general medium-prime
collisions. Neither a polynomial-loss nor a sublinear-power-exponential-loss
unrestricted doubling inequality was established.

No new theorem, numerical search, counterexample, or target modification
resulted from this continuation. The additive Euler remainder and uniform
sector estimates remain the newest verified auxiliaries. The original
quadratic conjecture is unsolved, with Spec.lean unchanged and its sole
sorry at line2177. No incomplete proof has been submitted; no worker pending.

## Global monotone profile quadrature (VERIFIED; continuation record)

New compiled files, all audited using only permitted axioms:
  EulerMassMonotoneQuadrature.lean
  BuchstabQuantitativeProfile.lean
  BuchstabUniformVariableTail.lean
  BuchstabQuantitativeStep.lean
  EulerMassUnrestrictedRatio.lean
  EulerMassUnrestrictedQuadrature.lean
  BuchstabProfileInterval.lean
  BuchstabGlobalProfile.lean
Corresponding /tmp logs use the snake_case filenames.

Abel summation bounds monotone weighted cumulative errors by 2*b(0)*E,
independently of mesh size. The elementary harmonic lower bound gives
  initialEulerMass(floor(exp(t*L))) >= t*L
without any cutoff condition. Thus a global additive remainder
  |M(n)-C*log(n)| <= A (n>=2)
implies unrestricted Euler ratio errors
  |M(floor(exp(vL)))/M(floor(exp(tL)))-v/t|
    <= (A+C+1)/(tL)*(1+v/t)
for v>=0,t>0,L>0. The extra 1 handles floor equal to one.

The strongest new result, prime_profile_global_upper, proves that for
s>=1,L>0 and nonnegative antitone tail-integrable f with f(x)<=H*exp(-x),
  M(floor(exp(L))) * sum_{p<=floor(exp(L))}
    f(s*L/log(p)-1)/(p*M(p^-))
  <= tailIntegral(f,s-1)/s + 88*(A+C+1)*H*exp(1-s)/L.
All primes are included. The integral coefficient is exactly one.
The proof partitions child levels into unit intervals, retains their
finite interval integrals, and sums errors using
  sum_{j<N} (j+2)^2*exp(-j) <= 22.
There is no hidden terminal-tail or sector-count loss.

BuchstabUniformVariableTail exposes that actual tail thresholds can be
chosen independently of M>=13. BuchstabQuantitativeStep retains explicit
actual child-profile domination hypotheses and both quadrature and tail
losses; it is not a recursive domination theorem.

SCOPE: No all-depth quantitative comparison or arithmetic error-potential
bound was inferred. The global quadrature estimate alone does not settle
the level-two endpoint, and in particular does not imply O(k^2).
Spec.lean remains unchanged with its original sole sorry and import.

An unformalized direction is exact Euler coordinates T_i=1/(C*delta_i).
First-hit weights become exact inverse-square interval integrals, and
|T_i-log(p_i)|<=B should turn discretization errors into an O(depth)
shift in log(D). Even this would not by itself remove the endpoint barrier.

## Inverse-log main-error conjugacy (VERIFIED; NO TARGET SETTLEMENT)

New compiled file: ContinuousMainLogError.lean.
Log: /tmp/continuous_main_log_error.log. All three printed results use
only propext, Classical.choice, and Quot.sound.

Defined the continuous positive propagation operator
  K_log(H)(s) = 1/s^2 * integral_{t>max(2,s-1)} (t+1)/t^2 *
                 integral_{v>t-1} (v+1)*H(v) dv dt.
A child inverse logarithm contributes (t+1)/s in addition to the
normalized main-term measure dt/s. The exact conjugacy is
  s^2*K_log(H)(s) = criticalCostKernel(v -> v^2*H(v))(s), s != 0.
This is a continuous-model identity, NOT an arithmetic transfer theorem.

Consequently, if S is bounded below by a positive constant on (1,2),
any extended-valued supersolution S+K_log(H)<=H on s>1 has H(2)=top.
No finite-mass or measurability premise on H is needed. In particular,
there is no real-valued, depth-independent supersolution with the
positive exponential source exp(-a*s), a>=0. Thus contraction of the
unweighted main operator does not justify uniformly propagating an
O(1/log z) positive quadrature allowance. Signed arithmetic cancellation
or controlled finite-depth accumulation would require separate proofs.

Also reviewed the critical initial-core reduction and the square-cubic
void route. Neither missing endpoint premise was proved. No actual
quadratic-scale survivor result or counterexample was obtained. The
best unrestricted Jacobsthal upper bound in this development remains
BuchstabArbitraryGrowth.lean. Spec.lean is unchanged, including its
original sole sorry; no incomplete proof has been submitted.

## Exact Euler-coordinate transfer and actual polylogarithmic growth (VERIFIED)

Nine new compiled files, with permitted-axiom audits:
  BuchstabEulerCoordinates.lean
  BuchstabEulerQuadrature.lean
  BuchstabEulerStep.lean
  BuchstabEulerBase.lean
  ContinuousBuchstabSlowOperator.lean
  ContinuousBuchstabSlowDeficit.lean
  BuchstabEulerUniformMain.lean
  BuchstabEulerSurvivor.lean
  BuchstabPolylogarithmicGrowth.lean
Logs in /tmp use the corresponding snake_case filenames. No worker pending.

1. Euler coordinates T_i=1/(C*delta_i) are positive and increasing. The
inclusive additive Euler remainder implies, for every prime, the strict
remainder |M(p^-)-C*log p| <= 2*A+C. Thus some fixed positive C,B give
  |T_i-log(p_i)| <= B
at EVERY index. The exact identity is
  q_i*delta_i/delta_k = T_k*(1/T_i-1/T_(i+1)).

2. Right-endpoint rectangle sums in reciprocal coordinates yield, for any
nonnegative antitone integrable profile f on [s-1,infinity), s>0,
  sum_{i<k} q_i*delta_i * f((s*T_k+B-log p_i)/T_i)
    <= delta_k * tailIntegral(f,s-1)/s.
All primes are included, and there is NO quadrature or terminal-tail loss.
The child level is exactly that of exp(s*T_k+b+B)/p_i when the child shift
is b. A lower-root shift >=2*B retains the actual square guard.

3. The base profile is globally bounded by H*exp(-2*s/3) in Euler
coordinates with shift B. At large primes this uses the existing physical
exponential source and T_i >= (2/3)*log p_i. At the finitely many small
prefixes, the upper source is EXACTLY density once its divisor cutoff
contains the fixed wheel; otherwise the source <=1 is absorbed into H.
No small-prime exception remains.

4. The continuous augmented envelope
  u_n(s)+H*(19/20)^n*exp(-2*s/3)
is a two-step supersolution. The general clipped deficit is antitone,
nonnegative and integrable, and includes the whole region below level two.
Its tail is bounded by the forcing plus the full continuous kernel.

5. Actual finite-prime induction now gives, with q=19/20,
  referenceUpper(n,k,exp(s*T_k+(2*n+1)*B))
    <= delta_k*(1+u_n(s)+H*q^n*exp(-2*s/3)),  s>=1,
and the quantitative lower bound
  delta_k*(s-2-(24000+2*H)*q^n)/s
    <= referenceLower(n,k,exp(s*T_k+(2*n+2)*B)), s>=2.
All constants are fixed; all depths, prime prefixes, and real levels in
these ranges are allowed. No threshold depends on n, s, or a slack.
This is a comparison of ACTUAL reference main terms, not just the model.

6. The separate actual smooth error is charged using the already verified
60*smoothLeafConstant(1)*3600^n*D*log(p_k)/log(D)^3 bound, uniformly for every
smaller prefix. Choosing s=2+2/T_k and requiring
  (24000+2*H)*q^n <= 1/T_k
gives a genuine survivor/Jacobsthal estimate
  h(k) <= A*(3600*exp(2*B))^n*p_k^2.
Both root and child units and all guards remain in the error budget.

7. A finite geometric-depth lemma uses q^20<=1/2. For fixed K>0,R>=1,
some fixed d and G>0 satisfy: for every T>0, some n has
  K*q^n<=1/T,  R^n<=G*(T+1)^d.
This gives the unconditional prime-indexed theorem
  exists d,A>0, forall k, h(k)<=A*p_k^2*log(p_k)^d,
and the actual budget theorem
  exists d : Nat, exists A>0, forall k>0,
    h(k)<=A*k^2*log(k+2)^d.
The latter is the strongest unrestricted upper result in this development.

SCOPE: The logarithmic exponent is finite but may be very large. It is NOT
zero, and no step makes it zero. The main comparison still requires the
level-two square guard; the original quadratic endpoint remains unsolved.
Spec.lean has not been edited, its import and conjecture are unchanged, and
its original sorry remains. No incomplete proof was submitted.


## Critical-power, logarithmically weakened void estimates (VERIFIED)

Two new compiled files:
  LogCriticalExposureBudget.lean (115 lines)
  LogCriticalVoid.lean (including an explicit entropy-envelope comparison)
Logs:
  /tmp/log_critical_exposure_budget.log
  /tmp/log_critical_void.log
All printed axioms are propext, Classical.choice, Quot.sound only.
No pending worker and no target settlement.

LogCriticalExposureBudget.lean defines
  logExposureSize b t = floor(t^40 / log(t)^b).
It proves elementary floor bounds and that, for ONE FIXED positive natural b,
eventually in t, this size is positive and
  t^80 <= 2^80*k  ==> IsJacobsthalBound (logExposureSize b t - 1) k.
This uses the genuine unrestricted fixed-log-power Jacobsthal bound. If its
exponent is d, take b=d+1. Eventually A*42^d*2^80 <= log t; together with
j <= t^40 and j*log(t)^(d+1) <= t^40 this absorbs the growth constant.
The inequality log(j+2) <= 42*log t and all floor losses are charged.

LogCriticalVoid.lean proves that the exposure overhead of the core
  S = {p in P : p <= D*t^30}
is eventually <= j/400. This follows from
  log(t)^(b+1) <= t^10/(34400*(D+2)).
The reciprocal tail is <=199/200, so the general factorial exposure bound
gives exp(-j/400), hence exp(-t^40/(800*log(t)^b)).
The 80th-power envelope transfers this to the actual budget k:
  exists_log_critical_linear_void:
    exists b>0, eventually k, forall prime P with P.card<=k,
      V_P(k) <= exp(-sqrt(k)/(800*log(k)^b));
  exists_log_critical_quadratic_void:
    exists b>0, eventually k, forall prime P with P.card<=k,
      V_P(k^2) <= exp(-k/(800*2^b*log(k)^b)).
These are unconditional and uniform in the prime set. One fixed b works.

The additional audited theorem
  eventually_log_critical_envelope_above_entropy
proves, for every A>0 and natural b, eventually
  exp(-k*log(k+2)) < exp(-A*k/log(k)^b).
This is a comparison of the bounding envelopes only, NOT a positive lower
bound on the actual void fraction. It records why the new estimates cannot
be used with the existing phase-entropy exclusion to prove the conjecture.

Review of endpoint possibilities did not provide a bound on the explicit
core-weight variance or collision remainders. All existing square-cubic
correlation hypotheses remain unproved. The exact Euler transfer still
has a level-two square guard, and the fixed log exponent is not zero.

Spec.lean remains unchanged (SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9), with its sole
original sorry at line2177. No proof or disproof has been submitted.


## Logarithmic-loss correlation reduction and one-hit barrier (VERIFIED)

Four new compiled files, with permitted-axiom audits:
  LogLossSquareCubicArithmetic.lean (138 lines)
  LogLossSquareCubicSeed.lean (107 lines)
  LogLossSquareCubicReduction.lean (128 lines)
  OneHitCollisionBarrier.lean (148 lines)
Logs:
  /tmp/log_loss_square_cubic_arithmetic.log
  /tmp/log_loss_square_cubic_seed.log
  /tmp/log_loss_square_cubic_reduction.log
  /tmp/one_hit_collision_barrier.log
No sorry, sorryAx, or new axioms in these files. All printed axiom sets are
propext, Classical.choice, Quot.sound. No pending worker.

1. LogLossSquareCubicVoidBound C B is an EXPLICIT UNPROVED hypothesis:
   eventually k, uniformly over prime sets P.card<=k and lengths m>=k,
     V_P(2m)^2 <= exp(C*k/log(k)^B)*V_P(m)^3.
   The budget-uniform eventual quantifiers are part of this definition.

2. exists_log_loss_square_cubic_reduction proves that ONE FIXED positive
   natural B suffices for a conditional quadratic conclusion, for any
   fixed nonnegative C. This relaxes the former exp(C*k^beta), beta<1,
   loss at the level of the sufficient hypothesis. It does NOT prove it.

   Exact iteration construction on k=2^t:
     r=b+2, N=Nat.log 16 (t^r), Q=16^N,
     j=16*N, m=2^(2*t-64*N), B=b+8*r+1=9*b+17.
   Eventually 64*N<=t, hence k<=m and 16^j*m=k^2 exactly.
   Also Q<=t^r<=16*Q, Q^8*sqrt(m)=k, Q^9<=5^j.
   The unconditional seed absorbs the loss exp(C*k/log(k)^B) while
   retaining rate E=k/(1600*2^b*t^b*Q^8).
   The finite square-cubic iteration gives exp(-E*5^j), with
     E*5^j >= k*t^2/(25600*2^b).
   This exceeds the normalized phase entropy, which is <=42*k*t.
   The dyadic conclusion patches to all budgets with a factor four.
   All floors, powers, and interval lengths are exact in Lean.

3. OneHitCollisionBarrier.lean proves the finite inequality
     (1-collision)*(mu-p)^2 <= mu*(1-density(P)),
   where mu=m*density(P), assuming p>0 is in R and p<=mu.
   A good (residue-injective) phase has at most p core survivors; the
   actual phase-count variance bound supplies the inequality.
   Thus when p<=mu/2,
     coreCollisionFraction P R (range m) >= 1-4/mu.

   The uniform asymptotic theorem eventually_collision_near_one says:
   for fixed A>0, d : Nat, epsilon>0, eventually in k, for any prime
   core P.card<=k and any R containing a positive modulus
     p <= A*k*log(k+2)^d,
   every m>=k^2 satisfies collision>=1-epsilon. It uses the verified
   uniform Mertens density lower bound. It needs no disjointness because
   it is a statement about the remainder, not a conditional completion.

SCOPE: This refutes the hope of bounding the currently defined additive
collision remainder by a tiny error in the relevant medium-prime regime.
It does NOT give a lower bound on actual void probability or disprove the
new correlation premise. Repeated-hit correlations require a different
estimate from the one-hit-plus-exceptional-phase decomposition.

The original target remains UNSOLVED. Spec.lean is unchanged, SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9,
with its sole original sorry at line2177. No incomplete proof submitted.


## Weighted repeated-hit covariance and completion fibers (VERIFIED)

Three new compiled files, with permitted-axiom audits:
  WeightedCoverageCollision.lean
  WeightedCoreCollision.lean
  CompletionCollisionFibers.lean
Logs:
  /tmp/weighted_coverage_collision.log
  /tmp/weighted_core_collision.log
  /tmp/completion_collision_fibers.log
No pending worker. All printed axiom sets are only propext,
Classical.choice, Quot.sound. These are auxiliary results, not a settlement.

WeightedCoverageCollision.lean:
  F_R(S) denotes the actual populationCoveredFraction S R.
  completionIncrement R S p a = F_R(S minus class a mod p)-F_R(S) >=0.
  completionCollision R S T p = mean_a(increment_S(a)*increment_T(a)).
  coverageCovariance R S T = F_R(S union T)-F_R(S)*F_R(T).
  For insertion of p not in R, the exact identity is
    Cov_(R+p)(S,T)
      = mean_a Cov_R(S minus a,T minus a)
        + completionCollision R S T p
        - (F_(R+p)(S)-F_R(S))*(F_(R+p)(T)-F_R(T)).
  The negative product is explicitly retained in the identity.

  weightedCollisionCost ps S T is the positive recursive majorant obtained
  by dropping that negative product at each step. It is nonnegative and
  bounds Cov for every duplicate-free list of positive moduli. It does NOT
  require one-hit populations or even prime moduli for this finite result.
  Thus F_R(S union T) <= F_R(S)*F_R(T)+weightedCollisionCost.

  CrossSeparated R S T means no residue modulo a prime in R is shared
  ACROSS S and T. Repetitions within S or within T are permitted. The
  recursive cost vanishes under this condition, proving negative
  dependence in this strictly weaker-than-union-injectivity regime.
  This condition is still not established for the target populations.

WeightedCoreCollision.lean:
  weightedCoreRemainder P R S T averages over the core phase the minimum
  of (i) actual conditional union completion probability and (ii) the new
  recursive cost on the two actual core survivor populations.
  It is nonnegative and gives
    F_(P union R)(S union T)
      <= mean_core(w_S*w_T)+weightedCoreRemainder.
  Its upper bounds include the uncapped recursive mean, the ACTUAL union
  cover probability, and (for disjoint populations) the old all-or-nothing
  coreCollisionFraction. On injective phases the recursive cost is zero.
  Adjacent intervals give the unconditional finite comparison
    V_(P union R)(2m) <= V_(P union R)(m)^2
                         +coreWeightVariance P R m
                         +weightedCoreRemainder for the adjacent blocks.
  The variance and weighted remainder remain explicit; neither is bounded
  at the small relative scale needed by the square-cubic reduction.

CompletionCollisionFibers.lean:
  Each completionIncrement is EXACTLY the old-phase probability that the
  survivor population is nonempty and wholly in the selected new residue.
  populationConcentration R S p is the probability of any such nonempty
  one-residue population. Therefore
    mean_a completionIncrement = populationConcentration/p,
    completionCollision R S T p
      <= populationConcentration(R,S,p)*populationConcentration(R,T,p)/p.
  For prime R this is <=1/p. The whole positive recursive majorant is
  bounded by the sum of reciprocal moduli in the supplied list. This
  coarse bound is NOT a small relative correlation estimate.

SCOPE: The weighted remainder avoids the previous error of charging one
on almost every collision phase. Its bound by actual coverage can itself
be vacuous in a comparison with that same coverage probability. A strict
relative estimate, or control of the negative cancellations in the exact
covariance recurrence, is still needed. No hidden uniform contraction,
independence of core translates, or endpoint positivity was assumed.

Spec.lean remains unchanged, including the sole original sorry at line2177.
SHA256: 1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
The conjecture remains UNSOLVED; no proof or disproof has been submitted.

=== Signed displacement cancellation (continuation checkpoint) ===
Verified files:
  CompletionDisplacement.lean
  CompletionDisplacementBounds.lean
Logs:
  /tmp/completion_displacement.log
  /tmp/completion_displacement_bounds.log
Both compile and print only propext, Classical.choice, Quot.sound.

signedCompletionSource is completionCollision minus the product of the
mean completion increments. Its complete displacement mean modulo p is
exactly zero. Translation acts by a cyclic shift on the second increment
vector. The source depends on the displacement only modulo p. Its full
period L1 sum is at most 2*p*meanIncrement(S)*meanIncrement(T).

Balanced residue counts yield the finite bound, for every D:
  abs(sum_{d<D} signedCompletionSource(P,S,T+d,p))
    <= populationConcentration(P,S,p)*populationConcentration(P,T,p)/p.
The normalized bound has an additional factor 1/D.

averaged_coverageCovariance_insert_error and its upper-bound version
retain the recursive child covariance EXACTLY. Only the source has been
estimated. No independence or cancellation of the child covariance is
asserted. Iterating requires tracking how the child populations depend
on both the displacement and the selected residue. Splitting successive
residue classes risks accumulating products of moduli. No sufficiently
small relative correlation estimate, proof, or disproof has been found.

Resource checkpoint: $157.79 and 10h57m remaining.
Spec.lean remains unchanged with the original sole sorry.

=== Exact obstruction to short-period child cancellation (VERIFIED) ===
File: Submission/CompletionDisplacementObstruction.lean
Log: /tmp/completion_displacement_obstruction.log
Compiled olean, all four printed axiom audits contain only propext,
Classical.choice, Quot.sound. No holes in this file.

For P={3}, inserted prime p=2, S=T={0}:
  two_prime_source_short_sum:
    sum_{d<2} signedCompletionSource(P,S,T+d,2) = 0.
  two_prime_covariance_short_sum:
    sum_{d<2} coverageCovariance({2,3},S,T+d) = 1/9.
  two_prime_child_short_sum:
    sum_{d<2} mean_{a mod 2} Cov_P(S minus a,(T+d) minus a) = 1/9.
  two_prime_covariance_full_sum:
    sum_{d<6} coverageCovariance({2,3},S,T+d) = 0.

Thus a complete displacement period for the newly inserted prime does
NOT eliminate the recursive child covariance. This directly refutes the
naive recursive cancellation shortcut, not the target conjecture. It
illustrates the product-period issue. It does not rule out a more subtle
quantitative estimate under the interval/scale hypotheses of the target.

The original conjecture remains unresolved. No target proof or disproof
was obtained, and Spec.lean was not modified during this continuation.

=== Relative signed-source bound (VERIFIED; conjecture still unresolved) ===
File: Submission/CompletionRelativeDisplacement.lean
Log: /tmp/completion_relative_displacement.log
Compiled olean. The three printed axiom audits contain only propext,
Classical.choice, Quot.sound.

Let F_P(S) be the actual populationCoveredFraction S P. For p not in P:
  populationConcentration_eq_insertion_gain:
    concentration(P,S,p) = p*(F_(P+p)(S)-F_P(S)).
  concentration_product_eq_gain_product:
    concentration(S)*concentration(T)/p
      = p*(F_(P+p)(S)-F_P(S))*(F_(P+p)(T)-F_P(T)).
  concentration_product_le_relative_cover bounds this by
    p*F_(P+p)(S)*F_(P+p)(T).

signedCompletionSource_displacement_relative and
averaged_coverageCovariance_insert_relative_error give this relative bound
on the signed source sum, and on the exact insertion error respectively.
The latter still retains the complete recursively filtered child covariance.

averaged_translatedCovariance_insert_relative_error normalizes by D:
  abs(averaged covariance minus averaged child covariance)
    <= (p/D)*F_(P+p)(S)^2,
for any translated copy T=S+b. Choosing b at least the interval length
keeps the populations disjoint, without changing the estimate.

This is a relative ONE-PRIME estimate, not the all-depth correlation
premise needed by LogLossSquareCubicReduction. A naive iteration partitions
displacements by the previously inserted moduli. The resulting subranges
have strides equal to their product, and the boundary costs can acquire
prefix products. Factorizing independent phase means after a COMPLETE
prefix period does not remove the length of that period. No proof that
these losses are sublinear-exponential has been obtained.

Other endpoint avenues reviewed: critical initial-core density, exposure
budget bootstrapping, greedy encodings, and uniform-in-depth positive
sieve cost. Their missing premises were not discharged. In particular the
existing critical positive-cost supersolution obstruction must not be
ignored when trying to upgrade the uniform slow cost to inverse-log-square
scale. No target proof/disproof is claimed.
Spec.lean remains unchanged with its original sole sorry.

=== Complete displacement-period bound and necessary generic loss (VERIFIED) ===
Files:
  CompletionFullPeriod.lean
  CompletionRelativePeriodObstruction.lean
  CompletionPeriodLossNecessary.lean
Logs:
  /tmp/completion_full_period.log
  /tmp/completion_relative_period_obstruction.log
  /tmp/completion_period_loss_necessary.log
All compile with oleans. Every printed axiom audit contains only propext,
Classical.choice, Quot.sound. No target theorem is used as a dependency.

CompletionFullPeriod:
  displacementPhaseEquiv enumerates all residue phases by translating one
  fixed phase through Q=product(P). This is an actual CRT equivalence.
  populationCoveredFraction_full_displacement:
    mean_{d mod Q} F_P(S union (T+d)) = F_P(S)*F_P(T).
  coverageCovariance_full_displacement:
    mean_{d mod Q} Cov_P(S,T+d) = 0, INCLUDING all recursive child terms.
  coverageCovariance_displacement_mod proves the actual period Q.
  coverageCovariance_full_abs_sum <= 2*Q*F_P(S)*F_P(T).
  coverageCovariance_displacement_sum_relative:
    abs(sum_{d<D} Cov_P(S,T+d)) <= Q*F_P(S)*F_P(T), for EVERY D.
  The latter is a complete all-prime relative bound, but Q is exponentially
  too large for the existing endpoint correlation reductions.

CompletionRelativePeriodObstruction gives a small exact example:
  P={5,7}, S={0,1}, T={35,36}, D=2.
  F_P(S)=2/35.
  sum_{d<2} Cov_P(S,T+d)=62/1225.
  (sum_{p in P}p)*F_P(S)^2=48/1225, strictly smaller.
  All translated populations T+d are disjoint from S.

CompletionPeriodLossNecessary generalizes this analytically:
  For distinct primes p,q>=3 and S=range 2,
    F_{p,q}(S)=2/(p*q), F_{p,q}(range 3)=0.
  At offset b=p*q, the D=2 covariance sum is F-2F^2.
  no_uniform_additive_displacement_cost proves, for EVERY real C, an
  actual two-prime example with |P|=2, population and averaging lengths 2,
  and b>=2, for which the absolute covariance sum exceeds
    C*(sum_{p in P}p)*F_P(range 2)^2.
  The primes are chosen symbolically using their infinitude, not by a scan.

SCOPE: This rules out replacing the full product loss by a constant times
an additive prime budget in a theorem about arbitrary separated translates.
The counterexamples use a FAR offset b=product(P), not adjacent blocks.
They do NOT refute the adjacent-block correlation premises, the quadratic
Jacobshtal conjecture, or a genuinely interval-local improvement. Adjacency
and interval length relative to the prime budget would need to enter any
successful stronger estimate. No such estimate has been proved.

Spec.lean remains unchanged with its sole original sorry at line 2177.
The conjecture is still unresolved; no target proof or disproof submitted.

=== Nearby-displacement endpoint criterion (VERIFIED, CONDITIONAL) ===
Files:
  NearbyDisplacementCriterion.lean
  NearbyDisplacementQuadraticReduction.lean
Logs:
  /tmp/nearby_displacement_criterion.log
  /tmp/nearby_displacement_quadratic_reduction.log
Both compiled with oleans. Printed axiom audits contain only propext,
Classical.choice, Quot.sound. No original conjecture dependency is used.

nearbyCovarianceSum(P,m) is the sum over d<m of
  Cov_P(range m, range m translated by m+d).
Unlike the preceding generic displacement statements, only nearby disjoint
blocks occur. All their positions lie in range(3m).

Unconditional finite theorem void_triple_le_nearby_covariance:
  m*V_P(3m) <= m*V_P(m)^2 + nearbyCovarianceSum(P,m).
void_triple_of_nearby_covariance turns a supplied bound
  nearbyCovarianceSum <= m*(a-1)*V_P(m)^2
into V_P(3m)<=a*V_P(m)^2, for m>0.

ternary_scaled_tail proves exact ternary iteration:
  if V(3n)<=a*V(n)^2 for n>=m, a>=1, and a*V(m)<=exp(-E),
  then V(3^j*m)<=exp(-E*2^j).
No factor-four relaxation, which would lose the critical gain, is made.

LogLossNearbyCovarianceBound(C,B) is an EXPLICIT UNPROVED premise:
  eventually k, all prime sets |P|<=k, all m>=k,
    nearbyCovarianceSum(P,m)
      <= m*(exp(C*k/log(k)^B)-1)*V_P(m)^2.

exists_nearby_covariance_quadratic_reduction proves that some fixed B>0
makes that premise sufficient for the unchanged target conclusion, for
any C>=0. It reuses the verified logarithmic-loss void seed. With the prior
N=Nat.log 16 (t^(b+2)), the new iteration uses 40N ternary steps:
  3^(40N)<=16^(16N), 5^(16N)<=2^(40N).
Thus the same exact dyadic length budget and phase-entropy domination apply.
The proof normalizes the prime set, handles the full arithmetic tail and
finite prefix, and retains the local covariance hypothesis throughout.

REMAINING GAP: This gives a sufficient LOCAL averaged estimate directly
aligned with the signed-source work; it does NOT prove that estimate.
The all-prime product-period bound is too costly. Its far-offset
counterexamples do not negate this nearby premise. Filtered child
populations are still not intervals, and no valid low-loss recursion for
these local averages has been established. Reviews of minimum-count
frequencies, one-hit tail padding, and low-count concentration supplied no
missing unconditional estimate. The original conjecture is still unresolved.
Spec.lean remains unchanged with its sole original sorry.

=== Deterministic initial-core and stability review (NO NEW SETTLEMENT) ===
Revisited SparseSmallPrimeQuadratic, BudgetScaleCoreDeficit,
InitialCoreDensityReduction, ReciprocalBudgetQuadratic, TwoSurvivorReduction,
and the signed/nonnegative Selberg optimization results.

The complete initial-core deficit remains an unconditional NECESSARY
condition for a long cover, not a contradiction. At the budget cutoff k,
the tail reciprocal mass has order log(log k)/log k. The verified row
bounds charge that mass; it cannot be discarded merely because it tends
to zero. A critical lower count of order m/log(k)^2 with a fixed coefficient
would still not dominate a tail budget of order
m*log(log k)/log(k)^2 for all k. A fixed large interval dilation cannot
absorb the unbounded log(log k) factor.

No uniform lower density at critical level, no useful joint stability
bound for the selected tail rows in a low-count core phase, and no
prime-replacement or tensor-amplification argument was proved. The
existing conditional core-density and local-covariance reductions remain
conditional. No new Lean theorem is claimed from this review.

Spec.lean is unchanged with its original statement, import, and sole sorry.
The target remains unresolved; there is no complete proof/disproof to submit.

=== Aggregate-variance and endpoint continuation (NO SETTLEMENT) ===

Re-read the existing large-sieve/Bennett diagnostic, the exact nearby
covariance criterion, BudgetScaleCoreDeficit, InitialCoreDensityReduction,
and the earlier insertion, tensor-amplification, and joint-fluctuation
reviews. No new unconditional estimate closing either endpoint was found.
The p^2 Fourier-energy normalization and all-phase entropy cost remain
necessary. The critical initial-core lower density and the nearby covariance
premise remain unproved; neither has been silently inserted into a proof.

No new mathematical Lean file was added and Spec.lean was not edited.
The original theorem still has its sole sorry at line2177. Its SHA256 is
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
No proof or disproof of the original conjecture has been completed.

=== Quantitative profile, optimal cover, and downward-resampling review (NO SETTLEMENT) ===

The proposed affine profile c*delta_k*(m-C*k^2)_+ was checked against
largest-prime deletion. Near its threshold the formal margin looks favorable,
but an upper row coefficient larger than c causes a loss proportional to m/p
at longer lengths. A restricted length window does not propagate to the
previous cardinality at its upper end. No compatible all-length coupled
lower/upper profile was obtained.

Re-read OptimalCoverCore, OptimalCoreExchange, MultiPrimeExchange,
SinglePrimeExchange, OptimalCoreGapCap, and the overlap/count reductions.
The apparent new observations about unused-prime injectivity, inclusion of
primes below the survivor count, and smooth survivor differences are already
proved in OptimalCoverCore. They do not supply a budget-improving exchange.
No such exchange or new structural endpoint estimate was proved.

Re-read SurvivorResampling, PrimeCoverResampling,
PopulationSensitiveRowVariance, RowConditionalVariance, and the Fourier
normalization results. Downward changes are indeed controlled by current
survivor hits, but this does not turn the raw second moment into a
survivor-only quantity or remove the jump-cap dependence in a lower-tail
entropy estimate. No sufficiently strong pointwise downward self-bound or
tilted aggregate variance bound was obtained. The old raw-second-moment
counterexample is not claimed to disprove every downward-minimum bound.

No new mathematical Lean theorem is claimed from this continuation.
Spec.lean is unchanged; erdos_970 still has its original sole sorry.
There is no completed proof or disproof to submit.

=== One-sided lower-tail continuation (NO SETTLEMENT) ===
Re-examined whether the full-centred Gaussian obstruction leaves a useful
one-sided estimate. The earlier PGF review already records the relevant
zero-phase rough-number deficit at length y^2: classical PNT and sharp
Mertens asymptotics give count/mean -> exp(gamma)/2 < 1. Its rare-phase
contribution obstructs exact Poisson PGF domination. This asymptotic argument
remains an informal observation here, not a new Lean theorem.

Re-read the weak soft-endpoint criteria, initial derivative/local results,
and the existing positive-parameter counterexamples. None proves a uniform
positive parameter or a sufficient rate. A suitably weaker sub-mean tail or
critical soft-endpoint inequality remains unproved. No new mathematical
Lean result or completed settlement was obtained. Spec.lean was not edited.

=== Selected-row concentration continuation (NO SETTLEMENT) ===
Re-read the exact row-variance and residue-Fourier identities and the
budget-scale core deficit. The potential shortcut from aggregate variance
to arbitrary selected rows is already excluded by the normalization in
selected_centeredHits_sq_le_energy: p * discrepancy^2 <= energy, whereas
energy = p^2 * classVariance. The selected-row Cauchy--Schwarz and necessary
cover-energy estimates are already proved in ResidueFourierVariance. They
do not yield the needed density-conditioned concentration bound for a rare
low-count core phase. No stronger such bound was proved in this continuation.
No mathematical Lean source was added or changed. Spec.lean remains unchanged
with its original conjecture and sole sorry; no settlement is claimed.

=== Gibbs-weighted row variance obstruction (VERIFIED AUXILIARY RESULT) ===
New compiled file: Submission/GibbsRowVarianceObstruction.lean.
Namespace: Erdos970.GapAverages.GibbsRowExample.
This is NOT a disproof of erdos_970.

For the complete initial core P={2,3}, m=35, and larger prime p=7,
the exact joint distribution of survivor count N and conditional row
variance V is:
  probability 1/3: N=11 and V=12/49;
  probability 2/3: N=12 and V=10/49.
A Fin6-to-Phase(P) CRT equivalence transports kernel-checked natural-count
data into the actual phase model. joint_mean proves the full joint law.
For EVERY real t>0, gibbs_row_variance_strictly_increases proves
  E[V] * E[exp(-t*N)] < E[exp(-t*N)*V].
The exact difference is 4*(exp(-11*t)-exp(-12*t))/441.
Thus even an arbitrarily small positive Gibbs tilt cannot in general
suppress the row variance. not_uniform_gibbs_row_variance_suppression
records the negation of that auxiliary uniform comparison. A comparison
with a larger constant or an explicit error is NOT refuted by this example.

Final Lean build exit status 0; both main theorem axiom audits contain only
propext, Classical.choice, Quot.sound. No sorry or native_decide was used.
Build log: /tmp/gibbs_row_variance_obstruction.log.
Spec.lean remains unchanged with SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9
and its original sole sorry. No completed proof/disproof of erdos_970 exists
in this continuation, and none has been submitted as a solution.

=== Uniform endpoint stochastic-shift obstruction (VERIFIED AUXILIARY RESULT) ===
The original target submission was sent to the verifier once and failed, as
expected from its remaining sorry. No successful settlement is claimed.

New compiled file: Submission/EndpointShiftObstruction.lean.
Namespace: Erdos970.GapAverages.EndpointShift.
The proposed repair to failed endpoint stochastic domination was a fixed
additive shift B. Targeted finite tests in /tmp/endpoint_shift_diagnostic.py
found no shift-one failure in the tested sets and lengths; those tests were
NOT used as proof, and the following analytic argument disproves the uniform
claim for EVERY fixed real B.

UniformSignedShift(B) is the signed exponential comparison
  (exp(s)-1)*(G_P(-s,m)-density(P)*exp(B*s)*F_P(-s,m)) <= 0
for all prime sets, interval lengths, and real s. Uniform stochastic domination
of the endpoint-conditioned count by the unconditioned count+B implies this
comparison, using the monotone function (exp(s)-1)*exp(s*x).

Verified consequences of the candidate (all premises retained):
* laplace_of_signed_shift:
    F_P(-s,m) <= exp(m*density(P)*(exp((B+1)*s)-exp(B*s))).
* centered_mgf_of_signed_shift: if abs((B+1)*s)<=1, then
    E exp(s*(N-m*density(P))) <= exp((B+1)^2*m*s^2).
* An individual phase is bounded using its exact reciprocal probability.
  For P=primesBelow(64*t^6), product(P)<=4^(64*t^6), m<=4096*t^12,
  and abs(B+1)<=t^3, evaluating at s=+/-1/t^3 forces
    abs(roughCount(P,m)-m*density(P))
      <= (64*log(4)+4096*(B+1)^2)*t^11.
* Comparing m=t^12 and m=4096*t^12, where rough counts equal prime
  counts minus the common core count plus one, forces the forbidden
  prime-counting recurrence with error O(t^11).

not_uniformSignedShift and not_uniformStochasticShift prove the exact
negations of these AUXILIARY uniform proposals for every fixed B. They do
NOT negate erdos_970, nor rule out every cardinality-dependent shift or a
one-sided exponential comparison at a single positive parameter.

Final Lean build exited 0; all four printed axiom audits contain only
propext, Classical.choice, Quot.sound. Log: /tmp/endpoint_shift_obstruction.log.
No holes or untrusted numerical computation occur in the new proof.
Spec.lean is unchanged and still has the original conjecture and sole sorry.
No complete proof or disproof of the original conjecture has been obtained.

=== Multiplicative candidate-grid obstruction (VERIFIED AUXILIARY RESULT) ===

New file: ProductGridObstruction.lean (298 lines).
Namespace: Erdos970.ProductGrid.

For K=2^t, choose all odd primes <=K, with residue zero, and 2t+1
new distinct primes greater than K^2, assigning residue 2^e to the e-th
new prime (0<=e<=2t). Every x*y with 1<=x,y<=K is covered: either a
factor has an odd prime divisor <=K, or both factors are powers of two.
The prime budget is <=pi(K)+2t+1=o(K), proved using the existing elementary
prime-counting density limit. CRT realizes this as translated coprimality.

Verified main results:
  product_grid_cover
  primes_card_density_zero
  translated_product_grid_cover
  no_fixed_linear_product_grid
  arbitrarily_large_grid_counterexamples
  translated_grid_cover_with_survivor

Thus for EVERY fixed natural C, the proposed statement that some
1<=x,y<=C*k always has gcd(a+x*y,n)=1 is FALSE, including after discarding
any finite range of k. This rules out the direct bilinear-grid sufficient
lemma; it does NOT disprove the interval conjecture.

The same CRT translate explicitly has a survivor at an index i with
K<i<=2K, using Bertrand's postulate. The extra primes exceed K^2, so
they hit only their assigned powers of two in that interval, whereas an
odd prime i>K avoids the core. This confirms that these examples do not
cover the whole quadratic interval.

Build exit status 0, no warnings. All six printed axiom audits use only
propext, Classical.choice, Quot.sound. Log: /tmp/product_grid_obstruction.log.
No numerical search or untrusted computation was used.
Spec.lean remains unchanged, with SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9.
The original erdos_970 still has its sole sorry. No new submission was made.

Other reviews in this continuation supplied no new target implication:
- Naive tensor amplification still fails the distinct-prime residue model.
- Varying the cutoff in the currently charged lower-sieve/tail estimates
  did not remove their critical logarithmic deficit.
- The existing common-kernel radial/nonradial support barriers were checked;
  no spectral positivity at the needed square-root cutoff was obtained.

=== Full-resampling Gibbs transport (VERIFIED POSITIVE AUXILIARY ESTIMATE) ===

New file: GibbsResamplingTransport.lean (166 lines).
Namespace: Erdos970.Resampling.

For an arbitrary finite survivor population S, a positive modulus p, a
nonnegative tilt t, and a genuine cap C_a<=B on every residue row, the file
proves
  E_b [e^(-t N_b) E_a (N_a-N_b)^2]
    <= B*(1+e^(tB))/p * E_b [e^(-t N_b) N_b],
where N_b counts points of S avoiding row b. This includes exposed private
positions; it is not a pointwise current-survivor bound, and does not move
unweighted row variance into a Gibbs expectation.

Proof uses the exact two-row difference, the row cap, exchange of the two
residue averages, and w_b<=e^(tB)*w_a. No independence is asserted between
old survivor rows. prime_insert_gibbs_resampling transfers the estimate to
actual prime phases and averages over all old core configurations, retaining
the full Gibbs normalizer and explicit cap hypothesis.

The coefficient is sharp already for S={0}, p=2, B=1. Consequently there is
no coefficient uniform in all nonnegative tilt parameters even in that
one-point example. This does NOT refute estimates at one fixed positive
tilt, nor a better bound using additional interval/core structure.

All four printed audits list only propext, Classical.choice, Quot.sound.
Build exit status 0 with no warnings. Log: /tmp/gibbs_resampling_transport.log.

The new estimate does NOT yet yield the missing critical lower-tail bound:
for the available small-prime row caps, the retained e^(tB) factor is too
large at a fixed positive parameter. Conditional small-core entropy and
large-prime variance were considered, but no uniformly sufficient endpoint
estimate was proved. The original Spec.lean remains unchanged with its sole
sorry; no completed proof or disproof has been submitted.

=== Finite entropy, tensorization, and Herbst integration (VERIFIED) ===

New compiled files:
  FiniteGibbsEntropy.lean
  PopulationGibbsEntropy.lean
  FiniteHerbstBound.lean
  EntropyCapBudgetBarrier.lean
Namespace: Erdos970.FiniteGibbs.

The pending PopulationGibbsEntropy file needed an import of
PopulationLowCountBennett, propositional reordering in the commuting-filter
identity, and one zero-multiplication simplification. After those fixes,
the full induction over prime coordinates builds and has clean axioms.

FiniteGibbsEntropy proves a positive-function variational inequality,
convexity of entropy under finite averaging, two-coordinate tensorization,
and the one-coordinate full-resampling entropy estimate with constant one.
PopulationGibbsEntropy transfers these to arbitrary finite populations:
  Ent(exp(-t*N)) <= t^2*D(t)*E[exp(-t*N)*N],
  D(t) = sum_{p in P} (1+exp(t*B_p))*B_p/p,
assuming nonnegative tilt and genuine row caps classHits(S,p,a)<=B_p.
All private-point costs and exponential factors remain explicit.

FiniteHerbstBound proves the complete analytic integration step:
  If Ent(exp(-t*f)) <= t^2*A*E[exp(-t*f)*f] on 0<t<=T,
  with A>=0 and T>0, then
    E exp(-T*f) <= exp(-E[f]*T/(1+A*T)).
Proof differentiates the finite Laplace sum and free energy G=-log F,
then proves monotonicity of G(t)*(1+A*t)/t and uses its right limit E[f]
at zero. No unproved interval-uniform derivative inference is used.

population_laplace_cap applies this with A=D(T), and the exact population
mean |S|*density(P). population_survivor_of_cap_budget proves a sufficient
condition for every phase to contain a survivor, retaining the necessary
cost log(card(Phase P)). The mass of a single phase is not discarded.

EntropyCapBudgetBarrier then proves that this specific certificate NEVER
meets its strict cost inequality when 2 belongs to P, for ANY population,
nonnegative tilt, and valid nonnegative row caps:
  |S|*density(P)*T/(1+D(T)*T) <= 1/2 <= log(card(Phase P)).
The proof uses B_2>=|S|/2, density(P)<=1/2, the prime-two summand of D(T),
and exp(x)>=1+x. It is an exact restriction on this cap-based certificate,
NOT a disproof of Jacobsthal's quadratic bound or of sharper entropy
estimates exploiting conditional row oscillation.

Printed audits for all main theorems in these files contain only propext,
Classical.choice, Quot.sound. Build logs:
  /tmp/finite_gibbs_entropy.log
  /tmp/population_gibbs_entropy.log
  /tmp/finite_herbst.log
  /tmp/entropy_cap_budget_barrier.log
No holes, native_decide, untrusted computations, or dependency on erdos_970
were used for these auxiliary theorems.

The conjecture is NOT settled. Spec.lean remains unchanged, with its sole
original sorry. No completed proof or disproof is ready for submission.

=== Conditional oscillation refinement and exact-scale barrier (VERIFIED) ===

New compiled files:
  GibbsOscillationTransport.lean
  PopulationOscillationEntropy.lean
  OscillationCertificateBarrier.lean

The Gibbs resampling transport estimate now also holds with B bounding
|classHits(S,p,a)-classHits(S,p,b)|, not the absolute row sizes. Its
coefficient is still (1+exp(t*B))*B/p. Balanced rows have coefficient zero.
This is a genuine improvement over the raw-cap method, not an assumption
that private-point costs vanish.

PopulationOscillationBound P S B explicitly requires the oscillation bound
for every conditional population populationSurvivors S Q r with Q subset P
and p in P minus Q. These are actual sieve conditionings, NOT arbitrary
subsets of S. The hypothesis is preserved upon fixing a new residue row.
This proves full product tensorization, followed by the finite Herbst bound
and a phase-uniform survivor certificate with the same explicit phase-space
logarithm. All arithmetic cap assumptions remain visible.

The refined worst-case-cap certificate also cannot be uniformly sufficient
at any fixed positive natural quadratic scale C*k^2. This is proved, not
merely suspected, in no_uniform_quadratic_oscillation_certificate C K hC,
including after any finite cardinality threshold K.

Key facts:
* log(card(Phase P)) >= card(P)/2.
* If 2 belongs to P and the strict certificate cost inequality holds, then
    card(P)*B_2 < 2*card(S).
  This follows from D(T)>=B_2 and density(P)<=1.
* The shifted-zero phase r_p=p-1 on range(m) has its two residue-row count
  difference EXACTLY equal to the prior rational alternatingCount(P,1,m),
  transported to real numbers. The arithmetic equivalence is
    p divides (1+j) iff j mod p = p-1.
* Take an odd-prime parity counterexample Q at length C*card(Q)^2 and adjoin
  prime two. A hypothetical certificate at C*(card(Q)+1)^2 would bound the
  conditional parity oscillation by 2*C*(card(Q)+1). Moving the endpoint
  back costs only C*(2*card(Q)+1), contradicting the already verified
  unbounded parity discrepancy at the original exact quadratic length.

Thus even replacing raw row caps by these worst-case conditional
oscillation caps does not settle the target. This does NOT rule out
phase-dependent Gibbs estimates or a different arithmetic argument, and
it is NOT a disproof of erdos_970. The parity examples still have survivors.

All printed main-theorem axiom audits use only propext, Classical.choice,
Quot.sound. Builds exit zero without warnings. Logs:
  /tmp/gibbs_oscillation_transport.log
  /tmp/population_oscillation_entropy.log
  /tmp/oscillation_certificate_barrier.log
No new holes or untrusted computations were introduced.

Spec.lean remains unchanged with its original sole sorry. No proof or
disproof of the original conjecture has been completed or submitted.

=== Signed Gibbs entropy and sharper secant estimate (VERIFIED) ===

New files:
  FiniteGibbsDirichlet.lean
  PopulationSignedEntropy.lean

The elementary exponential secant bound has been improved to
  (exp x-exp y)*(x-y) <= (exp x+exp y)/2*(x-y)^2.
The proof differentiates (u-2)*exp u+u+2 and uses exp(-u)>=1-u.
This proves a coefficient 1/2 in the full weighted-resampling entropy bound,
improving the earlier verified coefficient 1. The earlier theorem remains
valid; its coefficient was not claimed to be optimal. Exponential transport
factors in the separate row-cap estimate have NOT been removed.

A signed one-coordinate cost is now explicit:
  signedResidueCost S p t = t*E_a[exp(-t*N_a)*centeredHits(S,p,a)].
It majorizes the actual entropy for every real t and is nonnegative. Balanced
rows give cost zero regardless of population size. The sharper cap corollary
residue_entropy_half_cap still charges (1+exp(t*B))*B/p, with an extra 1/2.

signedPopulationCost recursively averages these actual costs over all other
fixed coordinates. population_entropy_le_signed proves full tensorization
for a nodup list of positive moduli and arbitrary finite population. No
worst-case conditional cap or independence of row counts is assumed.

population_laplace_of_signed_cost and population_survivor_of_signed_cost
apply the existing finite Herbst integration. They explicitly require a
bound on the signed cost by t^2*A*E[exp(-t*N)*N] for all 0<t<=T. The survivor
criterion also retains log(card(Phase P)). This arithmetic cost estimate is
NOT proved at a uniform quadratic scale, so these results do not settle
Erdos970.

Both files compile without warnings. Printed main theorem audits contain
only propext, Classical.choice, Quot.sound. Logs:
  /tmp/finite_gibbs_dirichlet.log
  /tmp/population_signed_entropy.log

Earlier in this continuation the suggested core-dependent Bennett averaging
step was found ALREADY implemented in PhaseUnionBennett.lean. That review
produced no new result and must not be counted as progress.

Spec.lean remains unchanged, with its original sole sorry. No proof or
disproof of erdos_970 is ready for submission.

=== Exact private-position Gibbs balance (VERIFIED) ===

New file: PopulationPrivateEntropy.lean

privateGibbsMass recursively averages the actual private positions, with
weight 1-1/p on the unique hitting coordinate. The Gibbs factor is that of
the final survivor count; it is not replaced by an unweighted mean.

signedPopulationCost_eq_private proves the exact identity
  signedPopulationCost ps S t = t * (privateGibbsMass ps S t -
    (sum p in ps.toFinset, 1/p) * laplaceMoment(count S ps.toFinset,t)).
It applies to nodup lists, arbitrary finite populations, and every real tilt.
No primality or positivity is needed for the identity itself.

Also verified:
* privateGibbsMass_nonneg for positive moduli;
* privateGibbsMass_ge_survivor_balance at positive tilt, which is a LOWER
  bound, not the upper bound needed for concentration;
* population_survivor_of_private_stability, conditional on
    privateGibbsMass <= (sum 1/p + A*t) * E[exp(-t*N)*N]
  for all 0<t<=T, with the full logarithmic phase-space cost retained.

No uniform quadratic-scale private stability estimate was obtained. This
reformulation does not settle the conjecture and does not assert that private
mass vanishes at a covered phase.

Lean detail: rewriting List.toFinset_cons inside a partially applied count
under laplaceMoment needed an explicit equality for the WHOLE real-valued
laplaceMoment expression; simp on the finset expression alone did not rewrite
its dependent implicit arguments.

Build /tmp/population_private_entropy.log exits zero without warnings.
Printed main theorem audits use only propext, Classical.choice, Quot.sound.
Spec.lean is unchanged with its original sole sorry. No final proof is ready.

=== General finite thinning and exact void/Laplace equivalences (VERIFIED) ===

New compiled files:
  PrimeDilutionGeneral.lean
  FiniteThinningGeneral.lean
  ThinningVoidEquivalence.lean

PrimeDilutionGeneral:
- exists_large_prime_reciprocal_sum: the reciprocal sum of a finite set of
  genuine primes above any prescribed threshold exceeds any real target.
  Uses Mathlib's divergence of prime reciprocals and a finite small-part bound.
- exists_dilution_primes_target: for 0<d<1 and 2/B<=d, a finite large-prime
  tail has survival product in [d-1/B,d] and reciprocal sum at most 2/d.
  The earlier pending compile error was fixed by rewriting 2/B as 2*(1/B).

FiniteThinningGeneral:
- laplace_expansion at every real parameter, not only log 64.
- covered_laplace_error_general: with d=1-exp(-t), reciprocal sum <=K,
  and tail product in [d-1/B,d], the error at length m<=B is at most
       2^m * (m^2*K+m)/B.
- exists_padding_approx_general: for any t>0, finite length bound M, and
  eta>0, a disjoint finite prime tail simultaneously approximates all void
  probabilities at m<=M by countLaplace(P,t,m), and approximates the density
  by density(P)*(1-exp(-t)). All added primes are at least M.

ThinningVoidEquivalence:
- exists_padding_limits packages the preceding finite approximations into
  sequences of genuine finite prime sets, with proved density/void limits.
- exponential_void_iff_laplace(c): ExponentialVoidBound(c) is equivalent to
       countLaplace(P,t,m) <= exp(-c*m*density(P)*(1-exp(-t)))
  uniformly for all prime sets, t>0, and m. No sign assumption on c is needed
  for this equivalence. Neither side is asserted unconditionally.
- geometric_void_iff_laplace: analogous equivalence with right side
       (1-density(P)*(1-exp(-t)))^m.
- Forward directions use finite prime thinning and preservation of inequalities
  under limits. Reverse directions use the soft-to-hard limit t -> infinity.

All three files compile without warnings, and printed audits for their main
results use only propext, Classical.choice, Quot.sound. No target sorry is used.
Logs:
  /tmp/prime_dilution_general.log
  /tmp/finite_thinning_general.log
  /tmp/thinning_void_equivalence.log

Scope: these are auxiliary approximation/equivalence results, NOT a quadratic
bound and NOT a disproof. The asymptotic obstruction to unit-constant Poisson
bounds mentioned earlier remains unformalized. There is still no proved
positive-rate lower-tail estimate sufficient for the target. Spec.lean remains
unchanged with its original sole sorry; no completed submission is ready.

=== Positive genuinely nearby coverage covariance (VERIFIED) ===

New compiled files:
  NearbyCovarianceBlocks.lean
  NearbyCovarianceCertificate.lean
  NearbyCovarianceObstruction.lean

This continuation tested the stronger zero-loss sign premise
  nearbyCovarianceSum(P,m) <= 0 whenever P.card <= m.
It is FALSE, even with genuinely nearby disjoint blocks, not only at offsets
comparable to the full prime product.

Verified example:
  P={3,5,7,11,13}, card(P)=5, m=7, product(P)=15015.
  coveredFraction(P,7)=36/15015.
  At cyclic start a=7499, both length-seven blocks starting at offsets 0 and 9
  are covered. Offset9=m+2 lies in [m,2m), as required by nearbyCovarianceSum.
  Therefore the sum of nearby joint coverage probabilities is at least1/15015.
  Since 15015 > 7*36^2, the nearby covariance sum is strictly positive.

The finite cover-count certificate uses150 blocks of100 starts and a final
block of15 starts, each checked by decide +kernel. No native_decide or external
numeric facts are used. The raw whole-period check was too memory-intensive.

IMPORTANT LEAN IMPLEMENTATION DETAILS:
- set_option Elab.async false kept the independent short-block checks within
  the memory limit.
- Applying a generic finite-count splitting identity to a fully COMPUTABLE
  outer filter caused the kernel to evaluate the entire large closed count
  during definitional comparisons. Even an unused local proof of that identity
  could trigger this evaluation. Irreducibility attributes did not fix it.
- The assembly instead pins Classical.propDecidable for the OUTER filter in
  coverCount/classicalCount. classicalCount_eq proves equality to the ordinary
  short computable filters. The block certificates remain kernel checked.
  This is ordinary decidability-instance independence, not an unchecked count.
- The cyclic_void_count bridge explicitly takes the outer DecidablePred so the
  assembled count can be transported without forcing whole-period evaluation.
- A remaining difference between finite and classical if-decision instances in
  the joint-cover lower bound was handled by pointwise case splitting and
  sum_congr, not by claiming definitional equality of those instances.

Principal results in NearbyCovarianceObstruction:
  cyclic_void_count
  NearbyExample.actual_void
  NearbyExample.actual_joint_lower
  NearbyExample.nearby_covariance_pos
  NearbyExample.not_uniform_nonpositive_nearby
All compiled; printed axiom audits contain only propext, Classical.choice,
Quot.sound. Logs:
  /tmp/nearby_covariance_blocks.log
  /tmp/nearby_covariance_certificate.log
  /tmp/nearby_covariance_obstruction.log

Exact-integer Python diagnostics were used to locate the example:
  /tmp/nearby_covariance_exact.py and .log.
The formal proof does not trust these computations. Additional finite checks
of dyadic/ternary void inequalities passed for those tested sets; they establish
NO uniform bound and are NOT kernel-checked theorems.

SCOPE: this refutes only the stronger nonpositive-covariance premise. It does
not refute LogLossNearbyCovarianceBound, does not refute a ternary void inequality,
and does not refute erdos_970. No proof or disproof of the target was found.
Spec.lean remains unchanged with the original sole sorry. Nothing is ready for
submission as a settlement of the conjecture.

=== Further routes examined; NO new settlement or Lean theorem ===

The subsequent continuation examined three possible ways to remove the
remaining logarithmic loss. No proof file was edited during these checks.

1. Scale comparison / amplification.
   No multiplicative comparison for the actual Jacobsthal function was
   obtained. CRT does not automatically concatenate interval covers: a
   mixed-radix concatenation would require its block length to preserve all
   old prime residues, and an arbitrary covered block has no such period.
   Thus the existing polylogarithmic bound has not been bootstrapped to an
   absolute quadratic bound.

2. Interval-dependent quadratic certificates.
   An adaptive graph/forest interpretation of quadratic sieve polynomials
   was considered, but no uniform positive-mean certificate was established.
   Actual large-overlap packing controls only the high end; the moderate
   overlap term in QuadraticOverlapReduction is still uncontrolled.
   Neither a multiplicity cap nor small moderate mass may be assumed for
   an arbitrary cover.

3. Conditional row concentration and phase entropy.
   PopulationSensitiveRowVariance and ResidueFourierVariance retain actual
   conditional populations and Fourier weights. Their row caps, combined
   with conditional Bennett/Chernoff estimates, do not by themselves prove
   that there is no covering residue assignment.
   In particular, freezing a small core does NOT permit charging only the
   number of core phases: an existential covering assignment for the tail
   still has its own residue-space granularity. A small conditional covering
   probability need not be zero. The full tail configuration count must be
   retained (or replaced by a separately justified smaller count).
   No such improvement, nor a uniform relative row bound, was proved.

These are research diagnostics, not new kernel-checked results and not a
negation of erdos_970. Spec.lean is unchanged (SHA256
1de87242334d7c377997bd145cf1e1bc8ba90b92f776606b92290e42e92d07b9)
and still has its original sole sorry at line2177. No completed submission
is available.

=== Surviving-origin product-grid distinction (VERIFIED REDUCTION ONLY) ===

New compiled file:
  NonzeroProductGridReduction.lean
Namespace: Erdos970.NonzeroProductGrid.

GridBound C is an EXPLICITLY UNPROVED premise. It asks for a surviving product
x*y with 1<=x,y<=C*k, for any at-most-k prime residue sieve whose origin survives
(all forbidden residues are nonzero modulo their primes).

Verified theorems:
- next_bound_of_grid: such a product gives a positive surviving displacement
  <=(C*k)^2.
- jacobsthalBound_of_grid: the existing next-gap equivalence transfers this to
  arbitrary intervals.
- quadratic_bound_of_grid: for C>0, GridBound C implies the unchanged original
  quadratic conclusion, with real constant C^2.

All three printed axiom audits contain only allowed axioms. GapReduction.olean
was rebuilt because it was missing; no old proof was changed. Build logs:
  /tmp/grid_gap_reduction.log
  /tmp/nonzero_product_grid_reduction.log

IMPORTANT DISTINCTION: ProductGridObstruction uses zero residues for its small
prime core. It does NOT by itself refute this surviving-origin grid premise.
Conversely, no proof of the new premise was found. Bilinear sieve/counting,
multiplicative-character, and graph interpretations did not supply the required
uniform estimate. This new conditional reduction must not be invoked without
its GridBound hypothesis.

Finite diagnostics only (NOT KERNEL-CHECKED THEOREMS):
  /tmp/nonzero_product_grid_milp.py
  /tmp/nonzero_product_grid_milp.log
The MILP modeled all nonzero prime classes with at least two hits in the finite
multiplication table, plus singleton rows that can be realized by fresh primes.
It reported infeasibility of covers using K-1 primes at side lengths
K=8,10,12,15,20; K=30 timed out with no solution or bound. These solver reports
are not trusted by any Lean proof and imply no uniform grid theorem.
The diagnostic process has finished; no worker remains active.

SCOPE: no proof or disproof of erdos_970 has been obtained. Spec.lean is unchanged
and retains its original sole sorry. Nothing is ready to submit as a settlement.

=== Fixed-set square-root combination obstruction (VERIFIED AUXILIARY RESULT) ===

New compiled file:
  SquareRootCombinationObstruction.lean
Namespace: Erdos970.SquareRootCombination.
The principal result is not_fixed_square_root_combination.

Take P={17,19,23,29,31,37,41,43,47,53,59,61,67}, and Q={2}.
P has interval bound14 by the one-hit pigeonhole bound. Q has bound2.
Adjoining parity covers all27 positions0,...,26: parity covers the even
positions, and the thirteen odd primes are assigned the thirteen odd positions.
Nevertheless (sqrt(14)+sqrt(2))^2<27. Hence even disjoint genuine prime sets
cannot generally combine fixed-modulus interval bounds by rounding up the
square of the sum of their square roots.

The finite residue-cover certificate is checked by decide +kernel. The final
axiom audit contains only propext, Classical.choice, Quot.sound.
Log: /tmp/square_root_combination_obstruction.log

This does NOT disprove square-root subadditivity for the UNIFORM function h(k),
which uses maxima over all prime sets of the respective sizes. No proof or
counterexample to that uniform scale comparison was obtained. In particular,
the fixed-set obstruction must not be presented as a disproof of erdos_970.

The original target remains unresolved. Spec.lean has not been changed and
still contains its original sole sorry. No completed submission is ready.

=== Deterministic-tail/core-entropy continuation (NO NEW SETTLEMENT) ===

Revisited a legitimate distinction from merely freezing tail phases: if a
DETERMINISTIC upper bound on all selected tail rows turns a full cover into a
low-COUNT event for the core alone, then tail phase entropy has actually been
eliminated. In this situation it is valid to charge only core phase entropy.
This must not be confused with discarding the entropy of an existential tail
assignment without such a deterministic implication.

The available estimates still did not close this route. In particular,
SoftExposure.eventually_soft_quadratic_low_tail does control counts below a
fixed small multiple of m/log(k), but its decay exponent is only k^(4/5)/64.
For a core cutoff k^alpha, core log-phase-size has scale k^alpha. Choosing
alpha<4/5 favors the entropy comparison but leaves a fixed tail-count charge
larger than the small count threshold. Moving alpha sufficiently near1 makes
the tail charge small, but then this entropy comparison fails.

An on-paper leading-profile check also exposed the critical balance in trying
to sharpen this same construction: the sharp linear-sieve lower coefficient
at an exposure prime scale k^tau and the tail coefficient at cutoff k^alpha
are respectively log((2-tau)/tau) and log((2-alpha)/alpha). The latter exceeds
the former when alpha<tau, whereas alpha<tau is the favorable power comparison
for core entropy against an exp(-c*k^tau) estimate. This is a diagnostic for
these profiles only, NOT a Lean theorem and NOT a limitation of every possible
arithmetic argument. Lower-order/logarithmic costs cannot simply be discarded.

No new Lean theorem or target proof was obtained in this continuation.
Spec.lean is unchanged, with its original sole sorry. No submission is ready.

=== Nonzero-origin square-candidate obstruction (VERIFIED AUXILIARY RESULT) ===

New compiled file:
  NonzeroSquareGridObstruction.lean
Namespace: Erdos970.NonzeroSquareGrid.

For H>=3 use all primes <=H, all with forbidden residue1. The origin survives.
Every square x^2 with1<=x<=H is covered: x=1 uses2, x=2 uses3, and x>=3 uses
a prime divisor of x-1. The prime count is pi(H)=o(H), so every fixed linear
side multiplier C can be defeated, with arbitrarily large prime budgets.
Displacement2 always survives, so these are not full interval covers.

Main verified results:
- arbitrarily_large_square_cover;
- arbitrarily_large_integer_square_obstruction, using n=product(P), a=-1;
- no_fixed_linear_square_companion.
The last negates the square-only candidate assertion even with the explicit
assumption that a itself is coprime to n. All printed axiom audits use only
propext, Classical.choice, Quot.sound. No untrusted computation or sorry is
used by these results. Log: /tmp/nonzero_square_grid_obstruction.log.

SCOPE: This refutes the diagonal x=y simplification of the surviving-origin
product-grid proposal. It does NOT refute GridBound C for unrestricted x,y,
and it does NOT disprove erdos_970. The construction has a survivor at2.

No proof or disproof of the original target has been found. Spec.lean remains
unchanged with its original sole sorry. No completed submission is ready.

=== Soft weighted-cylinder Laplace lower bound (VERIFIED, NO SETTLEMENT) ===

New file: SoftCylinderLaplace.lean, namespace Erdos970.GapAverages.
Compiled individually; all six printed final theorem audits contain only
propext, Classical.choice, Quot.sound. Log: /tmp/soft_cylinder_laplace.log.

For a fixed population S covered by a residue vector r, changing coordinates
from r to s leaves at most sum_p 1[s_p != r_p] B_p survivors, whenever B_p caps
the ACTUAL old row population classHits(S,p,r_p). Averaging its exponential
and using independence of residue COORDINATES gives the new unconditional
finite bound
  E_s exp(-t * survivors(S,P,s)) >=
    product_p (1+(p-1)*exp(-t*B_p))/p,    t>=0.
No independence between the row populations is assumed.

Verified main results:
- softCylinderWeight_le_population_laplace;
- softCylinderWeight_le_countLaplace_of_cover, using raw caps m/p+1;
- exp_softCost_le_softCylinderWeight, with
    softCost = sum_p min(log p, t*B_p);
- softCylinderWeight_le_two_pow_exp_softCost, the reverse comparison up to
    2^card(P). This compares finite envelopes, not all possible methods;
- survivor_of_softCylinderLaplace, CONDITIONAL on a strict Laplace upper
    bound below this new product weight;
- core_softCylinderWeight_le_countLaplace: retaining one core phase Q and
    varying a disjoint tail R gives the core mass product(1/q) times the
    soft tail weight. Its caps are for the ACTUAL core-filtered population.

Follow-up review did NOT supply the required upper estimate. The existing
quadratic low-count theorem has exponent k^(4/5) at a small fixed multiple
of m/log k. The log-critical void theorem controls zero counts only, not
this positive-parameter Laplace transform. These statements must not be
interchanged. The soft product legitimately retains the cost of every
coordinate, through the finite factor above; it does not remove entropy
for free and does not settle erdos_970.

Spec.lean remains unchanged with its original sole sorry. No proof or
disproof of the original conjecture is ready, and no submission was made.

Soft-cylinder follow-up (verified clarification):
- Also proved countLaplace_le_lowCountFraction_add_exp in the same file:
    L_P(t,m) <= Pr(N<=b) + exp(-t*b), t>=0.
  The final file compiles and all SEVEN printed audits are clean.
- The older BuchstabLowTail.lean theorem
  eventually_refined_quadratic_low_tail is stronger than the 4/5 result:
  it gives exponent19/20 with a different fixed (small) count threshold.
  This is an EXISTING verified result (see the earlier log entry), not a
  new advance from this continuation. The review above must not be read
  as asserting that4/5 was the strongest already available exponent.
- Neither exponent, with its actual count threshold and fully charged
  retained-core/tail costs, was combined into a quadratic survivor proof.
  No successful Laplace upper/lower comparison is claimed.

=== Cardinality cost of prime thinning (VERIFIED, NO SETTLEMENT) ===

New file: PrimeDilutionBudgetNecessary.lean.
Namespace: Erdos970.PrimeDilution.
It compiles without warnings; all four final printed audits contain only
propext, Classical.choice, Quot.sound.
Log: /tmp/prime_dilution_budget_necessary.log.

The proposed use of log-critical void bounds through bounded-budget prime
padding does not close the new soft-cylinder route. Verified finite bounds:

1. neg_log_product_le_card:
   For B>=2 and every modulus p in R at least B,
     -log(product_{p in R}(1-1/p)) <= |R|/(B-1).
   The result does not even require primality.

2. log_target_le_card_of_dilution:
   Thinning to density <=1-exp(-t) therefore necessarily costs
     -log(1-exp(-t)) <= |R|/(B-1).
   For small t this is a logarithmic cost in1/t, not a cost of order t.

3. exp_neg_two_le_product_of_card_le:
   If |R|<=B as well, the remaining density is at least exp(-2).

4. no_small_parameter_bounded_padding:
   If t<exp(-2), there is NO such R with |R|<=B whose density is <=1-exp(-t).
   In particular, primes all at least the interval length cannot model
   arbitrarily small Laplace parameters while keeping their cardinality
   within that length budget.

Scope: this refutes only that bounded-cardinality large-modulus padding
proposal. It is not a counterexample to the original conjecture, and does
not rule out a different direct Laplace upper bound or other padding schemes.
The existing unbounded-cardinality thinning limit remains valid.

Spec.lean remains unchanged, including its sole original sorry. No completed
proof or exact-negation disproof is ready; no submission was made.

=== Explicit varying-parameter Laplace upper bound (VERIFIED, NO SETTLEMENT) ===

New file: RefinedQuadraticLaplace.lean.
Namespace: Erdos970.SoftExposure.
Compiled without warnings; all three printed final theorem audits contain
only propext, Classical.choice, Quot.sound.
Log: /tmp/refined_quadratic_laplace.log.

Let M=refinedQuadraticScale and L=refinedLowCountLogConstant, the EXISTING
constants from BuchstabLowTail. Define
  b_k = M*k^2/(L*log(k+2)),
  a_k = k^(19/20)/64,
  t_k = a_k/b_k.

Verified:
- t_k>0 for k>0;
- t_k = [L/(64*M)] * log(k+2)/k^(21/20);
- refinedLaplaceParameter_tendsto_zero;
- eventually_refined_quadratic_laplace:
    uniformly over prime sets P with |P|<=k, eventually
      countLaplace P t_k (M*k^2) <= 2*exp(-a_k).
  This follows from the actual positive low-count estimate, NOT from the
  zero-count bound or unbounded-cardinality prime padding. Both terms in
  L(t)<=Pr(N<=b)+exp(-t*b) are retained.
- eventually_survivor_of_refined_soft_weight combines this with the new
  soft-cylinder lower bound, CONDITIONAL on
    2*exp(-a_k) < softCylinderWeight(P, m/p+1, t_k).
  This product comparison is NOT proved uniformly over |P|<=k.

The t_k limit is explicitly checked, so this theorem must not be advertised
as a fixed-positive-parameter Laplace estimate. No successful uniform
upper/lower comparison or quadratic Jacobsthal bound was obtained.

Spec.lean remains unchanged with its sole original sorry. No completed
proof or negation theorem has been submitted.

=== Final soft-weight comparison review (NO NEW SETTLEMENT) ===

Reviewed the remaining comparison on initial prime segments. The verified
soft-coordinate upper comparison already shows saturation near 1/p when
t*B_p is large relative to log p. Thus the varying-parameter upper bound
2*exp(-k^(19/20)/64) cannot simply be declared smaller than the soft product.
An on-paper prime-prefix diagnostic suggests an obstruction to the raw-cap
comparison, but no asymptotic Lean disproof of that comparison was completed.
Do not report that diagnostic as a verified theorem or as a disproof of970.

No original-target proof was obtained. The only new verified additions in
these final continuations are SoftCylinderLaplace.lean,
PrimeDilutionBudgetNecessary.lean, and RefinedQuadraticLaplace.lean, with
the exact scope and remaining hypotheses recorded above. Spec.lean is
unchanged, with its original import, statement, and sole sorry at2177.
