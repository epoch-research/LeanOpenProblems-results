## Upper multiplicity bounds give upper, not lower, overlap frequencies

Completed `Submission/UpperPowerOverlap.lean` and its exact-type/axiom
check file. Both compile cleanly; all three audited declarations use only
propext, Classical.choice, and Quot.sound. The three declarations prove:

* If g(n)<=n^alpha eventually, alpha>0, eta<2, and epsilon>0,
  every sufficiently large totient fiber has at most
  n^((2-eta)*alpha+epsilon) ordered pairs whose gcd has totient >=n^eta.
* This applies to any finite subfamily, without squarefreeness.
* For a subfamily F with |F|>=n^(alpha-delta), the bound becomes
  n^(alpha*eta-2*delta-epsilon)*|largePairs(F)| <= |F|^2.

The proof uses the existing lcm amplification with all divisor losses
retained. The global upper bound remains an explicit hypothesis. It does
not provide the LOWER overlap frequency needed to improve an exponent,
and it does not prove or disprove Erdős 821.

Build/audit logs: `/tmp/UpperPowerOverlap.log` and
`/tmp/UpperPowerOverlapCheck.log`. Spec.lean is unchanged, with its original
sorry and SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete settlement or new submission has been made.

---

## Follow-up: rough pools still need a new large-conductor estimate

Rechecked TypeIIBounds and NearFullStructuredCriterion after identifying the
modulus-three mode. Choosing pools of products of growing primes excludes
that particular small-modulus example, but no improvement of the remaining
Q^2 large-sieve term was obtained. The existing structured lower bound has
2*r+1<=t; at the needed r=t-2 this permits only t<=3, not unbounded orders.
This is a limitation of the available estimate, not a disproof of Erdős 821.

No new Lean source theorem was added in this follow-up. The conjecture
remains UNSOLVED, Spec.lean is unchanged with its original sorry, and no new
submission or build was attempted. No proof repair is pending.

---

## Surviving modulus-three mode in the principal-unit baseline

Added `ProgressionLocalMode.lean` and `ProgressionLocalModeCheck.lean`.
Both compile cleanly. All eight audited declarations use only propext,
Classical.choice, and Quot.sound. Logs: /tmp/ProgressionLocalMode.log and
/tmp/ProgressionLocalModeCheck.log.

For P={3}, let A_L={3*i+4 : i<L}, N=(3*L+1)^2. The file proves:

* |A_L|=L and its elements lie between 4 and 3*L+1;
* the actual centered successor kernel equals 1/2 on A_L x A_L;
* every row correlation on this rectangle is L/4;
* the exact Gram energy is L^4/16;
* nevertheless outputDivisorError(w_P-v_P,Q,N)<=7*Q/2 for every Q,N.

So unconditional Type I control does not imply a uniform small Gram bound
for arbitrary pools and arbitrary rectangles. This is only a surviving
small-modulus mode, not a disproof of Erdős 821 and not a counterexample to
an estimate restricted to suitable rough, growing modulus pools. Those
pools can exclude modulus 3; their large-conductor Gram estimate is still
unproved. No new smooth-prime supply or multiplicity exponent is claimed.

The original conjecture remains UNSOLVED. Spec.lean is unchanged with its
sorry and SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No new submission was made; no source repair or build is pending.

---

## New unconditional Type I bridge and concrete progression baseline

Completed and compiled:

* `SuccessorTypeIDivisibility.lean` (272 lines) and its check file;
* `SuccessorProgressionBaseline.lean` (366 lines) and its check file.

All 48 audited declarations have only propext, Classical.choice, and
Quot.sound. Both exact-type check files exit with code zero. Logs:
`/tmp/SuccessorTypeIDivisibility{,Check}.log` and
`/tmp/SuccessorProgressionBaseline{,Check}.log`.

The Type I bridge uses the ACTUAL output discrepancy W=w-v:

    Delta_d = max_{T<=N} |sum_{n<=T,d|n} W(n)|.

For U>=1 and |W(n)|<=B on [1,N], it proves

    successorTypeIError <= U*B*log N + 3*log N*sum_{d<=U*V} Delta_d.

It also gives the exact rectangle-prefix identity retaining both the output
cutoff and d | p*a*b+1, and a conditional prime criterion combining this
Type I bound with the previously developed Type II Gram hypothesis.

The concrete baseline is now unconditional. For each positive m, the
residue-one weight 1_{n=1 mod m} is compared with
1_{gcd(n,m)=1}/phi(m). Periodic counting gives, for every d>0 and prefix T,

    |sum_{n<=T,d|n}(residue weight - principal weight)|
      <= 1 + 3^omega(m)/phi(m).

Both weights are then set to zero at n=1 and summed over a finite pool P.
The added prefix cost is at most one per modulus. An absolute constant C
bounds the total cost by C*|P|, uniformly in the moduli. Consequently

    successorTypeIError(w_P,v_P;N,U,V)
      <= U*|P|*log N + 3*C*U*V*|P|*log N.

Other unconditional results:

* The principal weighted Mangoldt sum is exactly
  sum_{m in P}(psi(N)-nonunitMangoldt(m,N))/phi(m).
* If 0<m<=N throughout P, it is at least
  (psi(N)-log_2(N)*log N)*sum_{m in P}1/phi(m).
* w_P(1)=0, w_P is nonnegative, and w_P(n)<=tau(n-1) for n>=1.
* If each m in P is Y-smooth and N<=m*Y, every detected prime n<=N has
  Y-smooth predecessor n-1.

Main declarations are in Erdos821.AnalyticSieve.SuccessorVaughan:

    successorTypeIError_le_bounded_divisor_error
    prime_output_card_gt_of_divisibility_gram
    progression_divisible_prefix_error
    progression_pool_divisor_error
    exists_uniform_progression_pool_TypeI_bound
    progression_principal_mangoldt_lower
    successorProgressionWeight_le_divisors
    progression_prime_output_smooth

The necessary Type II Gram estimate is STILL UNPROVED. No all-root prime
supply and no new unconditional inverse-totient exponent are claimed.
The strongest exponent remains the ten-thousand-band strict gain.
Spec.lean is unchanged with its original sorry and SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
The original task remains UNSOLVED. No new submission was made, and no
source repair or build is pending.

---

## New successor Type II Gram/four-corner reduction

Added `Submission/SuccessorTypeIIGram.lean` (roughly 380 lines) and
`Submission/SuccessorTypeIIGramCheck.lean`. Both compile; all fifteen audited
results use only propext, Classical.choice, and Quot.sound. Logs:
`/tmp/SuccessorTypeIIGram.log` and `/tmp/SuccessorTypeIIGramCheck.log`.

The new unconditional finite results include:

* A fourth-power bilinear bound from two Cauchy--Schwarz steps:
  S^4 <= (sum a^2)^2 (sum b^2)^2 sum_{r,t}(sum_s K(r,s)K(t,s))^2.
* Separation of the Gram diagonal, using only a pointwise kernel bound,
  from an explicit off-diagonal row-correlation hypothesis.
* The exact four-corner expansion of the Gram energy.
* Exact dyadic assembly for the OUTPUT-weighted Vaughan Type II term.
* A full Type II fourth-power bound using the previously proved coefficient
  energies, with the actual centered successor kernel and cutoff retained.
* A conditional prime-output lower bound from a Gram bound and the explicit
  Type I/main-term comparison, including prime-power and collision costs.
* Smoothness of positive rectangle-output predecessors when every input
  factor is smooth.

Main declarations, in Erdos821.AnalyticSieve.SuccessorVaughan:

    kernelBilinear_fourth_le
    kernelGramEnergy_le_of_correlations
    successor_typeII_block_fourth_le
    kernelGramEnergy_four_corners
    successor_typeII_dyadic
    successor_typeII_fourth_le_gram_sum
    successor_typeII_abs_le_of_gram
    prime_output_card_gt_of_gram
    rectangle_positive_output_smooth

The new prime criterion retains unproved arithmetic hypotheses. The needed
centered row correlations have not been bounded sufficiently. For rectangle
weights their uncentered part contains the COUPLED equations
p*a*b+1=r*s and p'*a'*b'+1=t*s. The existing single-congruence cofactor means
have not been shown to control them. No new unconditional prime supply or
multiplicity exponent is claimed.

The exact conjecture remains UNSOLVED. Spec.lean is unchanged with its
original sorry and SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No new submission was made. There is no pending source repair or build.

---

## Completed ten-thousand-band certificate and strict fixed-exponent gain

The five `TenThousandPool...lean` development files and
`TenThousandPoolStrictGainCheck.lean` now compile successfully. The original
monolithic 10,000-entry decision procedure exceeded the memory limit.
The repair proves all band parameter inequalities algebraically, and checks
the exact budget sum in 100 blocks of 100 terms. The repaired Bands file
also compiles with the default Lean thread stack. No native_decide is used.

Exact certificate:

    sum of band numerators = 9993236399,
    denominator = 10000000000,
    tail = 11/62500,
    total = 0.9994996399 < 1999/2000.

The strongest new theorem is:

    Erdos821.exists_ten_thousand_pool_strict_gain :
      ∃ K : ℕ, 2 ≤ K ∧ ∀ γ : ℝ,
        γ < 2441371/4000002 + 1/(40000020*(K : ℝ)) →
        {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite

Consequently the exact endpoint 2441371/4000002 (approximately
0.6103424448287775) is attained, and a strictly larger exponent exists.
`erdos_821_ten_thousand_pool_closed_range` proves the conjectured conclusion
for every epsilon >= 1558631/4000002. The rational threshold exceeds even
the largest margin allowed by the preceding thousand-band statement:

    406887/666667 + 1/80000040 < 2441371/4000002.

The expanded-type checks expose the original totient-fiber ncard, and
all audited declarations depend only on propext, Classical.choice, and
Quot.sound. Logs: /tmp/TenThousandPool{Bands,RoughBound,SmoothDensity,
Multiplicity,StrictGain,StrictGainCheck}.log and
/tmp/TenThousandPoolBands.default.log. All corresponding exit codes are zero.

This is still only a FIXED exponent, not a settlement of the original
conjecture. The all-higher-root smooth-predecessor series divergence remains
unproved. Spec.lean is unchanged, retains its original sorry, and has SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No new submission was made. There is no pending build or source repair.

---

## New finite successor-Vaughan reduction, with output weights retained

Added `SuccessorVaughanReduction.lean` and its exact-type/axiom check file.
Both compile. The new declarations use only propext, Classical.choice,
and Quot.sound.

The file proves:

* Vaughan's identity summed against any real-valued output weight;
* a discrepancy bound retaining the short term, both Type I terms, and
  the actual output-weighted Type II term;
* removal of nonprime prime powers with error 2*B*sqrt(X)*log(X), where
  B bounds the weight per output;
* a finite conditional lower bound for distinct prime-output cardinality;
* exact reindexing for rectangle successors p*a*b+1;
* a collision bound by the square of the divisor count of n-1.

In particular the Type II term retains the equation r*s=p*a*b+1 and both
Vaughan coefficients. The existing input-character and divisibility means
have NOT been shown to estimate this output-factorization correlation.
The required strict lower bound remains an explicit hypothesis. No new
unconditional smooth-prime supply or multiplicity exponent is claimed.

The exact conjecture remains UNSOLVED. Spec.lean is unchanged with its sorry,
and no submission was made.

---

## New finite certificate: half-level moments with factor-two domination

Added and kernel-checked `DominatedHalfPartitionModel.lean` and its check file.
An exact law on 48 partitions of 12, with total integer mass 13305600, has:

* all single-part means 1/j;
* all joint binomial moments of selected total size at most 6;
* pointwise mass at most twice the permutation reference mass;
* zero fourth-root-smooth mass.

The theorem `all_nonnegative_tests_bounded` proves the factor-two upper bound
for EVERY nonnegative rational-valued statistic on the displayed finite
reference space, not just a solver-selected list. All declarations passed
axiom audits; only permitted axioms occur. No solver computation is trusted
by the Lean proofs.

This is a finite obstruction to a proposed moment-inference argument. It is
NOT an asymptotic model of primes and NOT a disproof of Erdős 821. It does not
claim that every conditional arithmetic cofactor bound has been represented
by these finite inequalities. The original conjecture remains UNSOLVED;
Spec.lean is unchanged and still contains its sorry. No submission was made.

---

## Follow-up: bounded rectangle iteration review and submission status

The exact conjecture remains UNSOLVED. The original Spec.lean is unchanged
and still contains its sorry. One earlier submission of that incomplete
file was rejected by verification; it was not a valid settlement. No new
submission has been made in this review.

Rechecked BoundedPrimeRectangleSupply, CofinalBoundedRectangleSupply,
RestrictedCofactorWeights, RestrictedCofactorCompletion, and the periodic
cofactor means. The rectangle supply retains two unrestricted cofactor
intervals. Its displayed smoothness exponent is

    (7*k+7)/(14*k+16) = 1/2 - 1/(14*k+16),

not a root order tending to zero. Reapplying the same theorem does not
replace those intervals by smooth cofactor sets. The restricted-weight
means retain the actual restricted input mass and are not prime-output
lower bounds with both cofactors restricted. No new arithmetic lower
bound or exponent amplification was obtained. No Lean source was changed
and no proof repair is pending.

---

## Follow-up: parity-breaking correlation review

No new Lean theorem was obtained and the original conjecture remains
UNSOLVED. Considered whether bounded multiplicative-function correlations
could supply the missing smooth-predecessor prime lower bound. No such
prime-weighted or bilinear estimate was proved or found as an available
arithmetic input. A qualitative error on the full integer scale cannot be
assumed smaller than a prime-count main term.

A further sign check matters: after excluding all prime divisors at most
sqrt(X), the surviving integers in [2,X] are primes, so the arithmetic
Liouville function is negative throughout that set. Cancellation on that
fully sieved set is not itself the positive prime lower bound sought here.
No external correlation theorem or uniform rate is being claimed as proved.

No Lean source changed. Spec.lean retains its original sorry; the earlier
partial results and audits are intact. There is no complete proof/disproof
or pending auxiliary proof repair.

---

## Follow-up: growing-depth iteration does not give a one-step transfer

No new Lean theorem was obtained. Rechecked IteratedTotientFibers,
IteratedPowerfulTotient, and IteratedRadicalLift for a possible conversion
of growing-depth fibers to one-step fibers. The exact recurrence sums over
intermediate outputs; it is not an exponent-preserving encoding. The
available eventual size and multiplicity estimates fix the depth before
the output tends to infinity, so no uniform assertion at moving depth may
be substituted. Padding all input prime exponents above the depth makes
the iterate injective on that restricted class and therefore does not
supply branching. No suitably low-loss alternative encoding was proved.

Spec.lean remains unchanged with its original sorry. The strongest partial
multiplicity exponent and the latest closed-output specialization are
unchanged. There is no pending Lean repair or complete settlement to submit.

---

## Follow-up: direct averaged-function input and reference check

The original conjecture remains UNSOLVED. Investigated whether a lower
average for the smooth-number indicator on shifted primes could bypass the
missing progression estimate. No prime-weighted lower bound was obtained;
a count of smooth integers or an Euler-product identity is not such a bound.
The endpoint smooth-series equivalence and the one-sided distribution
criterion remain valid targets, with their arithmetic inputs unproved.

The external problem page is still unreachable: curl failed with DNS error
6 for www.erdosproblems.com. The /opt documentation contains Pantograph
manuals, not an additional mathematical reference. The targeted Mathlib
search found smooth-number and Euler-product tools but no theorem supplying
the needed all-root shifted-prime estimate. This is not a claim about the
current external research status, which could not be checked here.

No Lean source was changed in this continuation. Spec.lean retains its
original sorry. The latest closed-output result and its permitted-axiom
audit remain intact; there is no pending proof repair or valid settlement
to submit.

---

## Follow-up: distinguishing closed outputs from intermediate values

No new Lean theorem was added in this continuation; the original conjecture
remains UNSOLVED. Rechecked whether ThousandPoolClosedFibers closes the
iterated-fiber or sparse-modulus routes.

SmallRadicalMiddleFibers already proves that, within one fixed totient
fiber, at most R intermediate values can have radical at most R. The new
closed-output supply concerns the radical of the output n, not radicals
of the many m with phi(m)=n. It therefore does not supply polynomially
many inexpensive intermediate values for an iterated-fiber collapse.

FiberModulusAudit already gives the exact sparse-family main term and
cofactor accounting. From Q^alpha moduli near Q and a prime cutoff Q^beta,
the ideal incidence count exponent is (alpha+beta-1)/beta, not one. After
charging the uncontrolled cofactor cutoff (beta-1)/beta, the resulting
exponent is alpha/beta < alpha for beta>1. This remains a loss even if an
ideal sparse-modulus prime lower bound were available. An additional
cofactor smoothness input is required. No improved sparse-family error
estimate or controlled-cofactor lower count was obtained.

The new closed-output specialization from the preceding continuation stays
compiled and audited. Spec.lean is unchanged with its original sorry and
SHA-256 8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
There is no completed proof/disproof to submit or pending source repair.

---

## Latest positive continuation: strict thousand-band gain at closed outputs

The original conjecture remains UNSOLVED. Spec.lean is unchanged with its
original sorry. No complete proof/disproof has been submitted.

### Completed result and audit

- Submission/ThousandPoolClosedFibers.lean (107 lines)
- Submission/ThousandPoolClosedFibersCheck.lean (30 lines)

The result and independent expanded-type audit compile cleanly. All four
new declarations depend only on propext, Classical.choice, and Quot.sound.
Logs: /tmp/ThousandPoolClosedFibers.log and
/tmp/ThousandPoolClosedFibersCheck.log. The result olean is fresh.

Namespace: Erdos821.ClosedPadding.

`closed_fibers_of_single_log_smooth_count` specializes the ALREADY PROVED
general closed-output transfer in UniformClosedFibers.lean to the one-log
prime count. The general transfer itself is not new and already preserves
any exponent strictly below 1-b/t.

`exists_thousand_pool_closed_strict_gain` supplies one K>=2 such that, for
every gamma>=0 below

    406887/666667 + 1/(40000020*K),

and every pair of natural parameters r,N, there is n>N with

    n^gamma < g(n),
    rad(n)^r <= n,
    phi(rad(n)) divides n.

K is fixed before gamma, r, and N. The root order r controls the radical of
the OUTPUT n, NOT root-smoothness of shifted primes.

`infinite_thousand_pool_closed_endpoint r` attains the exact rational
exponent 406887/666667 with both output conditions, for each fixed r.
`exists_closed_exponent_above_thousand_pool` supplies one exponent strictly
above that rational value, valid for every fixed r. The audit expands g as
an actual totient-fiber ncard and rad(n) as the product of n.primeFactors.

### Scope and remaining overlap gap

This improves the explicit structural specialization from the older
wide-block exponent to the strongest currently proved range. It does NOT
improve the multiplicity exponent itself and does not give exponents tending
to one. Small output radical and closure do not assert a power-sized common
factor among preimages: preimages may contain large primes absent from the
output's support. The LCM amplification criterion still needs an actual
lower count for large-gcd-totient pairs satisfying the strict surplus
ell < alpha*eta. No such lower count was obtained.

Spec.lean retains SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
There is no pending source repair or unfinished auxiliary proof.

---

## Latest continuation: prime-power support and hyperbola checks

The original conjecture remains UNSOLVED. No Lean source theorem was added
or changed in this continuation, and no complete proof/disproof is ready.

Rechecked the proposed full-input amplification against the exact existing
results `eq_of_totient_eq_of_primeFactors_eq` and
`g_eq_card_admissibleSupports` in Work.lean. For a fixed target totient,
a prime support determines its preimage uniquely. Prime powers therefore
supply no independent choices at that fixed support. This is not a general
impossibility result for future amplification arguments.

Rechecked divisor-complement symmetry against SymmetricDivisorHyperbola.lean
and CofactorMomentSwitching.lean. The square-root hyperbola gains the factor
k+1, not an exponentially growing factor that removes the high-order
geometric loss. The balanced identity retains divisor weights on both
sides. Expanding the complementary weight produces product moduli up to X;
it does not keep all moduli below the known distribution level. No estimate
for that missing prime-weighted correlation was obtained.

These checks reconfirm earlier limitations, rather than provide new
arithmetic input or a new multiplicity exponent. The strongest verified
multiplicity result remains exists_thousand_pool_strict_gain. Spec.lean
still has its original sorry and SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
There is no pending build or unfinished auxiliary proof.

---

## Latest positive continuation: actual prime supply for the same bounded input

The original conjecture remains UNSOLVED. `Spec.lean` is unchanged with
its original `sorry`; no proof or disproof has been submitted. The strongest
multiplicity conclusion remains `exists_thousand_pool_strict_gain`.

### Completed modules and audit

- `BoundedPrimeRectangleSupply.lean`
- `CofinalBoundedRectangleSupply.lean`
- `BoundedPrimeRectangleSupplyCheck.lean`

Both result modules and the independent expanded-type audit compile
cleanly with no warnings. All 11 new declarations were axiom-audited;
only `propext`, `Classical.choice`, and `Quot.sound` occur. Logs:
`/tmp/BoundedPrimeRectangleSupply.log`,
`/tmp/CofinalBoundedRectangleSupply.log`,
`/tmp/BoundedPrimeRectangleSupplyCheck.log`.

### Actual prime lower bound, not an inference from congruence means

`rectanglePrimeOutputs p L` is the finite set of DISTINCT prime values
of a*b*p+1, for 1<=a,b<=L.

The previously proved below-half structured AP count is used as a
SEPARATE arithmetic input. A structured prime R has a divisor d of R-1
which is a product of prescribed block primes. Choose one block prime p,
put a=d/p and b=(R-1)/d, and bound both cofactors. Pigeonholing among the
bounded block primes gives one COMMON input p with many distinct outputs.

`eventually_exists_prime_rectangle_supply r` proves, eventually in m,
that some p in geometricBlockPrimes(m) has more than

    progressionScaleN((2*r)*m)

prime rectangle outputs, with cofactor cutoff
progressionScaleN((r+2)*m). The structured AP order is r+1 and its prime
cutoff exponent is 2*r+3; the below-half hypothesis is satisfied exactly.

### Same input, prime supply, and the beyond-half mean

At M=64*m and k>=5, `eventually_bounded_prime_supply_and_mean` gives one p
with 2^M<p<=2^(2M), for which all of the following hold:

- More than 2^((14*k+10)*M) distinct prime outputs with a,b<=L;
- Every output R is <=A+1 and R-1 is (L+1)-smooth;
- A+1<Q^2;
- Every prescribed fixed logarithmic saving in the squarefree-modulus
  successor-divisibility mean, for q<=Q.

Here L, Q, A are the previously defined parametric scales. The mean is
uniform over p, so it applies to the input selected by the AP pigeonhole.
Only scales M=64*m are used in this package; no quantifier exchange to
arbitrary moving parameters is made.

### Cofinal count and distribution exponents

`exists_prime_rectangle_supply_above_levels` proves:

For every theta<4/7 and beta<1, there is a FIXED k>=5 such that for every
fixed natural log-power d and eta>0, eventually in m there is a bounded
prime input p having more than A^beta DISTINCT prime outputs, with
A^theta<Q and the mean error times (1+log A)^d at most eta*L^2.
All output support, predecessor smoothness, and A+1<Q^2 are retained.

The audit expands the actual finite image of (a,b) -> a*b*p+1, filters
by `Nat.Prime`, and expands L,Q,A into powers of two. It is not just an
audit of an abstract prime-supply predicate.

### Remaining gap (now more precise)

There IS now an actual prime-successor lower bound for the unrestricted
two-cofactor rectangle and a common bounded input. It was obtained from
below-half prime AP information, NOT by converting a congruence mean into
a prime-detecting lower sieve. It does not provide all-root smoothness.

The smoothness cutoff L+1 has ambient exponent approaching 1/2 as k grows.
The parameter k is scale separation, NOT a smooth-root order. Increasing
k gives count exponents tending to one, but does not make this smoothness
exponent tend to zero. Thus the new result does NOT improve the existing
0.61033... multiplicity exponent and does NOT establish Erdős 821.
Restricting the free cofactors enough for all-root smoothness still needs
a new arithmetic lower bound. The older CRT avoidance theorem concerns
arbitrarily LARGE input primes and is compatible with this bounded-input
existential lower bound.

---

## Latest positive continuation: parametric full-ambient levels below 4/7

The original conjecture remains UNSOLVED. `Spec.lean` is unchanged with
its original `sorry`. No proof/disproof submission has been made. The
strongest multiplicity theorem remains `exists_thousand_pool_strict_gain`.

### Completed modules and audit

- `ParametricRectangleKernel.lean`
- `ParametricSmallPrimeMean.lean`
- `ParametricSmallPrimeMeanCheck.lean`

Both result modules and the expanded-type audit compile cleanly with no
warnings. All 21 new declarations have been axiom-audited, and only
`propext`, `Classical.choice`, and `Quot.sound` occur. Logs:
`/tmp/ParametricRectangleKernel.log`, `/tmp/ParametricSmallPrimeMean.log`,
`/tmp/ParametricSmallPrimeMeanCheck.log`.

### New scales and finite rate

For each fixed k>=5, set

    L = 2^((7*k+7)*m), Q = 2^((8*k+4)*m), A = 2^((14*k+16)*m).

For input primes 2^m<p<=2^(2m), every rectangle product a*b*p with
a,b<=L is <=A. Exactly Q^(14*k+16)=A^(8*k+4), and A+1<Q^2 for m>=1.
The real-power equality Q=A^((8*k+4)/(14*k+16)) is also proved.

The mean over any family of squarefree q<=Q has finite error

    <= C_k*(m+1)^2/2^m * L^2 * restrictedMass(f,X)

uniformly over all nonnegative weights on primes >=2^m, with no lower
mass assumption and no restriction on their upper input cutoff X. This
finite rate is proved for k>=3; the full-ambient above-half assertion
uses k>=5. The local main term remains phi(q)/q^2.

Exports in `Erdos821.AnalyticSieve`:

- `exists_parametric_small_prime_rate`
- `eventually_parametric_small_prime_poly_rate`
- `eventually_parametric_successor_log_rate`
- `eventually_parametric_bounded_input_mean`
- `exists_bounded_input_mean_above_level`

The last theorem proves, for every theta<4/7, the existence of one fixed
k>=5 whose level exceeds theta and which works for EVERY fixed log-power
d and eta>0, at all sufficiently large scales. Its package includes a
prime input in the stated range, product support, exact scale identities,
A+1<Q^2, the actual strict inequality A^theta<Q, and

    (1+log A)^d * successor-divisibility mean error <= eta*L^2.

Quantifiers are not exchanged: k is fixed before d, eta, and the scales.
The audit checks the finite weighted statement and the full final theorem
with all three scales expanded into powers of two.

### Scope and remaining gap

This realizes the previously suggested parametric extension (with an
index shift). It improves the available full-ambient level from 36/65 to
any fixed value below 4/7, with logarithmic savings, but is still only a
congruence mean. Both unrestricted cofactor intervals remain. No lower
bound for prime successors or new all-root smooth-prime supply has been
proved, and no improvement of the multiplicity exponent is claimed.
The parameter k here controls scale separation; it is NOT the root order
in the smooth-shifted-prime criterion for the original conjecture.

---

## Latest dependency review: unit-slope and cofinal structured criteria

No new settlement or auxiliary theorem was obtained in this review.
`Spec.lean` is unchanged with the original `sorry`.

Checked the exact statements in `UnitSlopeLimit`, `UnitSlopeMultiplicity`,
`UnitSlopeWideDensity`, `NearFullStructuredCriterion`, and
`OneSidedDistributionCriterion` for a possible unused implication.

- “Unit slope” concerns the Mangoldt lower constant, not a multiplicity
  exponent tending to one. Its parameterized multiplicity limit is the
  fixed number 14587/27899.
- The proved `eventually_structuredWeightLower_below_half` needs
  2*r+1<=t. For the near-full criterion r=t-2 and t>=3, this forces t=3.
  It therefore does not supply cofinally many orders.
- The two-cofactor mean retains its own input weights and local density
  phi(q)/q^2; it is not a residue-one Mangoldt lower bound for the
  near-full structured modulus family. No such substitution was made.
- The one-sided cofinal deficit condition likewise remains unproved.

The earlier prime-chain and coloring review also produced no new
contradiction: growing avoiding paths have not been ruled out, and the
full higher-divisor coloring cost has not been overcome.

The strongest multiplicity result and quantitative mean rate remain the
ones documented below. No proof/disproof submission was made.

---

## Latest continuation: quantitative small-prime mean rate

The original conjecture remains UNSOLVED. `Spec.lean` is unchanged with
its original `sorry`; no proof or disproof has been submitted. Its SHA-256
remains `8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The strongest verified multiplicity conclusion is still
`exists_thousand_pool_strict_gain`.

### Completed modules and audit

- `SmallPrimeMeanRate.lean` (192 lines)
- `SmallPrimeMeanRateCheck.lean` (40 lines)

Both compile cleanly, with no warnings. All seven new declarations have
been independently axiom-audited, with only `propext`, `Classical.choice`,
and `Quot.sound`. The audit includes expanded finite-weight and actual
natural-number successor-divisibility statements. Logs:
`/tmp/SmallPrimeMeanRate.log`, `/tmp/SmallPrimeMeanRateCheck.log`.

### Exact improvement

There is C>0 such that, for EVERY scale m, every nonnegative weight on
primes >=2^m, and every squarefree modulus family bounded by Q=2^(72m),
the old two-cofactor mean error is at most

    C*(m+1)^2/2^m * L^2 * restrictedMass(f,X),  L=2^(64m).

No lower bound on the input mass or upper restriction on X is needed.
This follows from the finite squarefree Kloosterman kernel and reciprocal
nonunit correction, not from interchanging any eventual quantifiers.

Exports:

- `squarefree_rectangle_kernel_rate`
- `rectangle_prime_nonunit_rate`
- `exists_doubleCofactor_small_prime_rate`
- `eventually_doubleCofactor_small_prime_poly_rate`
- `smallPrimeAmbientScale_log_le`
- `eventually_small_prime_successor_log_rate`
- `eventually_exists_prime_successor_log_rate`

Every fixed power of (m+1) is absorbed by the exponential decay. In
particular, the full-ambient bounded-input construction, with
2^m<p<=2^(2m) and A=2^(130m), admits every fixed logarithmic saving:

    (1+log A)^d * mean error <= eta*L^2

at all sufficiently large scales, for any fixed natural d and eta>0.
The packaged theorem retains Bertrand nonvacuity, actual product support
<=A, Q^65=A^36, A+1<Q^2, and natural successor divisibility.

### Remaining gap

This strengthens the quantitative error but does NOT supply prime
successors or improve the multiplicity exponent. At Q=A^(36/65), sieving
to sqrt(A) gives the standard linear-sieve parameter s=72/65<2, where
the usual lower factor is zero. Arbitrary logarithmic savings do not
alter that parameter. This diagnoses the direct linear-sieve route;
it is not a no-go theorem for every possible method and not a disproof.
The unrestricted cofactor support also still needs to be addressed for
all-root smoothness. No new all-root prime lower bound was proved.

---

## Latest positive continuation: nonunit inputs and full-ambient beyond-half mean

The original conjecture remains UNSOLVED. `Spec.lean` is unchanged with
its original `sorry`; no proof or disproof has been submitted. The strongest
multiplicity result remains `exists_thousand_pool_strict_gain`.

### Completed modules and audit

- `SquarefreeCofactorNonunits.lean`
- `SquarefreePrimeInputMean.lean`
- `SmallPrimeAmbientMean.lean`
- Independent audit: `SmallPrimeAmbientMeanCheck.lean`

All three result builds and the audit compile cleanly, exit 0. All 31
new declarations were axiom-audited; only the three permitted axioms occur.
Logs: `/tmp/SquarefreeCofactorNonunits.log`,
`/tmp/SquarefreePrimeInputMean.log`, `/tmp/SmallPrimeAmbientMean.log`,
`/tmp/SmallPrimeAmbientMeanCheck.log`.

### Correct main term for arbitrary nonnegative input weights

`nonunit_doubleCofactorRow_zero` shows non-coprime input rows vanish.
The local main term is now

    B*C*phi(q)/q^2 * sum_{1<=n<=X, gcd(n,q)=1} f(n).

`doubleCofactor_squarefree_nonunit_mean` and
`eventually_doubleCofactor_squarefree_nonunit_relative` establish the finite
and scaled means with NO primality or coprimality restriction on f. The
error is bounded relative to its actual total mass, with no density lower
assumption.

### Prime input correction: no requirement p>Q

For prime-supported f, `squarefreeCofactor_prime_main_correction` bounds
the aggregate change to the old full-mass main term by

    B*C*H(Q)*sum_{1<=n<=X} f(n)/n.

`doubleCofactor_squarefree_prime_mean` gives the finite sum of this correction
and the existing Kloosterman mean error. If all input primes are >=2^m,
then reciprocal mass <= total mass / 2^m; H(2^(72m))/2^m tends to zero.
Thus `eventually_doubleCofactor_small_prime_relative` retains the full-mass
main term phi(q)/q^2 for arbitrary nonnegative prime weights above 2^m,
not only above Q=2^(72m). No domination by Lambda is needed.

### Actual beyond-half range relative to full product size

Take L=2^(64m), input primes 2^m<p<=2^(2m), and

    A = 2^(2m)*L^2 = 2^(130m),   Q = 2^(72m).

All positive rectangle products a*b*p are <=A. Exactly Q^65=A^36,
and A+1<Q^2 for m>=1. The cutoff therefore has exponent 36/65>1/2
relative to the FULL product ambient range, not merely the free-cofactor
product. Bertrand's postulate supplies a prime in this input interval at
every m>=1.

`eventually_small_prime_input_rectangle_mean` is uniform for every prime
p>=2^m. `eventually_exists_prime_ambient_rectangle_mean` packages the
bounded input, ambient size identities, and mean. The result
`eventually_small_prime_successor_divisibility_mean` states the mean using
the actual natural conditions q | (i+1)*(j+1)*p+1; its ZMod translation is
also proved. Expanded-type checks are included in the audit.

### Remaining gap

These are distribution estimates, NOT prime-successor lower bounds and
NOT an all-root smooth-prime supply. Both unrestricted cofactor intervals
remain. The older avoidance construction uses a prime input that can be
extremely large; its old ambient-level limitation under p>Q is not an
obstruction to this NEW small-input range. Nevertheless, no prime-successor
lower bound or improved totient multiplicity exponent was derived here.
In particular a level merely above one half cannot be silently converted
into a prime-detecting lower sieve.

---

## Latest continuation: exact normalized prime-local divisor factors

The original conjecture remains UNSOLVED. `Spec.lean` is unchanged with
its original `sorry`; no proof or disproof has been submitted. The strongest
multiplicity conclusion remains `exists_thousand_pool_strict_gain`.

New completed modules:

- `PrimeDivisorLocalFactors.lean`
- `PrimeDivisorLocalFactorsCheck.lean`

The result and independent expanded-type audit compile cleanly, exit 0.
All nine new declarations (two definitions and seven results) depend only
on permitted axioms. Logs: `/tmp/PrimeDivisorLocalFactors.log` and
`/tmp/PrimeDivisorLocalFactorsCheck.log`.

For prime p, define local valuation weights w_p(0)=(p-2)/(p-1),
w_p(e)=p^(-e) for e>0. The actual binomial generating series for the
higher divisor function tau is evaluated in Lean, yielding

 (1-1/p)^k * sum_e tau_(k+1)(p^e) w_p(e)
   = 1 + (1-(1-1/p)^k)/(p-1).

No global shifted-prime moment asymptotic is asserted by this identity.
The normalized factor lies between 1 and 1+8*k/p^2. Its product over ANY
finite prime set is at most the already proved subexponential eulerCost(k).
Consequently, for any family P(k) of finite prime sets, fixed d, and
0<=rho<1, k^d * product_(p in P(k)) factor(k,p) * rho^k tends to zero.

In particular, the explicit algebraic coefficient

 (k+1) * product_(p in P(k)) factor(k,p) * (1/2)^k

is eventually smaller than theta^k for every fixed theta>1/2. This rules
out recovering a near-one geometric coefficient solely by accumulating
these local factors. It is NOT an upper bound on the actual shifted-prime
moment and NOT a disproof of Erdős 821. The missing global arithmetic
lower bound remains unproved.

---

## Latest continuation: exact coloring amplification review

The original conjecture remains UNSOLVED. Spec.lean is unchanged.
No new theorem or arithmetic lower bound was obtained in this review.

Rechecked SquarefreeColoring, ExactColoringCost, ColoringPrimeProfile,
CoprimeRecordProducts, and ClosedSupportPadding. The exact finite coloring
extraction test requires

    |F| * r^k > C^r * n^s * tau_r(n).

The higher-divisor tuple cost cannot be discarded, including for growing
numbers of colors. The current fiber lower estimates and prime-factor
profile bounds do not discharge this strict surplus condition. No
exponent-increasing amplification was proved. Coprime products and closed
padding retain their previously documented exponent losses.

The strongest verified positive conclusion is still the strict gain in
ThousandPoolStrictGain: some K>=2 permits every exponent less than
406887/666667 + 1/(40000020*K). This is not a settlement.
No proof/disproof submission was made.

---

## Latest positive continuation: strict gain beyond the thousand-band endpoint

The exact conjecture remains UNSOLVED. `Spec.lean` is unchanged with its
original `sorry`; no proof or disproof has been submitted.

New completed and independently audited modules:

- `ThousandPoolStrictGain.lean`
- `ThousandPoolStrictGainCheck.lean`

Both compile cleanly, exit code 0. All four exported theorem axiom lists
are subsets of the permitted three. The audit checks expanded types using
actual Nat.totient fibers. Logs:
`/tmp/ThousandPoolStrictGain.log`, `/tmp/ThousandPoolStrictGainCheck.log`.

`exists_thousand_pool_strict_gain` proves unconditionally that some natural
K>=2 gives infinitude for EVERY real exponent

    gamma < 406887/666667 + 1/(40000020*K).

This combines the established thousand-band single-log smooth-prime supply
with the previously established density-sensitive one-step cutoff
refinement. The refinement's half-level requirements are satisfied by
(t,b)=(40000020,15586800). No new lower-bound hypothesis is introduced.
No explicit numerical upper bound on K is claimed.

Consequences:

- `infinite_g_gt_thousand_pool_endpoint`: the exact exponent 406887/666667
  is now attained, not merely every smaller exponent.
- `exists_exponent_above_thousand_pool`: some exponent STRICTLY ABOVE
  406887/666667 is attained.
- `erdos_821_thousand_pool_closed_range`: the original conclusion for
  epsilon >= 259780/666667, including equality.

This does NOT yield exponents tending to one. Repeated use of the current
absolute-loss refinement spends the available density; the existing
cutoff-potential bound still prevents a zero-limit cutoff from that rule
alone. No density-replenishing arithmetic lower bound was established.

---

## Latest continuation: prime-input tuple smoothness requirements

The exact conjecture remains UNSOLVED. `Spec.lean` is unchanged with its
original `sorry`; no proof or disproof has been submitted. The strongest
verified multiplicity threshold remains 406887/666667.

New completed modules:

- `PrimeTupleSmoothness.lean`
- `PrimeTupleSmoothnessCheck.lean`

The result and independent audit both compile cleanly (exit code 0).
All six audited declarations use only the permitted axioms. Logs:
`/tmp/PrimeTupleSmoothness.log` and `/tmp/PrimeTupleSmoothnessCheck.log`.

For prime q, if a*q is a k-th-root-smooth prime predecessor, k>=1,
then q^(k-1)<=a. Hence at k>=2, q<=a and the successor a*q+1<=a^2+1.
The set of such successors arising from any fixed finite multiplier
family is finite. More generally a<=q^j forces k<=j+1. If a sieve cutoff
Q<=q, then Q^k<a*q+1.

These are size restrictions on a proposed prime-tuple construction,
NOT a disproof of Erdős 821 or any prime-tuple conjecture. A bounded
multiplier tuple cannot supply the all-root smooth predecessors even
if its forms take prime values infinitely often. Growing multipliers
would require a new prime-successor lower bound; the reviewed retained-
pool discrepancy and upper-sieve estimates do not furnish that input.
No new smooth-shifted-prime supply was established in this continuation.

---

## New checkpoint: certified thousand-band bound (not a settlement)

The exact conjecture remains UNSOLVED. `Spec.lean` is unchanged with its
original `sorry`. No proof or disproof has been submitted.

The strongest verified multiplicity threshold is now

    406887/666667 = 0.6103301948349026...

The five new result modules are `CertifiedPoolBands`, `ThousandPoolBands`,
`ThousandPoolRoughBound`, `ThousandPoolSmoothDensity`, and
`ThousandPoolMultiplicity`. They compile with fresh oleans and clean logs.
The 1,000 rational band certificates have exact integer budget
9993098816/10^10. Adding the short-tail budget 11/62500 gives
0.9994858816 < 1999/2000. Parameter checks use kernel `decide`, not
`native_decide`.

`infinite_g_gt_thousand_pool_gain` proves the conclusion for every
exponent gamma < 406887/666667. `erdos_821_thousand_pool_range` proves
it for epsilon > 259780/666667. `ThousandPoolCheck.lean` audits all 24
new declarations and checks expanded types involving the actual
Nat.totient fibers. All audited axioms are permitted.

This is only a fixed-exponent improvement. The previously verified
band-budget barrier at these distribution levels still applies; finer
bands cannot reach exponent one.

The continuation audit was rerun after adding the audit-file module
docstring: exit code 0, no warnings, all 24 axiom lists permitted.
Log: `/tmp/ThousandPoolCheck.log`. Revisited the endpoint smooth-series,
power-smooth-spectrum, cofinal moment, and near-full structured criteria.
Their missing arithmetic hypotheses remain undischarged. This review
produced no additional arithmetic lower bound and no settlement.

---

## Latest continuation reviews: no new settlement or arithmetic lower bound

Spec.lean remains unchanged with its original sorry. No new Lean theorem
was produced by the recent series, prime-chain, finite-moment, and
retained-record-fiber reviews. No proof/disproof has been submitted.

- Rechecked PowerSmoothSpectrum and EndpointSmoothUpper. The endpoint
  criterion still requires unbounded root parameters; the existing fixed
  cutoff supply does not discharge it.
- Rechecked GrowingSmoothPrimeChains and SparseSmoothPrimeChains. The
  conditional growing-depth consequences remain compatible with the
  available chain bounds; no contradiction was obtained.
- Reverified HalfPartitionMomentModelCheck.lean successfully. Its exact
  finite certificate matches ALL half-level joint moments (endpoint
  included), all single-part means, and exact total size, with no
  fourth-root-smooth outcome. Current log:
  /tmp/HalfPartitionMomentModelCheck.current.log. Its axioms are permitted.
- Exploratory finite partition systems at sizes 12,18,24,30 were tested
  in /tmp/partition_moment_probe.py and /tmp/partition_projection.py.
  Some HiGHS runs reported UNKNOWN numerical status, NOT infeasibility.
  The later least-squares projections gave positive floating candidates
  excluding quarter-/fifth-/sixth-smooth outcomes at several sizes.
  These candidates are NOT exact certificates or Lean results. They do
  not resolve the asymptotic model problem, much less Erdős 821. All
  computations have ended; the long HiGHS run was stopped.
- Rechecked CoprimeRecordFibers, CoprimeRecordProducts,
  ClosedSupportPadding, and RecordInputScale. No exponent-increasing
  retained-fiber construction was obtained. The requisite prime-successor
  lower supply for large-fiber weights is also still missing. Products
  and padding preserve exponents after accounting for output size;
  pairwise coprimality and collision losses cannot be discarded.

The strongest verified multiplicity threshold remains 406667/666667.
No final-file edits, unfinished Lean repairs, or active builds resulted
from these reviews.

---

## Latest review: growing order does not rescue the existing log-log-loss bound

The exact conjecture remains UNSOLVED. Spec.lean is unchanged. No new
result module or proof/disproof was produced in this review.

An attempt to fetch the current erdosproblems.com/821 reference failed
with DNS resolution unavailable in this environment.

Rechecked LogLogMomentLower, LogLogMomentScales, NearMomentScales,
CofinalMomentCriterion, and the previous factorial-sensitive audits.
The potentially tempting inference was to choose the order k so large
that k! overcomes the loss (log log X)^(30*(k-1)). However the actual
finite construction has an order/scale constraint. Writing w=k-1,
A=2^m, E=1024*A^2, its condition R+1<=E implies

    4096*w*(A+20)*(2*m+10) <= 1024*A^2,
    hence 8*w*(m+5) <= A.

For m>=32 the existing proved scale estimate gives H=log log X>=32*A.
Consequently k<=H, and the normalized lower coefficient satisfies

    k! / H^(30*(k-1)) <= H^(-14*k)  (k>=2).

Thus the current lower bound does not reach theta^k along these valid
scales even by allowing k to grow. These last elementary comparisons
were checked mathematically in this review, NOT added as Lean lemmas.
They concern the strength of the proved lower estimate, not an upper
bound for the actual shifted-prime moment and not a disproof of Erdős 821.

No new smooth-shifted-prime supply was found. The verified multiplicity
threshold remains 406667/666667. No submission was made.

---

## Latest continuation: prime-successor avoidance despite the cofactor mean

**The exact conjecture remains UNSOLVED.** `Spec.lean` is unchanged with
its original `sorry`. The strongest established multiplicity exponent is
still 406667/666667. No proof or disproof has been submitted.

### Main-gap review

Rechecked the exact smooth-shifted series equivalence in `Work.lean`,
the smooth-core extraction results, and the cofinal high-order moment and
near-full structured progression criteria. None of their missing lower
hypotheses was discharged. In particular the squarefree-modulus cofactor
mean is not near-full distribution at the ambient successor size.

### New completed result modules

- `PrimeSuccessorAvoidance.lean` (118 lines)
- `CofactorMeanWithoutPrimeSuccessors.lean` (112 lines)

Both compile cleanly with fresh oleans. All 14 lemmas/theorems are
independently audited in `CofactorMeanWithoutPrimeSuccessorsCheck.lean`,
which also checks expanded arithmetic and infinitude types. The only
axioms are `propext`, `Classical.choice`, and `Quot.sound`. No new sorry,
admit, or axiom was introduced. Logs are `/tmp/<Module>.log` and
`/tmp/CofactorMeanWithoutPrimeSuccessorsCheck.log`.

Namespace: `Erdos821.SuccessorAvoidance`.

### Arbitrarily large prime inputs with blocked successors

For every finite family A of positive natural multipliers, every reduced
residue class b modulo a positive M, and every cutoff K, the new CRT
construction supplies a reduced class r modulo some D, refining b mod M,
such that each a in A has a prime q>K dividing D and a*r+1.

Dirichlet then supplies arbitrarily large primes p in that class, with
p>D. For every a in A the corresponding q is a proper divisor of a*p+1.
Consequently infinitely many primes in the prescribed original reduced
class have NO prime successor a*p+1 for any a in A.

Important names:

    negative_inverse_residue
    exists_successor_avoiding_class
    exists_prime_no_successors
    infinite_primes_no_successors
    exists_prime_no_rectangle_successors

The rectangle specialization blocks all a*b*p+1 with 1<=a<=B and
1<=b<=C. All explicit blocking prime factors can be chosen above any
prescribed K. This is a theorem about arbitrary prime inputs, not about
inputs already known to have arbitrarily smooth predecessors.

### Coexistence with the proved relative mean

`singletonPrimeWeight p hp` is an arithmetic-function point mass at the
prime p. It has nonnegative values, total mass one up to p, and its
cofactor weight equals the corresponding single input row.

`eventually_prime_input_rectangle_mean` derives the existing relative
mean uniformly for EVERY prime p>Q, for all families of squarefree q<=Q,
with arbitrary unit residues. Here L=2^(64m), Q=2^(72m), and the local
main term per row is L^2*phi(q)/q^2.

`eventually_rectangle_mean_and_no_prime_successors` combines this actual
mean with the CRT construction. For every eta>0, eventually m, there are
arbitrarily large primes p>Q for which BOTH hold:

- every a*b*p+1, 1<=a,b<=L, has a proper prime divisor q>Q;
- the squarefree-modulus cofactor mean error is at most eta*L^2,
  uniformly over every chosen family of squarefree moduli <=Q and all
  unit residues.

Thus a blanket prime-successor lower bound for arbitrary retained prime
weights does not follow from this mean. The prime input in the CRT
construction can be extremely large compared with L. This is not a
counterexample to a suitable distribution statement at a large level
relative to the actual successor size.

### Exact ambient-scale check

The same file proves

    Q^25 = (Q*L^2)^9,
    p>Q ==> Q^25 < (p*L^2)^9,
    p>Q ==> Q^2 < p*L^2.

Names:

    rectangle_ambient_scale_identity
    prime_input_ambient_scale_bound
    prime_input_cutoff_below_ambient_half

So in the prime-above-Q specialization the cutoff has exponent at most
9/25 relative to the full product size p*L^2, not 9/16. The 9/16 claim
continues to be only relative to L^2. The more general mean with merely
coprime inputs does not require p>Q; these scale inequalities are not a
universal limitation on all possible uses of that theorem.

### Remaining gap

No new smooth-shifted-prime supply or totient multiplicity exponent was
obtained. The new obstruction is to an auxiliary uniform bootstrap, NOT
a disproof of Erdős 821. Additional arithmetic information about the
specific retained weights and their scales is still needed.

Spec SHA-256 remains
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.

---

## Latest continuation: squarefree-modulus two-cofactor mean completed

**The exact conjecture remains UNSOLVED.** `Spec.lean` is unchanged with
its original `sorry`. The strongest established multiplicity exponent
remains 406667/666667. No proof/disproof has been submitted.

### Completed and independently audited

Seven result modules, 1055 lines and 59 lemmas/theorems:

- `KloostermanRingProducts.lean` (121 lines)
- `SquarefreeKloosterman.lean` (106 lines)
- `KloostermanRingCompletion.lean` (169 lines)
- `IntervalFourierGcd.lean` (199 lines)
- `SquarefreeRectangleCounts.lean` (209 lines)
- `SquarefreeCofactorMean.lean` (161 lines)
- `SquarefreeCofactorScales.lean` (90 lines)

All result oleans compile cleanly. The comprehensive independent
`SquarefreeCofactorScalesCheck.lean` compiles cleanly, audits all 59
lemmas/theorems, and checks expanded types for the complete sum, actual
rectangle count, and final relative mean. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. The intermediate check files
are `SquarefreeKloostermanCheck.lean` and
`SquarefreeRectangleCountsCheck.lean`. Logs are `/tmp/<Module>.log`
and `/tmp/<Module>Check.log`. No new `sorry`, `admit`, or axiom was added.

### CRT and complete sums

Namespace `Erdos821.Kloosterman`:

    ringKloosterman
    ringKloosterman_equiv
    primitive_transport
    coordinateChar
    primitive_coordinate
    character_pi_factorization
    ringKloosterman_pi
    ringKloosterman_pi_fourth
    squarefreeCRT
    squarefreeCRT_apply
    annihilatorPrimeProduct_dvd_gcd
    ringKloosterman_squarefree_fourth

The ring sum uses inversion in the unit group. For squarefree positive q,
any primitive additive character psi, and any frequencies a,b:

    |K_q(a,b)|^4 <= 3^omega(q)*q^3*gcd(b.val,q).

The gcd loss is retained. The proof transfers via CRT to prime fields;
coordinates where b vanishes use the trivial bound. A coarser convenient
norm estimate is

    |K_q(a,b)| <= squarefreeBound(q)*gcd(b.val,q),
    squarefreeBound(q) = sqrt(sqrt(3^omega(q)*q^3)).

### Completion including nonunit frequencies

`ringFourier`, `ringWeightedKloosterman`, `ringHyperbolaWeight`, and
`ringUnitMass` work over arbitrary finite commutative rings.
The error identity removes the zero frequency and sums over
`univ.erase 0`, NOT over the units. This includes the nonzero nonunit
frequencies required for composite moduli.

For any positive modulus q and any integer interval I of length L:

    FourierMass(I) <= L+q*H_(q-1),
    sum_{t!=0} gcd(t.val,q)*|Fourier(I)(t)|
      <= q*tau(q)*H_(q-1).

The second bound follows from a divisor-majorant for gcd and the
reciprocal-multiple harmonic estimate. Important names:

    gcd_reciprocal_sum_le
    gcd_reciprocal_reflect_sum
    gcd_val_neg
    gcd_val_mul_unit
    ringFourierMass_interval_le
    gcd_ringFourierMass_interval_le

### Actual rectangle counts and local density

`ringRectangleCount q M N B C r` counts integer pairs

    0<=i<B, 0<=j<C, (M+i)*(N+j)=r mod q.

The target r is a UNIT. Let U count the units in the first interval,
H=H_(q-1), and K=squarefreeBound(q). For squarefree positive q:

    |R-C*U/q| <= K*(B/q+H)*tau(q)*H,
    |U-B*phi(q)/q| <= 3^omega(q),
    |R-B*C*phi(q)/q^2|
      <= K*(B/q+H)*tau(q)*H + (C/q)*3^omega(q).

The final RHS is `squarefreeRectangleError q B C`.
The unit-density estimate is valid at arbitrary integer shifts, obtained
by translating into the previously proved natural cofactor count.
Important names:

    squarefree_interval_hyperbola_error
    ring_unit_interval_pairing
    ringHyperbolaWeight_eq_rectangleCount
    ringIntervalUnitCount_eq_coprime
    ringIntervalUnitCount_density_error
    ringRectangleCount_error_local

### Retained arithmetic weight and finite mean

The existing `doubleCofactorRow` and `doubleCofactorWeight` are reused.
The new main term is

    squarefreeCofactorMain f q B C X
      = B*C*phi(q)/q^2 * restrictedMass f X.

For f>=0, inputs coprime to q, and F=restrictedMass f X:

    |doubleCofactorWeight-squarefreeCofactorMain|
      <= squarefreeRectangleError(q,B,C)*F.

The CRT coefficient satisfies

    squarefreeRectangleError(q,B,C)
      <= 6^omega(q)*rectangleError(q,B,C).

For each delta>0 there is A_delta>0 such that uniformly over every
family P of squarefree q<=Q, and every nonnegative retained weight whose
nonzero inputs are coprime to the chosen moduli:

    sum_{q in P} |doubleCofactorWeight-squarefreeCofactorMain|
      <= A_delta*Q^delta*rectangleMeanKernel(Q,B,C)*F.

No density assumption is imposed. Important names, namespace
`Erdos821.AnalyticSieve`:

    squarefree_doubleCofactorWeight_error
    doubleCofactor_squarefree_modulus_mean

### Beyond-half scale range

The existing L=rectangleIntervalScale(m)=2^(64m) and
Q=rectangleModulusScale(m)=2^(72m) are retained; Q^16=(L^2)^9.
Choosing delta=1/72 gives Q^delta=2^m. Combining the existing bound

    rectangleMeanKernel(Q,L,L) <= 22000*(m+1)^2*2^(126m)

with the subpower factor leaves an exponential saving against
L^2=2^(128m). For every eta>0, eventually m, uniformly over all such
squarefree modulus families, shifts, units, and admissible weights:

    sum_{q in P} |doubleCofactorWeight-squarefreeCofactorMain|
      <= eta*L^2*F.

Names:

    rectangleModulusScale_small_rpow
    eventually_squarefree_rectangle_kernel_relative
    eventually_doubleCofactor_squarefree_relative
    eventually_doubleCofactor_squarefree_prime_weight

The last theorem specializes to weights supported on primes n>Q.
The more general theorem needs only coprimality to the selected moduli.

### Scope and remaining mathematical gap

The composite-modulus gap in this auxiliary estimate is now closed for
SQUAREFREE moduli. Nonsquarefree moduli remain untreated.

This is still a 9/16 level relative to the PRODUCT OF TWO FREE INTERVAL
LENGTHS. It is not a prime-only progression estimate, not an arbitrary
multiplier-pool estimate, and not a prime-successor lower bound.
No smooth-shifted-prime supply or new totient multiplicity exponent has
been obtained. Neither free interval can simply be removed.

The natural balanced range of the current coefficient is
Q<L^(8/7), apart from subpower/logarithmic losses. If both free factors
must individually be <=x^delta to enforce smoothness, this coefficient
alone only reaches Q<x^(8delta/7). Thus it gives no route to a sqrt(x)
prime-detecting sieve at arbitrarily small delta. This observation is
about the proved error bound, not a lower bound on the actual error.
The crucial arbitrary-root smooth-prime supply remains missing.

### Development notes

- Explicit functions are needed in `Finset.prod_coe_sort` and some
  `sum_nonzero_residue_values` rewrites.
- For CRT product instances, use local classical decidable equality for
  both the prime-factor subtype and each coordinate field.
- Give global local instances explicit distinct names. Autogenerated
  names collided when independently developed modules were imported
  together. `ringIntervalDecidableEq` and
  `squarefreeRectangleDecidableEq` now avoid this issue.
- Native versus classical `Decidable` instances can obstruct `if_congr`
  even when the displayed expressions match. Splitting the conditions
  and using the proved iff bridges them without changing definitions.
- `ringRectangleCount` is separate because the older `rectangleCount`
  accidentally captures the prime `Fact` instance in its declaration.

Spec SHA-256 remains
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.

---

## Latest continuation: two-cofactor prime-modulus mean beyond its half-level

**The exact conjecture remains UNSOLVED.** `Spec.lean` is unchanged with
its original `sorry`. The strongest established multiplicity exponent
remains 406667/666667. No proof/disproof has been submitted.

### Completed and audited modules

Five new result modules, 683 lines and 36 lemmas/theorems:

- `KloostermanHyperbola.lean` (134 lines)
- `ModularRectangleCounts.lean` (122 lines)
- `DoubleCofactorKloosterman.lean` (83 lines)
- `RectangleMeanKernel.lean` (167 lines)
- `DoubleCofactorPrimeScales.lean` (177 lines)

All five result oleans compile cleanly. The comprehensive independent
`DoubleCofactorPrimeScalesCheck.lean` compiles cleanly and audits all 36
declarations. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
It also checks the exact scale relation and relative kernel theorem.
`DoubleCofactorKloostermanCheck.lean` is an additional earlier check.
Logs are `/tmp/<Module>.log` and `/tmp/<Module>Check.log`.
No new source `sorry`, `admit`, or axiom has been introduced.

### Actual integer rectangle count

For a prime q, r!=0, integer shifts M,N, and arbitrary natural lengths
B,C, let R count pairs

    0<=i<B, 0<=j<C,  (M+i)*(N+j)=r mod q.

Let U be the count of nonzero residues in the first interval, and write
K(q)=sqrt(sqrt(3*q^3)), H=H_(q-1). Completion now gives

    |R-C*U/q| <= K(q)*(B/q+H)*H,
    |R-B*C*(q-1)/q^2| <= K(q)*(B/q+H)*H+C/q.

The second right-hand side is `rectangleError q B C`.
These are actual natural pair counts, not assumed equidistribution.
The zero-frequency contribution is removed exactly before taking norms.

Key names, namespace `Erdos821.Kloosterman`:

    hyperbolaWeight_completion
    hyperbolaWeight_error_identity
    interval_hyperbola_error_le
    hyperbolaWeight_eq_rectangleCount
    rectangleCount_error_units
    intervalUnitCount_error
    rectangleCount_error_local

### Retaining an arbitrary arithmetic weight

Namespace `Erdos821.AnalyticSieve`:

    doubleCofactorRow
    doubleCofactorWeight
    doubleCofactorLocalMain
    doubleCofactorWeight_error

The row counts u*(M+i)*(N+j)*n=1 mod q. The weight sums this row against
f(n), n<=X. If f>=0 and every input with nonzero weight is coprime to q,
then, with F=restrictedMass f X,

    |doubleCofactorWeight - B*C*(q-1)/q^2 * F|
      <= rectangleError(q,B,C) * F.

There is NO lower-density assumption and no requirement f<=Lambda.
The two free cofactor intervals remain explicit.

### Finite mean coefficient and prime-modulus mean

The new fourth-power Holder argument proves

    (sum_{1<=q<=Q} K(q)/q)^4 <= 3*Q^3*H_Q,
    sum_{1<=q<=Q} K(q)/q <= K(Q)*(1+H_Q).

Consequently

    sum_{1<=q<=Q} rectangleError(q,B,C)
      <= K(Q)*(B+Q)*(1+H_Q)^2 + C*H_Q.

The last expression is `rectangleMeanKernel Q B C`.
Summing the actual arithmetic errors over ANY finite family of PRIME
moduli <=Q yields this kernel times F. The arithmetic theorem is

    doubleCofactor_prime_modulus_mean.

Only the analytic coefficient is summed over all integers q; the actual
arithmetic estimate is still restricted to prime moduli. Do not mistake
the coefficient sum for an all-modulus arithmetic theorem.

### Concrete beyond-half range

Definitions:

    rectangleIntervalScale m = 2^(64*m) = L,
    rectangleModulusScale m  = 2^(72*m) = Q.

Exact identities/bounds:

    Q^16 = (L^2)^9,
    L<Q for m>=1,
    rectangleMeanKernel Q L L
      <= 22000*(m+1)^2*2^(126*m).

Since L^2=2^(128*m), the relative kernel tends to zero. The theorem

    eventually_doubleCofactor_prime_relative

says that for every eta>0, eventually m, uniformly in integer shifts,
source cutoff X, units u(q), and any nonnegative weight f supported on
primes n>Q, the sum of errors over any family of prime moduli q<=Q is
at most eta*L^2*F. A specialization to `mangoldtRestriction` of any prime
subset is also proved:

    eventually_doubleCofactor_prime_subset.

This is a 9/16 level relative to the PRODUCT OF THE TWO FREE COFACTOR
LENGTHS. It is not a 9/16 prime-only progression theorem and not a
9/16 level for an arbitrary retained multiplier pool. The natural
finite bound suggests the balanced two-interval range Q<L^(8/7),
apart from logarithms, but only the explicit 9/16 specialization has
been formalized asymptotically.

### Remaining gap and scope

- Composite moduli are not covered by the arithmetic estimate.
- Both unrestricted cofactor intervals remain; neither is replaced by
  an arbitrary prime pool or removed.
- No lower bound for prime successors was obtained.
- No new smooth-shifted-prime supply or multiplicity exponent follows.

In particular this does not settle Erdos 821, and does not bypass the
previously documented prime-only bias or the missing cofinal supply.

Development notes: declare a local classical `DecidableEq` using
`noncomputable local instance`, not `local noncomputable instance`.
Explicitly supply the test function when rewriting
`unit_intervalResidueWeight_pairing`; elaboration may not infer it.
For some fourth-power sum rewrites, an explicit `sum_congr` followed
by `ring` is more robust than `simp` with `pow_mul`.

Spec SHA-256 remains
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.

---

## Latest continuation: signed spectral bound and incomplete Kloosterman sums

**The original conjecture remains UNSOLVED.** `Spec.lean` is unchanged,
including its original `sorry`. No proof/disproof has been submitted.
The strongest established multiplicity exponent remains 406667/666667.

### Completed modules

Two new result files, 322 lines and 18 lemmas/theorems:

- `KloostermanSpectral.lean` (185 lines, 12 lemmas/theorems)
- `KloostermanIntervals.lean` (137 lines, 6 lemmas/theorems)

Namespace: `Erdos821.Kloosterman`.

Both result oleans compile cleanly. Matching `*Check.lean` files compile
cleanly and include exact expanded-type examples. Every declaration has
been axiom-audited: only `propext`, `Classical.choice`, and `Quot.sound`.
Logs are `/tmp/<Module>.log` and `/tmp/<Module>Check.log`.

### Signed spectral estimate

For arbitrary complex weights alpha,beta on a finite field of size q,
put

    E(w) = q*sum_x |w(x)|^2 - |sum_x w(x)|^2.

The new exact Parseval and inverse-graph factorization identities imply

    |sum_{a,b} alpha(a)*beta(b)*K(a,b)|^2 <= E(alpha)*E(beta).

The zero Fourier mode is removed exactly. Names include:

    positiveTransform_correlation
    positiveTransform_energy
    positiveTransform_units_energy
    positiveTransform_inverse_units_energy
    bilinearKloosterman_factorization
    bilinearKloosterman_centered_bound

The bound is sharp for arbitrary complex weights: for u0!=0, taking
alpha(a)=psi(-a*u0), beta(b)=psi(-b/u0) gives bilinear sum q^2 and each
centered energy q^2. Names:

    positiveTransform_wave
    centeredEnergy_wave
    bilinearKloosterman_waves

This sharpness assertion concerns arbitrary coefficient sequences, not
actual prime weights. The spectral result uses additive orthogonality;
it does not itself use the earlier pointwise fourth-moment improvement.

### Interval completion

`intervalResidueWeight q M L x` counts the integers M,...,M+L-1 whose
residue modulo q is x. Its Fourier mass is proved to satisfy

    FourierMass <= L + q*H_(q-1).

The proof reuses `sum_norm_intervalWaveSum_units_le` from the existing
`PolyaVinogradov.lean`, together with the new weighted completion.

For a prime q, b!=0, arbitrary integer M and natural L, define I as the
sum of e_q(a*x+b/x) over x=M,...,M+L-1 excluding x=0 modulo q. Then

    |I| <= sqrt(sqrt(3*q^3)) * (L/q + H_(q-1)).

In particular, if L<=q,

    |I| <= sqrt(sqrt(3*q^3)) * (2+log q).

Names:

    fieldFourier_intervalResidueWeight
    fourierMass_intervalResidueWeight_le
    intervalKloosterman_eq_weighted
    intervalKloosterman_norm_le_harmonic
    intervalKloosterman_norm_le_log

This is unconditional and uniform in the integer shift. It is an
incomplete Kloosterman upper bound, not a lower bound for primes.
No growing-modulus dispersion estimate for the actual restricted
smooth-prime family has been derived. No new multiplicity exponent or
cofinal smooth-prime supply follows from the results proved so far.

### Development notes

When specializing the generic finite-field definitions to `ZMod q`,
the native `DecidableEq (ZMod q)` and the generic classical one produce
non-definitionally-equal `Fintype (ZMod q)^*` instances. In the interval
proofs, use the explicit local instance

    letI : DecidableEq (ZMod q) := fun a b => Classical.propDecidable (a=b)

and bridge older native-unit sums with

    apply Finset.sum_congr (by ext u; simp)

rather than assuming the two `univ` finsets are definitionally equal.

A fresh attempt to fetch erdosproblems.com/821 again failed with DNS
resolution error. No new external result was obtained.

Spec SHA-256 remains
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.

---

## Latest continuation: elementary Kloosterman fourth moment and weighted completion

**The exact conjecture remains UNSOLVED.** `Spec.lean` is unchanged with
its original `sorry`. The strongest established multiplicity exponent
remains 406667/666667. No proof/disproof has been submitted.

### Completed and audited modules

Three new result files, 415 lines and 26 lemmas/theorems:

- `KloostermanCollisionEnergy.lean` (121 lines)
- `KloostermanFourthMoment.lean` (162 lines)
- `KloostermanCompletion.lean` (132 lines)

Namespace: `Erdos821.Kloosterman`.

All three result oleans compile cleanly. Independent checks:

- `KloostermanFourthMomentCheck.lean`
- `KloostermanCompletionCheck.lean`

Both check files compile cleanly and include exact expanded-type examples.
All 26 declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`. Logs are `/tmp/<Module>.log` and `/tmp/<Module>Check.log`.
There are no source `sorry`, `admit`, or added axioms in these modules.

### Actual finite-field estimate

For a finite field F of cardinality q, a primitive additive character psi,
and U=F^*, define

    K(a,b) = sum_{u in U} psi(a*u + b/u).

The collision energy counts pairs (x,y),(z,w) in U^2 satisfying

    x+y = z+w,     1/x+1/y = 1/z+1/w.

If x+y is nonzero, the pairs agree up to swapping. The zero-sum pairs
are bounded separately using the injective first projection. Thus

    collisionEnergy <= 3*(#U)^2.

This argument does not require odd characteristic.

The exact fourth-moment identity is

    sum_{a,b in F} ||K(a,b)||^4 = q^2 * collisionEnergy.

Multiplicative rescaling (a,b)->(a*c,b/c), c in U, preserves the sum.
When a is nonzero this orbit has cardinality #U. Consequently

    ||K(a,b)||^4 <= 3*q^2*(#U) <= 3*q^3.

Inversion exchanges a and b, so the last bound holds whenever
(a,b)!=(0,0). This is the elementary three-quarter-power estimate,
NOT the Weil square-root bound.

Key names:

    collisionEnergy_le
    kloosterman_fourth_moment
    kloosterman_rescale
    kloosterman_norm_fourth_le_units
    kloosterman_norm_fourth_le
    kloosterman_norm_fourth_le_of_ne_zero

### Exact weighted completion

For any complex weight w on F, put

    what(t) = sum_x w(x)*psi(-t*x),
    FourierMass(w) = sum_t ||what(t)||,
    Kw(a,b) = sum_{u in U} w(u)*psi(a*u+b/u).

The new completion identity and bound are

    q*Kw(a,b) = sum_t what(t)*K(a+t,b),
    q*||Kw(a,b)|| <= sqrt(sqrt(3*q^3))*FourierMass(w),  b!=0.

Names:

    fieldFourier_inversion
    weightedKloosterman_completion
    weightedKloosterman_norm_le_of_complete_bound
    weightedKloosterman_norm_le

The Fourier-mass factor has NOT been removed, and no small-Fourier-mass
estimate for the actual retained smooth-prime weights has been proved.
There is no new signed prime-progression dispersion theorem here and
no improvement to the multiplicity exponent. In particular this
auxiliary cancellation estimate is not a settlement of Erdos 821.

Spec SHA-256 remains
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.

---

## Latest continuation: extraction from an arbitrary predecessor prime support

**The exact conjecture remains UNSOLVED.** The attained exponent remains
406667/666667. `Spec.lean` is unchanged with its original `sorry`.

New completed module: `SparsePredecessorSupport.lean` (100 lines, four
lemmas/theorems), namespace `Erdos821.SparsePredecessors`. Its fresh result
olean and `SparsePredecessorSupportCheck.lean` compile cleanly. The check
includes an exact-type half-population example. All four declarations use
only `propext`, `Classical.choice`, and `Quot.sound`. Logs are
`/tmp/SparsePredecessorSupport.log` and
`/tmp/SparsePredecessorSupportCheck.log`.

For a finite family P of integers 2<=p<=X, suppose every prime factor of
p-1 belongs to an arbitrary finite support Q. For Y>0 the new bounds are

    #{p in P : p-1 is not Y-smooth}
       <= X * sum_{q in Q, q>=Y} 1/q
       <= #Q * X/Y.

Names: `nonsmooth_card_le_support_reciprocal` and
`nonsmooth_card_le_support_card`. `smooth_subfamily_card_lower` therefore
retains at least (1-delta)*#P members when #Q*X<=delta*Y*#P. The proof is an
explicit covering by shifted multiples, not a distribution assumption.
Primality of members of P is not needed for this finite extraction lemma.

This tested replacing an initial-segment smoothness assumption by a small
arbitrary support. A near-full-sized prime population with subpower-sized
support would already yield arbitrary-root smooth-prime supply via this
extraction. The existing full-pool support bound is only o(X/log X), not
X^o(1), and does not supply that hypothesis. No new sparse-support prime
population or improved multiplicity exponent was obtained.

The common-cofactor/Prachar-style variant was also considered informally:
pigeonholing a common cofactor does allow its arbitrary prime factors to
be placed in a small support, but the available progression level limits
the number of resulting prime labels relative to their size. No valid
exponent-amplification step or new growing-modulus estimate resulted.

No proof/disproof has been submitted, and no source repair is pending.
Spec SHA-256 remains
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.

---

## Latest continuation: prime-only bias already below the smoothness cutoff

**The exact conjecture remains UNSOLVED.** `Spec.lean` is unchanged with its
original `sorry`. The strongest unconditional exponent remains
406667/666667; no new multiplicity exponent was obtained here.

### New completed modules

Three modules, **556 lines and 27 declarations**, compile cleanly and have
independent permitted-axiom audits:

- `SmoothPredecessorLogAccounting.lean` (255 lines, 15 declarations).
- `SmoothPredecessorLogBias.lean` (136 lines, 6 declarations).
- `SmoothPrimeLowModulusBias.lean` (165 lines, 6 declarations).

Matching `*Check.lean` files compile; the last includes an exact-type example
of the final negative statement. Only `propext`, `Classical.choice`, and
`Quot.sound` occur. Logs are `/tmp/<Module>.log` and
`/tmp/<Module>Check.log`. No source `sorry` or unfinished repair remains in
these modules.

### Actual new arithmetic estimate

For nonnegative f<=Lambda supported, up to N, on integers p>=2 whose
predecessors are Y-smooth, put F=sum_{p<=N} f(p), and

    E = sum_{d<=Y} |sum_{p<=N, d|(p-1)} f(p) - F/phi(d)|.

For W>0 with W^3<=Y, the new finite bound is

    (log L - log Y - C)*F
      <= log Y*E + log L*log N*(L + 2*N/W),

with a single absolute constant C. Names:
`smooth_restricted_log_bias_of_sharp_main` and
`exists_truncatedLogMainTerm_sharp_bound`.

The proof uses the exact divisor-Mangoldt identity. If a Y-smooth integer
has no square divisor a^2 with a>=W, then every prime-power divisor is at
most Y. The excluded predecessors have cardinality at most 2*N/W. The
baseline sum Lambda(d)/phi(d), d<=Y, is at most log Y+C: higher prime powers
and the correction log(p)/(p-1)-log(p)/p are summable contributions.

`eventually_smooth_low_modulus_bias` specializes this as follows. For fixed
B>=6 and T>=2*B+3, at N=2^(T*m), Y=2^(B*m), any such f satisfying

    N <= 2^m*F

has E>=F eventually. The choices are L=2^((T-2)*m) and W=2^(2*m).
All exceptional terms are bounded explicitly by F using exponential
versus quadratic growth.

### Unconditional application to the existing smooth-prime population

`eventually_supplied_smooth_cutoff_bias` applies to the actual previously
supplied family

    N=cofactorScale(100005,2*m), Y=cofactorScale(44425,2*m),
    f=smoothMangoldtWeight(N,Y).

It proves eventually **F>0 and E>=F**. The cutoff satisfies Y^2<N at m>=1,
as proved by `supplied_smooth_cutoff_below_half`.

`not_supplied_smooth_cutoff_relative_decay` therefore refutes prime-only
relative decay with the ordinary main term F/phi(d) even at modulus cutoff
Q=Y. Unlike `SmoothPrimeOnlyBias.lean`, this does NOT use primes q>=Y as
moduli: it accounts for the necessary excess of small-prime divisibility
inside the smooth predecessor family.

### Scope

This is a disproof of a proposed auxiliary relative-distribution assertion,
NOT a disproof of Erdős 821. It does not exclude corrected, conditional main
terms or new one-sided estimates. The verified long-cofactor relative means
remain valid. No relative cutoff-loss estimate strong enough for iteration
to arbitrary roots has been proved.

`Spec.lean` still has SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof/disproof has been submitted.

---

## Latest continuation: exponent 406667/666667 and the band-budget limit

**The original conjecture remains UNSOLVED.** `Spec.lean` is unchanged,
including its original `sorry`. The strongest unconditional multiplicity
threshold is now

    gamma < 406667/666667 = 0.6100001949999025...

This supersedes 398667/666667 (~0.5980002). In particular, exponent 61/100
is proved. This is still a fixed exponent, not an iteration to exponent one.

### New and revised verified modules

Nine new modules, **732 lines and 34 declarations**, compile cleanly and
have independent permitted-axiom audits:

| Module | Lines | Declarations |
|---|---:|---:|
| `PoolBandBudgetAudit.lean` | 82 | 5 |
| `PoolBandScales.lean` | 114 | 6 |
| `PoolBandBudget.lean` | 73 | 2 |
| `PoolBandBounds.lean` | 107 | 3 |
| `FinePoolBands.lean` | 95 | 8 |
| `FinePoolRoughBound.lean` | 68 | 2 |
| `FinePoolSmoothDensity.lean` | 103 | 2 |
| `FinePoolMultiplicity.lean` | 33 | 4 |
| `PoolBandLevelAudit.lean` | 57 | 2 |

Four existing modules were generalized and re-audited:

- `PoolDyadicRectangles.lean`: now 107 lines, 3 declarations.
- `PoolDyadicHyperbola.lean`: 129 lines, 1 declaration.
- `PoolHyperbolicBound.lean`: 88 lines, 1 declaration.
- `PoolNarrowHyperbolas.lean`: 137 lines, 3 declarations.

All affected dependencies through `PoolMultiplicity.lean` were rebuilt.
Every new/revised declaration has a matching `*Check.lean` audit. Only
`propext`, `Classical.choice`, and `Quot.sound` occur; some elementary
definitions need no axioms. All build logs `/tmp/<Module>.log` are empty;
check logs `/tmp/<Module>Check.log` have no errors/warnings. There is no
pending repair or new `sorry`/`admit`.

### Strongest declarations

In `FinePoolMultiplicity.lean`, namespace `Erdos821`:

- `infinite_g_gt_fine_pool_gain (gamma : R)
    (hgamma : gamma < 406667/666667)`.
- `infinite_g_gt_sixty_one_hundredths`: exponent exactly 61/100.
- `erdos_821_fine_pool_range (epsilon : R)
    (hepsilon : 260000/666667 < epsilon)`.
- `fine_pool_threshold_improves_retained_pool`.

`FinePoolSmoothDensity.lean` proves actual prime supply:

    exists C>0, eventually m,
      independentN(40000020,m)
        <= C*m * #smoothPrimePool(independentN(40000020,m),
                                  independentN(15600000,m)).

The two theorem names are `exists_fine_pool_smooth_prime_count_enlarged`
and `exists_fine_pool_smooth_prime_count`. The predecessor smoothness
ratio is 15600000/40000020, about 0.39.

### The artificial successor-sieve restriction was relaxed

`eventually_cofactor_dyadic_sift_below` proves that for 1<=t and b<2*t,

    eventually k,
      cofactorScale(b,cofactorDyadicIndex(t,k)) <= 2^(k-1).

A sufficient threshold is k>=512*b*t+2*t. Accordingly, the four revised
rectangle/hyperbola theorems now take **b<2*t**, not b<=t. This permits
sieve cutoffs above sqrt(q) in lower prime-variable bands, while the
cutoff still remains below q. It does NOT increase the initial
progression-modulus level.

### Thirty-six bands and exact budget

Let e_i = 7800000 + floor(2200007*i/36), for 0<=i<=36. These endpoints
are stored explicitly in `finePoolEndpoint`, with e_36=10000007.

The fixed successor-mean parameters are

    a=1, s=3, t=100000000, product upper scale=200000000,
    rq=rc=10, w=3, eta=1.

In band i,

    b_i = floor(100000000*9999900/e_(i+1)),
    l_i = 2*b_i-100000000+1.

The actual naturals are stored in `finePoolB` and `finePoolL`.
`finePool_band_parameters` verifies every scale and unit-support condition.
`finePool_band_limit` verifies every limiting budget. The budgets are
rational with denominator 100000000, and their exact sum is

    99926455/100000000 = 0.99926455.

The existing short tail contributes 11/62500=0.000176. Hence the total
is at most 0.99944055, strictly below 1999/2000=0.9995.
`eventually_fine_pool_rough_rejection_bound` gives that final aggregate
bound on the actual wide multiplier pool. The existing initial prime
supply has enough margin after its independent progression and
prime-power errors, yielding the new smooth-prime density above.

The uniform block-error lemma now handles all positive lower band
endpoints at once. The finite narrow multiplier partition is unchanged;
no pointwise c-bound or unjustified replacement by a wide-pool minimum
is used.

### A formal audit of why band refinement alone does not settle the problem

`PoolBandBudgetAudit.lean` is deliberately independent of the arithmetic
counts. Define

    poolBandBudget(x,A,n) = sum_{i<n} A_i*(1/x_i-1/x_(i+1)).

For positive monotone endpoints and A_i>=x_(i+1)/ell, it proves

    log(x_n/x_0)/ell <= poolBandBudget(x,A,n).

Thus if ell<=L, x_n>=tau, and this budget is <1, then

    tau*exp(-L) < x_0.

In particular, with initial half-level and successor exponent at most
1/4, the assumptions A_i>=4*x_(i+1), x_n>=1/2 and budget<1 imply

    exp(-1/4)/2 < x_0.

That cutoff is approximately 0.38940039, corresponding to exponent
approximately 0.61059961. This is an obstruction for this specific
nonnegative rejection certificate, NOT a lower bound for the actual
rejected-prime count and NOT a disproof of Erdős 821.

`PoolBandLevelAudit.lean` links the audit to the actual named constants:
under b*v<100000000*10000000 and b>=1,

    4*v <= (40000021/2)*poolBandCoefficient(b),

and for 1<=u<=v,

    4*log(v/u)
      <= scaledProductLongLimit(poolBandCoefficient(b),u,v).

So the audit is not based on an unrelated model coefficient. The tiny
positive error allowance and the fine-partition losses do not remove
this restriction.

### Remaining gap and next direction

The successor cutoff restriction b<=t was artificial and is now removed.
The separate restriction on the initial progression-prime supply was
not removed. No new signed lower bound for near-full smooth modulus
pools has been proved, and no exponent-amplification theorem exists.
Further numerical band refinement at these same levels cannot provide
the arbitrary-root input required by the full conjecture. A genuinely
new lower-bound argument, or another construction not subject to this
budget, is still needed.

Spec SHA-256 remains
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof/disproof has been submitted.

---

## Latest continuation: actual retained-pool supply and exponent 398667/666667

**The original conjecture remains UNSOLVED.** `Spec.lean` is unchanged,
including its original `sorry`. However, this continuation establishes a
new unconditional multiplicity threshold:

    gamma < 398667/666667 = 1196001/2000001
                         = 0.5980002009998995...

This supersedes the previous threshold 372267/666667 (~0.5584002).
The new result is an actual smooth-prime lower bound and multiplicity
transfer, not only a conditional estimate or a primitive character mean.
It still does NOT settle the arbitrary-epsilon conjecture.

### New modules and verification

Twelve new modules, **1343 lines and 69 declarations**, compile cleanly:

| Module | Lines | Declarations |
|---|---:|---:|
| `PoolPrimeRectangles.lean` | 154 | 13 |
| `PoolDyadicRectangles.lean` | 91 | 2 |
| `PoolHyperbolicCover.lean` | 87 | 6 |
| `PoolDyadicHyperbola.lean` | 129 | 1 |
| `PoolHyperbolicBound.lean` | 88 | 1 |
| `RefinedMultiplierPools.lean` | 133 | 15 |
| `PoolNarrowHyperbolas.lean` | 137 | 3 |
| `PoolSupplyScales.lean` | 113 | 8 |
| `PoolSupplyBlocks.lean` | 143 | 10 |
| `PoolSupplyBudget.lean` | 132 | 4 |
| `PoolSmoothDensity.lean` | 103 | 2 |
| `PoolMultiplicity.lean` | 33 | 4 |

Every declaration has a matching independent `*Check.lean` audit. Only
`propext`, `Classical.choice`, and `Quot.sound` occur (some elementary
natural-number declarations use no axioms). All `/tmp/<Module>.log` files
are empty. Audit logs `/tmp/<Module>Check.log` have no warnings/errors.
No `sorry`, `admit`, pending repair, or new axiom occurs in these modules.

### Strongest new multiplicity declarations

In `PoolMultiplicity.lean`, namespace `Erdos821`:

- `infinite_g_gt_retained_pool_gain (gamma : R)
    (hgamma : gamma < 1196001/2000001)`
- `infinite_g_gt_299_over_500`: exponent exactly 299/500 = 0.598.
- `erdos_821_retained_pool_range (epsilon : R)
    (hepsilon : 804000/2000001 < epsilon)`.
- `retained_pool_threshold_improves_scaled_product`.

The first theorem proves infinitude of the original actual g(n), not a
model function. The rational threshold simplifies to 398667/666667.

### Actual smooth-prime lower bound

`PoolSmoothDensity.lean` proves:

    exists C : N, C>0, eventually m,
      independentN(40000020,m)
        <= C*m * #smoothPrimePool(independentN(40000020,m),
                                  independentN(16080000,m)).

Names:

- `exists_retained_pool_smooth_prime_count_enlarged`.
- `exists_retained_pool_smooth_prime_count`.

The predecessor smoothness ratio is 16080000/40000020, about 0.402.
The existing bounded-enlargement Mangoldt slope and wide-prime-product
progression lower estimates supply the independent initial prime mass.

### New analytic steps that were missing at the last handoff

1. `intervalPrimeWeight M` is the Mangoldt weight restricted to ACTUAL
   primes n>M. Its mass up to N is at most psi(N)-psi(M), and its support
   is coprime to every sieve prime <=z when z<=M. No prime powers are
   silently used as primes in the unit-supported application.
2. `exists_pool_prime_rectangle_power_saving` gives a prime-pair count
   with main term #P*B*(psi(N)-psi(M))/(log(z+1)*log M). The ambient error
   uses D*B*N, NOT #P copies of the old pointwise error.
3. `eventually_dyadic_pool_sieve_error` allows any fixed denominator
   (k+1)^w. This is necessary to sum over both c and q block ranges.
4. `eventually_dyadic_pool_hyperbolic_pairs` and
   `exists_pool_hyperbolic_bound` retain the harmonic Mangoldt main mass,
   then sum it using the existing bounded Mertens error. The main term
   contains the reciprocal-log difference; the error has an arbitrary
   extra inverse-log power.
5. `RefinedMultiplierPools.lean` partitions the original wide pool
   EXACTLY into fine subintervals of each dyadic c interval. With r
   subdivisions in the exponent, each dyadic interval has 2^r pieces.
   There are LC*2^r blocks. Reweighting the main mass loses only
   1+2^(-r), independent of the original power-sized width. The ambient
   product D*floor(X/C) is at most (1+2^(-r))*X on each narrow block.
6. `exists_wide_pool_hyperbolic_bound` sums all those blocks. Its error
   costs the number of blocks, not the number of multipliers.

The earlier concern about replacing the whole wide pool by its minimum
has now been fully addressed, rather than ignored.

### Concrete application and budgets

Initial multiplier pool:

    P = widePairPool(10000000,m),
    independentN(20000000,m) <= c <= independentN(20000004,m).

Ambient prime cutoff:

    independentN(40000020,m) <= X <= independentN(40000021,m).

Long rejected-prime range:

    2^(128*8040000*m) < q <= 2^(128*10000007*m).

Analytic parameters:

    a=1, b=99990000, s=3, l=99990001,
    v=150000000, t=100000000,
    rq=rc=10, w=3, eta=1.

Multiplier dyadic range:

    KC=64*20000000*m-1,
    LC=256*m+2.

`PoolSupplyScales.lean` handles the floors before comparing powers. In
particular, the lower product bound uses

    X/(2*Q) <= D*(X/C/Q)

when C<=D and C*Q<=X. This retains full-product length even when the
short cofactor is very short. The upper product bound is

    D*(X/C/Q) <= 2*(X/Q)  when D<=2*C.

All narrow-block size hypotheses hold for m>=1000000. The sieve prime
cutoff lies strictly below independentN(10000000,m), so both prime
factors of every c in the ACTUAL wide pool avoid all sieve primes.

The long main coefficient is

    poolLongCoefficient
      = (2*100000000/99990000)*(1+2^(-10))^2.

The limiting normalized long budget, including the tiny relative error
allowance, is <49/50 (numerically approximately 0.97713185).
`eventually_pool_block_coefficient` absorbs all multiplier-block errors
relative to the actual lower reciprocal mass 1/widePairMassDenom.

`eventually_pool_long_rejection_bound` proves the 49/50 budget.
The previously proved short-tail estimate contributes 11/62500.
`eventually_pool_rough_rejection_bound` consequently proves

    log X * sum_{c in P} #roughProgressionPrimes(c,Y,X)
      <= (99/100)*X*poolTotientMass(P),

where Y=independentN(16080000,m). This is an aggregate c-pool bound, not
a pointwise estimate for every c.

### What still does not follow

This construction still uses the existing fixed half-level initial
prime supply. It does not yield arbitrary-root smooth shifted primes,
and there is no exponent-amplification theorem. The full original
conjecture remains open within this development.

Further numerical/band refinement might improve this fixed threshold,
but cannot be cited as an iteration to exponent one. The current
`PoolDyadicRectangles` theorem uses b<=t to place the sieve cutoff below
the prime interval; treating lower bands with t<b<2*t would need the
corresponding generalized dyadic cutoff lemma. That refinement alone
would still only improve a fixed constant, not supply the missing full
conjecture input.

Spec SHA-256 remains
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No full proof/disproof has been submitted.

---

## Latest continuation: retained-pool all-modulus and successor completion

**The original conjecture remains UNSOLVED.** `Spec.lean` is unchanged,
including its original `sorry`. The strongest proved multiplicity threshold
is still **372267/666667**. No new smooth-prime lower bound, no exponent
amplification, and no complete settlement has been established here.

### Completed and independently audited

Five modules, **742 lines and 34 declarations**, compile cleanly:

- `PoolCofactorConductorSplit.lean`: 128 lines, 6 declarations.
- `PoolCofactorCompletion.lean`: 229 lines, 8 declarations.
- `PoolCofactorScales.lean`: 168 lines, 8 declarations.
- `PoolSuccessorSieve.lean`: 137 lines, 10 declarations.
- `PoolSuccessorScales.lean`: 80 lines, 2 declarations.

The first module and the initial three completion lemmas existed at the
previous handoff. The rest were completed in this continuation. All five
have matching `*Check.lean` files. Every declaration has been independently
audited: only `propext`, `Classical.choice`, and `Quot.sound` occur. Build
and audit logs are `/tmp/<Module>.log` and `/tmp/<Module>Check.log`.
No warning/error or pending repair remains in these five modules.

### The finite all-modulus estimate is now complete

`pool_unit_all_modulus_mean_of_local_weight` works over any finite
`S subset Icc 1 Q`, assuming both the multiplier pool P and the support
of f up to N are units modulo each d in S. The unit assumptions are NOT
imposed at moduli outside S. Only nonnegative conductor majorants are
enlarged to the full interval.

`pool_unit_principal_density_error` and
`pool_unit_principal_mean_of_local_weight` replace the exact principal
term without a nonunit error. The natural-density completion is
`exists_pool_unit_natural_mean_bound`. For every epsilon>0 it supplies
C>0, uniform in f,P,S,Q,R,B,N,u, such that

    sum_{d in S} |poolCofactorWeight(f,P,d,u(d),0,B,N)
                       - #P*B*F(N)/d|
      <= C*Q^epsilon*H(Q) *
           [ #P*F(N)*(1+R*sqrt(R)*(1+log R))
               + primitivePoolCofactorMean(f,(R,Q],P,B,N) ].

Here F(N)=restrictedMass(f,N), and f>=0. There is NO B*Q lifting term.
The exact unit-supported identities are used to remove that term, not
an estimate that silently requires Q<N.

### The power-scaled natural mean is also complete

`exists_pool_unit_natural_power_saving` takes fixed natural parameters
`a b s l v t` satisfying

    1 <= a <= b, 2*a+1 <= s, 1 <= l, 1 <= t,
    2*b+1 <= l+t.

For any m,D,B,X, require

    cofactorScale(s,m) <= B,
    cofactorScale(l,m) <= D*B <= cofactorScale(v,m),
    X <= cofactorScale(t,m),
    P subset Icc 1 D, S subset Icc 1 cofactorScale(b,m).

For 0<=f<=Lambda and the two unit-support conditions on S, the natural
mean is at most

    K*(m+1)^7/2^m * (D*B)*cofactorScale(t,m).

K is uniform in f and both supports. The short cofactor lower scale s
controls small conductors. The PRODUCT lower scale l controls large
conductors. In particular, **no hypothesis b+1<=t remains**.

The explicit extra logarithmic factor is bounded by

    poolCofactorLogConstant(v)*(m+1)^3,
    poolCofactorLogConstant(v) = (256v+4)*(256v+1)^2.

This is an AMBIENT saving, not a relative saving for arbitrarily sparse
P or f. Their main mass is still actual #P*B*F(X).

### Finite successor sieve and its scaled application

`poolSieveModuli J z` consists of products of subsets of the prime sieve
pool J, with product at most z^2. It is a subset of Icc 1 z^2.

`poolPrimeSuccessorWeight f P A B N z` sums f(n) over triples

    c in P, A<a<=B, 1<=n<=N,
    c*a*n+1 prime and c*a*n+1>z.

`pool_successor_congruence` uses the fixed unit -1, so its divisibility
identity needs no coprimality assumption on c. Orthogonality is only
needed later, at the analytic-mean application.

`exists_pool_successor_sieve_bound` gives

    poolPrimeSuccessorWeight
      <= #P*(B-A)*F(N)/oneRootDenominator(J,z)
          + C*(z^2)^epsilon *
              sum_{d in poolSieveModuli(J,z)} poolSuccessorDiscrepancy(d).

The subset of sieve moduli is preserved, using a zero-extended error
function in the general weighted Selberg theorem.

`pool_sieve_unit_support` obtains both product-modulus unit hypotheses
from coprimality to the individual primes in J. Thus products can exceed
N even when the support of f consists of primes between z and N.

Finally, `exists_pool_unit_successor_power_saving` combines the sieve
and natural mean at doubled scale. Under the same fixed parameter
conditions, with all mean-size assumptions evaluated at 2*m, it proves

    poolPrimeSuccessorWeight(f,P,0,B,X,cofactorScale(b,m))
      <= #P*B*F(X)/oneRootDenominator(J,cofactorScale(b,m))
          + K*(m+1)^7/2^m * (D*B)*cofactorScale(t,2*m).

Here all p in J are primes <=cofactorScale(b,m), P is coprime to every
p in J, and every n<=X with f(n)!=0 is coprime to every p in J.

### Remaining mathematical obligations

The prior handoff's finite all-modulus completion and successor-sieve
steps are now proved. What remains is NOT an omitted lifting estimate:

1. Construct the actual interval prime weights (above the sieve primes)
   and suitable multiplier pools for the rough-prime rejection problem.
2. Subdivide the initial multiplier pool into narrow intervals: the
   hyperbolic cofactor cutoff depends on c. Replacing every c by the
   minimum of the old wide pool loses a power-sized factor.
3. Sum the ambient errors over those blocks and compare the actual
   principal masses with an independently established prime supply.
4. Prove a positive retained-prime lower bound.

Even accomplishing those steps with the existing fixed half-level prime
supply would give only another fixed smoothness threshold. This upper
sieve does NOT by itself provide primes with arbitrarily small relative
predecessor factors. No new argument giving multiplicity exponents
arbitrarily close to one has been found. Do not present this completion
as a settlement or an exponent-amplification theorem.

Spec SHA-256 is still
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No full proof/disproof is ready for submission.

---

## Latest continuation: retained multiplier-pool primitive estimates

**The original conjecture remains UNSOLVED.** `Spec.lean` is unchanged,
including its original `sorry`. The strongest proved multiplicity exponent
is still **372267/666667**. No new smoothness ratio is claimed in this
continuation, and no complete proof/disproof is ready to submit.

Four new modules, **641 lines and 31 declarations**, compile cleanly and
have independent permitted-axiom audits:

- `MultiplicativeCofactorEnergy.lean`: 148 lines, 8 declarations.
- `MultiplicativeCofactorMaximal.lean`: 134 lines, 6 declarations.
- `MultiplicativeCofactorPrimitive.lean`: 198 lines, 9 declarations.
- `MultiplicativeCofactorOrthogonality.lean`: 161 lines, 8 declarations.

Matching `*Check.lean` files audit every declaration. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. Logs are
`/tmp/<Module>.log` and `/tmp/<Module>Check.log`; no warnings/errors or
pending repairs. Temporary `AverageProbe.lean` was removed.

### New structural route, not another band-constant change

The existing rough-prime estimate treats the initial progression modulus
c pointwise. The new estimates instead retain the sum over a finite pool
P of multipliers c inside the character mean for c*a*q = -1 modulo the
sieve modulus. This is different from simply multiplying the old bound by
#P, and different from the earlier restricted-prime-weight generalization.

The arithmetic weight f is arbitrary with 0 <= f(n) <= Lambda(n).
All new primitive mean theorems have explicit f,hf,hLambda arguments.
There is no positive-density assumption on f or P; the final energy bounds
are ambient, not automatically relative to their actual masses.

### Product collisions and adaptive prefixes are controlled

For P subset [1,D], A subset [1,B], |w(a)|<=1, define

    pairCofactorCoefficient(P,A,w,n)
      = sum_{c in P, a in A, c*a=n} w(a).

The coefficient has norm at most tau_2(n). The existing divisor-square
moment therefore bounds its energy by X*(1+log X)^3, at X=D*B. Exact
reindexing preserves the product of the two character sums.

Fourier completion is performed in the short cofactor a BEFORE taking
products. The Fourier-twisted collision coefficients obey the same energy
bound. Thus even a character-dependent cofactor cutoff is allowed:

    primitive_maxPrefix_pool_bilinear_bound

controls the primitive mean of

    |sum_{c in P} chi(c)| * max_{T<=B}|sum_{a<=T} chi(a)|
      * |sum_{n<=N} f(n)chi(n)|

by

    maximalPairCofactorKernel(Q,D,B,N)
      = (2+log(B+2))*(1+log(D*B))^2
          * cofactorBilinearKernel(Q,D*B,N).

The pool character sum has NOT been replaced by #P.

### Actual full-product primitive saving

`primitivePoolCofactorMean f S P B N` is the corresponding sum over
primitive conductors in S, with weight 1/phi(conductor).
`cofactorScale_pool_primitive_saving` proves

    2^(2m) * primitivePoolCofactorMean
        f (cofactorScale(a,m),cofactorScale(b,m)] P B X
      <= poolCofactorLogLoss(D,B) * cofactorProductMeanConstant(b,v,t)
           * (m+1)^3 * (D*B) * cofactorScale(t,m)

under P subset [1,D], 1<=a<=b, 1<=l, 1<=t,

    2*b+1 <= l+t,
    cofactorScale(l,m) <= D*B <= cofactorScale(v,m),
    X <= cofactorScale(t,m).

Here `poolCofactorLogLoss(D,B)=(2+log(B+2))*(1+log(D*B))^2`.
The large-sieve length is D*B rather than B. This theorem is only for the
primitive conductor range, NOT an all-modulus progression estimate.

### Exact orthogonality and zero lifting error under explicit support conditions

`poolCofactorWeight f P d u A B N` counts the weighted congruence
u*c*a*n=1 modulo d, summed over c in P before absolute values.
`pool_cofactor_orthogonality` is exact. If every c in P is coprime to d
and every n<=N with f(n)!=0 is coprime to d,
`pool_cofactor_discrepancy` has exact principal term

    #P * coprimeCofactorCount(d,A,B) * restrictedMass(f,N) / phi(d)

and a nonprincipal error retaining all three character factors.
`unit_supported_twisted_changeLevel` and `unit_pool_character_changeLevel`
prove exact lifting, with NO deleted-prime error, under these hypotheses.
`unit_supported_nonunitMass_zero` makes the principal correction zero.

### Concrete next mathematical step (not yet proved)

Complete the conductor split and all-modulus mean for a collection S of
sieve moduli, with the two unit-support conditions holding for every d in S.
Small conductors still require the SHORT cofactor prefix B to be long;
large conductors can use the new full-product D*B*N estimate. Do not replace
this missing completion by the old all-modulus theorem.

The old all-modulus proof has a lifting error of order B*Q (times logs),
requiring the modulus level Q to stay below the prime-variable range N.
That condition would defeat the intended improvement when Q>N. The exact
unit-supported lifting above is the proposed way around this issue.

For a future Selberg application, restrict f to actual primes in an
interval above the sieve-prime cutoff z, and use multiplier pools whose
prime factors also exceed z. The relevant sieve moduli have all prime
factors at most z, so the two unit-support conditions can hold even when
the full modulus is larger than N. This application is NOT yet formalized.

A complete density application would also need:
- a weighted pool successor sieve with the actual mass of f;
- subdivision of the initial multiplier pool into narrow intervals, since
  the hyperbolic cofactor cutoff depends on c;
- summed error budgets and an actual retained-prime lower bound.

No improved multiplicity exponent, prime-only relative equidistribution,
or exponent-amplification result follows from the present modules alone.

Spec SHA-256 remains:
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.

---

## Latest continuation: rescaled sixteen-band positive improvement

**The original conjecture remains UNSOLVED.** `Spec.lean` is unchanged,
including its original `sorry`. No full proof/disproof has been submitted.
The strongest unconditional multiplicity threshold is now
**372267/666667 = 0.5584002207998896...**.

Five new auxiliary modules, **593 lines and 35 declarations**, have clean
builds and independent permitted-axiom audits:

- `ScaledProductBudget.lean`: 189 lines, 14 declarations.
- `ScaledProductBands.lean`: 153 lines, 12 declarations.
- `ScaledProductRoughBound.lean`: 110 lines, 3 declarations.
- `ScaledProductSmoothDensity.lean`: 108 lines, 2 declarations.
- `ScaledProductMultiplicity.lean`: 33 lines, 4 declarations.

Each has a matching `*Check.lean`. All declarations were independently
checked; the only axiom dependencies are `propext`, `Classical.choice`,
and `Quot.sound`. Logs are `/tmp/<Module>.log` and
`/tmp/<Module>Check.log`. No warnings/errors or repairs are pending.

### Arithmetic refinement

The original product-half-level estimate is unchanged. The construction
uses the larger initial pool `widePairPool 10000000`, with prime cutoff
`independentN(40000020,m)` and progression modulus exponents from 20000000
to 20000004. The quotient lies between

    2^(128*10000008*m) and 2^(128*10000011*m).

Sixteen long-cofactor bands have endpoints

    u_i = 8832000 + 73000*i,  0 <= i <= 15,
    u_16 = 10000007,

and actual prime-variable endpoints 2^(128*u_i*m). Each band has a
separately checked product-level sieve parameter set. The sum of long-band
budgets is 998489/1000000. Rescaling reduces the short-tail main bound to
7/40000, and its error is bounded by 1/1000000; the total short budget is
11/62500. Thus the rejected-prime budget is

    998489/1000000 + 11/62500 = 199733/200000 < 1999/2000.

The retained-prime proof uses the already proved bounded-gap Mangoldt
slope theorem at 99999/100000, leaving a strictly positive margin after
progression and prime-power errors. Every parameter and budget inequality
is proved in Lean by exact arithmetic, not floating-point approximation.

### New positive supply and multiplicity conclusions

`exists_scaled_product_smooth_prime_count` proves

    exists C>0, eventually m,
      independentN(40000020,m)
        <= C*m*#smoothPrimePool(independentN(40000020,m),
                               independentN(17664000,m)).

In namespace `Erdos821`:

    infinite_g_gt_scaled_product_gain (gamma : Real)
        (hgamma : gamma < 372267/666667) :
      {n | (g n : Real) > (n : Real)^gamma}.Infinite

Also:
- `infinite_g_gt_349_over_625` proves exponent 349/625 = 0.5584.
- `erdos_821_scaled_product_range` proves the original conclusion only for
  epsilon > 294400/666667.
- `scaled_product_gain_improves_fine_product` proves that the threshold is
  strictly larger than the previous 11141/20001.

### Remaining gap

This is a verified positive fixed-exponent improvement, not a settlement.
Neither rescaling nor increasing the number of bands establishes an
exponent-amplification theorem or arbitrary-root smooth-prime supply.
The full quantifier over every epsilon>0 remains unproved.

Spec SHA-256 remains:
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.

---

## Latest continuation: nine-band positive multiplicity improvement

**The original conjecture remains UNSOLVED.** `Spec.lean` is unchanged,
including its original `sorry`. No full proof/disproof has been submitted.
The strongest unconditional multiplicity threshold is now
**11141/20001 = 0.5570221488925554...**, improving the previous
11116/20001 by 25/20001.

Four new auxiliary modules, **397 lines and 21 declarations**, have clean
builds and independent axiom audits:

- `FineProductBands.lean`: 146 lines, 12 declarations.
- `FineProductRoughBound.lean`: 110 lines, 3 declarations.
- `FineProductSmoothDensity.lean`: 108 lines, 2 declarations.
- `FineProductMultiplicity.lean`: 33 lines, 4 declarations.

Each has a matching `*Check.lean`. Build and audit logs are
`/tmp/<Module>.log` and `/tmp/<Module>Check.log`. Every declaration was
checked; the only axiom dependencies are `propext`, `Classical.choice`,
and `Quot.sound`. There are no warnings/errors or pending repairs.

### Positive arithmetic refinement

The initial smooth progression modulus supply and the short-cofactor tail
are unchanged. The long-cofactor range is split at these nine-band endpoints:

    88600, 89700, 91000, 92300, 93600,
    94900, 96200, 97500, 98800, 100007.

Actual prime-variable endpoints are 2^(128*u*m). Each band separately uses
the product-half-level hyperbolic estimate with a tailored sieve level.
The new generic threshold lemma retains the strict inequality

    l*v < t*(100008-v),

which eventually ensures the required lower bound on cofactor length.
All nine parameter sets and all nine limiting budget inequalities are
proved by exact rational arithmetic (using the existing bound on log 2),
not by floating-point computation.

The long-band budgets sum to 1221/1250. Adding the unchanged weighted tail
bound 11/625 gives 1243/1250 < 199/200. Thus the same retained-prime argument
now supplies the smaller smoothness cutoff 177200/400020:

    exists_fine_product_smooth_prime_count :
      exists C>0, eventually m,
        independentN(400020,m)
          <= C*m*#smoothPrimePool(independentN(400020,m),
                                 independentN(177200,m)).

### New multiplicity exports

In namespace `Erdos821`:

    infinite_g_gt_fine_product_gain (gamma : Real)
        (hgamma : gamma < 11141/20001) :
      {n | (g n : Real) > (n : Real)^gamma}.Infinite

Also:
- `infinite_g_gt_557_thousandths` proves the exponent 557/1000.
- `erdos_821_fine_product_range` proves the original conclusion for
  epsilon > 8860/20001 only.
- `fine_product_gain_improves_product` verifies the strict improvement.

### Gap remains

This is a genuine positive fixed-exponent improvement, not a proof of the
full epsilon quantifier. No bootstrap to arbitrary-root smoothness has
been established. The sparse-scale quantifier review supplied no new
near-full prime-pool lower bound. Do not submit these auxiliary theorems
as a settlement of Erdős 821.

Spec SHA-256 remains:
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.

---

## Latest continuation: actual smooth-prime prime-only bias below square root

**The original conjecture remains UNSOLVED.** `Spec.lean` is unchanged,
including its original `sorry`; no full proof/disproof has been submitted.
The best multiplicity exponent remains **11116/20001**.

`SmoothPrimeOnlyBias.lean` (133 lines, 12 declarations) was freshly built
with an empty log and independently axiom-audited in
`SmoothPrimeOnlyBiasCheck.lean`. All declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. Audit logs have no warnings/errors.
Logs: `/tmp/SmoothPrimeOnlyBias.log` and `/tmp/SmoothPrimeOnlyBiasCheck.log`.
No repairs or background builds are pending.

### A concrete false extrapolation is ruled out

Let f be the actual Mangoldt weight restricted to primes p<=N with p-1
Y-smooth, and F its total mass. For any prime q>=Y, the prime-only
progression p=1 mod q has ZERO restricted mass. This is proved as
`smooth_prime_only_weight_zero`, using the singleton-cofactor identity.

For any finite prime pool P above Y, the summed discrepancy from the
PRIME-ONLY principal main term F/phi(q) is exactly

    F * poolTotientMass(P).

This is different from the cofactor-averaged natural main term B*F/d.
No assertion against either previously proved cofactor mean is made.

For the actual supplied family, take

    N = cofactorScale(100005,2m),
    Y = cofactorScale(44425,2m),
    Q = cofactorScale(50000,2m).

The pool of primes in (Y,Q] has reciprocal-totient mass tending to

    c = log(50000/44425) > 0.

The earlier smooth-prime supply gives F>0 eventually. The new
`eventually_supplied_prime_only_bias` proves eventually

    F>0 and primeOnlyRestrictedError(f,Q,N) >= (c/2)*F.

`suppliedBias_level_below_half` checks Q^2<N for every m>=1.
`not_supplied_prime_only_relative_decay` therefore refutes the proposed
assertion that this prime-only error is <=eta*F eventually for EVERY eta>0.
This is a genuine obstruction involving the actual family, not an abstract
countermodel. It is NOT the negation of Erdős 821.

### Remaining gap

The attempt to infer a cofinal higher-moment lower bound from compensating
bias below Y did not produce such a bound. The factorization log budget
alone is not the missing high-order arithmetic estimate. No new smoothness
ratio or multiplicity exponent was obtained.

In future work, do not assume a prime-only relative Bombieri--Vinogradov
statement with main term F/phi(d) for these smooth-prime restrictions: the
new theorem shows that extrapolation is false even below square root.
The cofactor-averaged estimates and their explicit long-prefix hypotheses
remain valid.

Spec SHA-256 remains:
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.

---

## Latest continuation: density-free relative error at the cofactor level

**The original conjecture remains UNSOLVED.** `Spec.lean` is unchanged with
its original `sorry`. No settlement has been submitted, and the strongest
multiplicity threshold remains **11116/20001**.

Two new modules, **273 lines and 14 declarations**, have clean fresh builds
and independent permitted-axiom audits:

- `PeriodicCofactorMean.lean`: 188 lines, 11 declarations.
- `PeriodicRelativeCofactorMean.lean`: 85 lines, 3 declarations.

All declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
Both have matching `*Check.lean`; logs are `/tmp/<Module>.log` and
`/tmp/<Module>Check.log`. No repairs/background builds are pending.
The temporary `PeriodProbe.lean` was removed.

### An elementary alternative when the cofactor is long

For every nonnegative arithmetic weight f supported on primes, define

    F(N) = sum_{n<=N} f(n),
    R(N) = sum_{n<=N} f(n)/n.

Exact residue-class counting gives, for each modulus d,

    |restrictedCofactorWeight(f,d,u,0,B,N)-B*F(N)/d|
      <= F(N)+B*restrictedNonunitMass(f,d,N)/d.

Averaging the nonunit correction retains its divisibility structure. Since
f is prime-supported, its all-modulus contribution is bounded by
`H(Q)*R(N)`. The new finite theorem `periodic_prime_cofactor_mean` proves

    sum_{1<=d<=Q} |restrictedCofactorWeight(f,d,u(d),0,B,N)-B*F(N)/d|
      <= Q*F(N)+B*H(Q)*R(N).

If every prime in the support is >=Z>0, then R(N)<=F(N)/Z, hence

    error <= [Q+B*H(Q)/Z]*F(N).

This needs NO lower bound on F(N), no domination f<=Lambda, and no upper
bound on the prime-variable cutoff N. It is useful when B is larger than
the modulus cutoff Q; it complements rather than replaces the product
half-level estimate for a short cofactor.

### Uniform asymptotic corollary

`eventually_periodic_relative_mean` states that for each fixed b and eta>0,
for every sufficiently large m, ALL nonnegative prime-supported weights f
whose support primes are >=cofactorScale(1,m) satisfy relative error

    <= eta*B*F(N)

uniformly for every N, every B>=cofactorScale(b+1,m), and every unit residue
family, with Q=cofactorScale(b,m).

`eventually_periodic_prime_subset_mean` specializes to Lambda restricted to
ANY prime subset above that lower cutoff. The subset is allowed to have
zero or arbitrarily small mass; no positivity claim is hidden in the result.

### Remaining issue

The result still counts a*p=1 mod d with a long averaged cofactor. It does
not supply primality of the successor a*p-1 or remove the a variable. The
large cofactor is exactly what makes residue counting effective. No new
prime-successor lower estimate, smaller smoothness ratio, cofinal moment
lower bound, or full-conjecture proof/disproof was obtained.

Spec SHA-256 remains:
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.

---

## Latest continuation: uniform restricted all-modulus mean and an actual smooth-prime application

**The original conjecture remains UNSOLVED.** `Spec.lean` is unchanged with
its original `sorry`. The best unconditional multiplicity threshold remains
**11116/20001**. No proof or disproof has been submitted.

This continuation proves positive arithmetic estimates, not a new numerical
multiplicity exponent: the restricted-weight primitive mean is completed
over ALL moduli at the product half level, uniformly over the weight. A
relative version is then applied unconditionally to the already constructed
fixed-ratio smooth-prime family.

### Verification

Seven modules, **872 lines and 34 declarations**, were freshly rebuilt in
dependency order and independently axiom-audited. All build logs are empty;
all audits have no warnings/errors and use only `propext`, `Classical.choice`,
and `Quot.sound`. No background build or source repair is pending.

The ordered list is `/tmp/restricted_modules.txt`; each module has a matching
`*Check.lean`. Logs are `/tmp/<Module>.log` and `/tmp/<Module>Check.log`.
`/tmp/restricted_rebuild.log` contains `COMPLETE`.

- `RestrictedPrimitiveMean.lean`: 176 lines, 8 declarations.
- `RestrictedConductorSplit.lean`: 135 lines, 4 declarations.
- `RestrictedCofactorCompletion.lean`: 136 lines, 5 declarations.
- `RestrictedPrincipalMean.lean`: 112 lines, 3 declarations.
- `RestrictedProductMean.lean`: 105 lines, 2 declarations.
- `RestrictedRelativeMean.lean`: 107 lines, 5 declarations.
- `SmoothRestrictedMean.lean`: 101 lines, 7 declarations.

All are in `Erdos821.AnalyticSieve`.

### Uniform restricted-weight product-half-level theorem

For 0<=f(n)<=Lambda(n), let F(X)=sum_{1<=n<=X} f(n). The new
`exists_restricted_product_natural_power_saving` proves that if

    1<=a<=b, 2a+1<=l, b+1<=t, 2b+1<=l+t,

then some K>0, INDEPENDENT OF f, satisfies

    sum_{1<=d<=cofactorScale(b,m)}
      |restrictedCofactorWeight(f,d,u(d),0,B,X)-B*F(X)/d|
      <= K*(m+1)^6/2^m * B*cofactorScale(t,m),

provided cofactorScale(l,m)<=B<=cofactorScale(v,m) and
X<=cofactorScale(t,m). The weights and residue units may vary with m.
The main term uses the actual restricted mass.

The finite small-conductor term retains F(X), and the large-conductor term
retains both character factors. The old divisor-sensitive harmonic
completion and logarithmic lifting error extend to f. The principal-density
replacement likewise retains F(X).

For the final scale bound, the mass-sensitive energy is MAJORIZED by the
original ambient kernel, using F(X)<=X log X. Thus this theorem's error is
still an AMBIENT error; it is not claimed to be automatically small relative
to an arbitrarily sparse restriction.

### Relative version, with the lower-mass hypothesis explicit

At doubled scales, `exists_restricted_relative_power_saving` requires

    cofactorScale(t,2m) <= 2^m * F(X).

It then gives relative error

    <= K*(m+1)^6/2^m * B*F(X).

The constant is again uniform in f. `eventually_restricted_relative_mean`
consequently gives error <=eta*B*F(X), for any eta>0 and all sufficiently
large m, uniformly in f and all the cutoffs/residues satisfying the stated
conditions. `eventually_set_restricted_relative_mean` specializes this to
arbitrary set restrictions of Lambda. Neither theorem proves the mass
hypothesis for an arbitrary set.

### Discharging the mass hypothesis for the actual supplied family

Define `smoothMangoldtWeight(N,Y)` to be Lambda restricted to the actual
prime pool p<=N with p-1 Y-smooth. Its mass is proved equal to the finite
prime-weighted sum and at least half the pool cardinality.

The identities

    cofactorScale(100005,m) = independentN(400020,m),
    cofactorScale(44425,m) = independentN(177700,m)

allow `exists_product_smooth_prime_count` to give the relative theorem's
mass lower bound at doubled scales. This step is UNCONDITIONAL.

The exported `eventually_supplied_smooth_relative_mean` fixes t=100005 and
allows any fixed a,b,l,v meeting the same product-level inequalities. With

    N=cofactorScale(100005,2m), Y=cofactorScale(44425,2m),
    f=smoothMangoldtWeight(N,Y),

it gives eventually, uniformly in the allowed B and u(d),

    sum_{1<=d<=cofactorScale(b,2m)}
      |restrictedCofactorWeight(f,d,u(d),0,B,N)-B*F(N)/d|
      <= eta*B*F(N).

### Scope and remaining gap

This is an actual restricted-prime arithmetic application, but it still
counts a*p=1 mod d with an AVERAGED cofactor a. It does not estimate p=1 mod d
alone, prove a prime-successor lower bound, or improve the smoothness ratio
177700/400020. No cofinal geometric/localized moment lower bound or near-full
structured progression lower bound has been obtained. In particular, the
new relative estimate must not be used to remove the cofactor average.

Spec SHA-256 remains:
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.

---

## Latest continuation: localization equivalence and factorial-sensitive arity audit

**The original conjecture remains UNSOLVED.** `Spec.lean` remains unchanged
with its original `sorry`. No full proof or disproof is available. The best
unconditional multiplicity threshold is still **11116/20001**.

Two new modules were freshly compiled and independently axiom-audited:
**362 lines, 36 declarations**, no warnings or errors, only `propext`,
`Classical.choice`, and `Quot.sound`. Each has a matching `*Check.lean`.
Logs are `/tmp/<Module>.log` and `/tmp/<Module>Check.log`. No repairs or
background builds are pending. The temporary `TempProbe.lean` was removed.

### Localizing does not weaken the cofinal arithmetic input

`LocalizedMomentCriterion.lean` (203 lines, 18 declarations), namespace
`Erdos821.HigherDivisors`, proves a general real-sequence lemma:

    W>=0, 2 W(L)<=W(L+1), W(L)->infinity,
    frequently A(L)>=C W(L), C>0
      => frequently A(L+1)-A(L)>=(C/4) W(L+1).

For the actual moment scales, define

    W(k,t,L) = X(t,L)*log(X(t,L))^(k-2)/k!,
    X(t,L) = 2^(128*t*L).

The scale doubles and tends to infinity. The block difference is proved
to be the actual nonnegative sum of tau_k(p-1) over primes in
`X(t,L)<p<=X(t,L+1)`, not an assumed cancellation expression.

`CofinalLocalizedMomentLower` asks for the theta^k lower bound in such
blocks, at cofinal orders and arbitrarily large scales. It is an UNPROVED
input. The new theorem

    cofinal_localized_iff_geometric :
      CofinalLocalizedMomentLower <-> CofinalGeometricMomentLower

shows that it is equivalent to the previous summatory input. In the
reverse direction choose theta<eta<1 and then k large enough that
`theta^k <= eta^k/4`. The exported
`erdos_821_of_cofinal_localized_moments` remains explicitly CONDITIONAL.
No local prime-moment lower estimate with the needed coefficients was
obtained. Fixed-cutoff Dirichlet-series residue divergence still has no
rate sufficient for this input.

### Important refinement of the previous Poisson-model audit

The earlier `PoissonArityCoefficientModel` proves geometrically small
RAW coefficients. Its conclusion must NOT be read as a geometric deficit
after multiplication by k!: factorial growth changes that conclusion.
The old Lean theorems are correct, but that stronger inference would not be.

`FactorialArityCoefficientModel.lean` (159 lines, 18 declarations), namespace
`Erdos821.ArityModel`, supplies a different, factorial-sensitive model:

    M(r,k,N) = k^r * choose(N+k-1,k-1),
    T(r,N) = 2^r*(N+1).

For each fixed k it proves the exact leading limit

    M(r,k,N)/T(r,N)^(k-1) -> c(r,k),
    c(r,k) = (k/2^(k-1))^r / (k-1)!.

For every r the first two coefficients are both 1, and every positive
order has a positive coefficient. Nevertheless

    k!*c(r,k) = k*(k/2^(k-1))^r,

and its ratio to theta^k tends to zero whenever theta>2^(-r).
For every theta>0 some fixed r>=1 therefore gives an eventual geometric
deficit EVEN AFTER factorial normalization, at all the correct fixed-order
scale powers.

The r=0 model is exactly `tau_k(2^N)`, and the r=1 model is exactly
`tau_k(2^N*3)`. These are genuine divisor weights, but the model does NOT
assert that their arguments have prime successors at arbitrarily large N,
and it is NOT a probability/distribution model of actual shifted primes.
It rules out the stated positivity-and-low-coefficient-only inference,
not arithmetic methods that use more prime-distribution information.
No conclusion against Erdős 821 is drawn.

Spec SHA-256 remains:
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.

---

## Latest continuation: restricted prime weights and the singleton-cofactor obstruction

**The original conjecture remains UNSOLVED.** `Spec.lean` is unchanged,
including its original `sorry`. No full proof or negation has been obtained.
The strongest unconditional exponent remains **11116/20001** from
`ProductMultiplicityGain.lean`; this continuation does not improve it.

### New verified finite results

Two modules, **371 lines and 29 declarations**, were freshly compiled with
empty build logs and independently axiom-audited. Every declaration uses
only `propext`, `Classical.choice`, and `Quot.sound`.

- `RestrictedCofactorWeights.lean` (19 declarations)
- `RestrictedCofactorDiagonal.lean` (10 declarations)

Each has a matching `*Check.lean`; logs are in `/tmp/<Module>.log` and
`/tmp/<Module>Check.log`. No background builds or source repairs are pending.

For an arithmetic function f with 0 <= f(n) <= Lambda(n), define

    F(N) = sum_{1<=n<=N} f(n).

The character orthogonality and exact principal term extend to f. The
principal term is

    coprimeCofactorCount(d,A,B) * (F(N)-nonunitMass(f,d,N)) / phi(d).

The replacement by (B-A)*F(N)/d retains F(N), not the full Mangoldt mass.
Its error is bounded by

    3^omega(d)/phi(d) * F(N)
      + (B-A)*nonunitMass(f,d,N)/phi(d).

The nonunit mass is at most the original logarithmic lifting error.
The character-lifting bound also extends to f. More sharply, the energy is

    sum_{n<=N} |f(n)|^2 <= log(N)*F(N).

`restricted_primitive_maxPrefix_bilinear_bound` consequently has the
adaptive-prefix kernel

    (2+log(B+2)) * sqrt(
      [2Q^2+4(2*pi*B+1)] * [2Q^2+4(2*pi*N+1)] * B*log(N)*F(N)).

This is a FINITE primitive-character bound. A full weighted all-modulus
product-scale completion has NOT been implemented or claimed.

### Why this does not recover the missing lower moment

The cofactor mean counts a*p = 1 mod d, averaged over a. The needed
shifted-prime progression is the SINGLETON a=1. Restricting f does not
remove that extra variable or provide a lower bound on F(N).

`restricted_cofactor_singleton` proves the exact singleton identity, and
`cofactorMaxPrefix_one` shows that its maximal character prefix is exactly
1: there is no cofactor cancellation in that case.

There is also a concrete obstruction to extrapolating the NATURAL main
term B*F(N)/d to B=1. If f is supported on odd integers, then at modulus 2

    restrictedCofactorWeight(f,2,1,0,1,N) = F(N),
    |restrictedCofactorWeight(f,2,1,0,1,N)-F(N)/2| = F(N)/2.

Thus for Q>=2 and positive F(N), the all-modulus natural discrepancy cannot
be <= c*F(N) for c<1/2. This does NOT contradict the exact principal term
F(N)/phi(2), which is correct, and is NOT a disproof of Erdős 821.
`cofactorScale_singleton_excluded` checks that the product-scale hypotheses
already exclude B=1 whenever l,m are positive.

No near-full structured progression lower bound, cofinal geometric moment
lower bound, or arbitrary-root smooth-shifted-prime divergence has been
proved. This route therefore leaves the full-conjecture gap open.

Spec SHA-256 remains:
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.

---

## Latest continuation: product-half-level mean and exponent above 5/9

**The original conjecture remains UNSOLVED.** `Spec.lean` is unchanged,
with its original `sorry`. No complete proof or disproof has been submitted.

The strongest unconditional result is now `ProductMultiplicityGain.lean`:

    infinite_g_gt_product_gain (γ : ℝ) (hγ : γ < 11116/20001) :
      {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite

The new threshold is approximately **0.5557722114**. In particular,
`infinite_g_gt_five_ninths` proves exponent **5/9**, and
`erdos_821_product_range` proves the original conclusion for
**ε > 8885/20001**. This supersedes the 3667/6667 threshold but is NOT
an exponent approaching one.

### Completed modules and verification

This continuation completed **18 modules, 1772 lines, 85 declarations**.
All 18 were freshly rebuilt in dependency order, with empty build logs.
All 85 declarations were then independently axiom-audited, with no audit
warnings/errors and only the permitted axioms `propext`, `Classical.choice`,
and `Quot.sound`. There is no pending repair or background build.

The ordered list is `/tmp/product_modules.txt`. Every module has a matching
`*Check.lean`. Build and audit logs are `/tmp/<Module>.log` and
`/tmp/<Module>Check.log`. The rebuild driver `/tmp/product_rebuild.log`
contains `COMPLETE`; the audit driver log is empty.

- `CofactorMaxPrefix.lean`
- `AdaptivePrefixLargeSieve.lean`
- `CofactorBilinearLargeSieve.lean`
- `CofactorBilinearSplit.lean`
- `CofactorBilinearCompletion.lean`
- `CofactorBilinearKernel.lean`
- `CofactorProductScales.lean`
- `CofactorProductPrimitiveMean.lean`
- `CofactorProductMean.lean`
- `CofactorProductSuccessor.lean`
- `DyadicProductRectangles.lean`
- `DyadicProductHyperbola.lean`
- `ProductCofactorHyperbolicBound.lean`
- `ProductSupplyBudget.lean`
- `ProductSupplyScales.lean`
- `ProductSupplyRoughBound.lean`
- `ProductSmoothPrimeDensity.lean`
- `ProductMultiplicityGain.lean`

### New arithmetic input: retain BOTH character factors

`cofactorMaxPrefix ψ B` is the maximum norm of a primitive character
prefix sum up to B, realized by a selected cutoff. A character-dependent
Fourier cutoff gives the rectangular bilinear large-sieve estimate with
only a `2+log(B+2)` loss. Removing the extra prime factors of an imprimitive
modulus costs at most `2^omega(d)`, absorbed into a fixed subpower bound.

The large-conductor term now retains

    sum_{c in P} 1/φ(c) * sum_{primitive ψ mod c}
      cofactorMaxPrefix(ψ,B) * |sum_{n<=N} Λ(n)ψ(n)|.

A dyadic conductor block D<c<=2D is bounded by

    36*(2+log(B+2))*log(N) *
      [2D*sqrt(B)*sqrt(N) + B*sqrt(N) + N*sqrt(B) + B*N/D].

Conductor divisibility is retained during all-modulus completion, costing
only a harmonic factor. Small conductors still use cancellation of the
UNWEIGHTED cofactor sum alone; no small-conductor prime-sum hypothesis
is assumed. Lifting the Mangoldt factor has its own explicit error.

The exported `exists_cofactor_product_natural_power_saving` proves, for
fixed a,b,l,v,t satisfying

    1<=a<=b, 2*a+1<=l, b+1<=t, 2*b+1<=l+t,

that some K>0 works uniformly in m,B,X and the residue-unit family u(d):

    cofactorScale(l,m) <= B <= cofactorScale(v,m),
    X <= cofactorScale(t,m)

imply

    sum_{1<=d<=cofactorScale(b,m)}
      |cofactorCongruenceWeight(d,u(d),0,B,X) - B*ψ(X)/d|
      <= K*(m+1)^6/2^m * B*cofactorScale(t,m).

Here `cofactorScale(t,m)=2^(256*t*m)`. The NEW level condition is
`2*b+1<=l+t`, replacing the old `2*b+5<=t`: it is a strict half level
of the PRODUCT of the cofactor and prime-variable lengths. The main
term uses the actual cutoff X. This is a mean-discrepancy bound, NOT a
lower bound for prime successors.

### Transfer to the fixed exponent above 5/9

The weighted successor sieve, actual prime-pair conversion and refined
dyadic hyperbola cover are extended to this new mean. The dyadic hyperbola
has the additional condition `H<=2^(2*k)`, used to ensure that the cofactor
prefix is below its permitted upper scale. This condition is checked in
the concrete application; it is not silently omitted.

The initial progression supply remains `widePairPool 100000`, with

    independentN 400020 m <= X <= independentN 400021 m,
    independentN 200000 m <= d <= independentN 200004 m,
    2^(128*100008*m) <= H=X/d <= 2^(128*100011*m).

The NEW smoothness cutoff is `independentN 177700 m`, i.e. lower dyadic
exponent `128*88850*m`. The rejected-prime range is split into three:

1. 88850 to 94000: product-level mean with
   a=1,b=106376,t=200003,l=12750, refinement r=10.
   Normalized budget at most 93/200.
2. 94000 to 100007: old prime-variable half-level mean with
   a=1,b=199999,t=400003,l=3, refinement r=10.
   Normalized budget at most 64/125.
3. Above 100007: existing short-cofactor mixed-root sieve.
   Main budget at most 7/400; error at most 1/10000.

Both long ranges use eta=1/1000000. The scale threshold m>=10000 is
sufficient for the new long-cofactor inequalities. The resulting
`eventually_product_supply_rough_bound` proves

    log(X) * #roughProgressionPrimes(d,independentN 177700 m,X)
      <= (199/200)*X/φ(d).

A bounded-enlargement Mangoldt cutoff with slope 999/1000 is selected.
The two existing progression/prime-power errors are each charged at
N*V/10000, and the incidence cap remains 16. This gives the single-log
smooth-prime supply `exists_product_smooth_prime_count`, and hence the
11116/20001 multiplicity threshold.

### Remaining gap and mathematical review

The all-order moment review did not recover the missing near-full
coefficient. Exact divisor switching still exposes moduli reaching X;
it does not itself estimate their signed prime-progression deficit.
No `CofinalGeometricMomentLower`, `CofinalNearFullStructuredLower`, or
arbitrary-root smooth-predecessor series divergence has been established.

A formal parametric limit of the new method is NOT proved. Informally,
optimizing the cofactor ratio continuously and making the tail negligible
suggests the rejected budget `8*log((1/2)/beta)`, whose positivity threshold
is beta>(1/2)*exp(-1/8). The corresponding multiplicity limit would be
about 0.55875155. This heuristic is still bounded away from one and is
not a settlement or a general impossibility result for other methods.

During cleanup, replacing a needed `<;> ring` by `; ring` left a second
conversion goal in `CofactorProductScales`. The fresh rebuild caught this;
it was repaired and the ENTIRE rebuild and audit were repeated successfully.
No stale-object result is being reported as a fresh successful build.

Spec SHA-256, independently rechecked:
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.

---

## Latest continuation: verified successor sieve and exponent 3667/6667

**The original conjecture remains UNSOLVED.** `Spec.lean` is unchanged,
with its original `sorry`. No settlement is available for submission.

The strongest unconditional result is now in `SuccessorMultiplicityGain.lean`:

    infinite_g_gt_successor_gain (γ : ℝ) (hγ : γ < 3667/6667) :
      {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite

Thus exponent 11/20 = 0.55 is included. The original conclusion is proved
only for ε > 3000/6667, not for every positive ε.

This continuation completed 22 modules, 2224 lines, 111 declarations.
All modules were freshly rebuilt in dependency order; all build logs were
empty. All declarations were independently axiom-audited, with only
`propext`, `Classical.choice`, and `Quot.sound`. No repair or build is pending.
Each module has a matching `*Check.lean`; logs are `/tmp/<Module>.log` and
`/tmp/<Module>Check.log`. The ordered list is `/tmp/successor_modules.txt`.

Modules, in dependency order:

- `OneRootDenominator.lean`
- `CofactorSuccessorSieve.lean`
- `CofactorSuccessorScales.lean`
- `UniformCofactorMean.lean`
- `UniformCofactorNaturalMean.lean`
- `CofactorSuccessorIntervals.lean`
- `UniformSuccessorIntervalScales.lean`
- `CofactorPrimePairCover.lean`
- `DyadicSuccessorScales.lean`
- `DyadicPrimePairRectangles.lean`
- `RefinedDyadicPartition.lean`
- `DyadicMangoldtMass.lean`
- `DyadicMangoldtTail.lean`
- `DyadicHyperbolicPrimePairs.lean`
- `LongCofactorHyperbolicBound.lean`
- `ShortCofactorHyperbolicBound.lean`
- `RoughHyperbolicSuccessors.lean`
- `SuccessorSupplyBudget.lean`
- `SuccessorSupplyScales.lean`
- `SuccessorSupplyRoughBound.lean`
- `SuccessorSmoothPrimeDensity.lean`
- `SuccessorMultiplicityGain.lean`

### Arithmetic content

The one-root Selberg denominator is bounded below by (φ(c)/c)*log(z+1),
uniformly in every positive coefficient c. The weighted sieve is applied
to prime successors c*a*q+1, retaining actual Mangoldt interval masses.
Uniform cofactor progression means now allow every initial cutoff below
an ambient scale. A fixed-refinement dyadic cover of a hyperbola loses
only 1+1/R. A harmonic Mangoldt asymptotic and summation by parts charge
the endpoint error after summing all dyadic blocks, at order 1/K².

The new long-cofactor bound has leading coefficient tending to four.
A separate mixed-root pair sieve handles the short-cofactor tail.
Mapping rejected progression primes to hyperbolic prime pairs yields,
uniformly at the fixed scales in `SuccessorSupplyScales.lean`,

    log(X) * #roughProgressionPrimes(d,Y,X) ≤ (97/100)*X/φ(d).

The existing wide-pair progression supply, prime-power removal and
incidence cap then give a single-log lower bound for smooth primes,
with X = independentN 400020 m and Y = independentN 180000 m.
This transfers to every multiplicity exponent below 3667/6667.

### Follow-up review and fresh final-result audit

The continuation after the checkpoint reviewed the exact smooth-series
characterizations, the cofinal moment and structured-modulus criteria,
and the finite-fiber LCM/record/overlap route. No new sufficient arithmetic
lower bound or multiplicity-exponent amplification was obtained. In
particular, record overlap UPPER bounds are not a supply of the large-overlap
pairs required by LCM amplification. This is a review, not a mathematical
impossibility result and not a new theorem.

`lake env lean Submission/SuccessorMultiplicityGainCheck.lean` was rerun
successfully. Its four audited declarations again report only the permitted
three axioms. The fresh log is
`/tmp/SuccessorMultiplicityGainContinuationCheck.log`.
The Spec hash was independently rechecked and remains unchanged.
No complete proof/disproof is ready, and no submission call has been made.

### Remaining full-conjecture gap

No supply reaching arbitrarily small predecessor-smoothness ratios has
been established. A parametric version of the present budget might give
every exponent below 5/9, but this is unproved and would remain partial.
The heuristic limiting rejected budget is 4*(1/β-2), requiring β>4/9.

The earlier single-log charged-refinement ceiling remains relevant:
an improvement at every step does not imply a cutoff approaching zero.
`CofinalNearFullStructuredLower` and `CofinalGeometricMomentLower` are
still unproved sufficient inputs for the full conjecture. Fixed-modulus
shifted Dirichlet-series lower bounds have cutoff-dependent error and do
not supply the required critical pole rate. The exact factorial moment
coefficient below half level is constrained by 2*(b*r)+5 ≤ t.

A possible new extension (NOT developed) is to retain both cofactor and
Mangoldt factors in the bilinear large-sieve mean. The API
`bilinear_characterSum_large_sieve` is available. A product-half-level
mean would still not automatically settle the original conjecture.

Spec SHA-256:
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.

---

## Latest continuation: verified weighted Selberg error completion

**The conjecture remains UNSOLVED.** `Spec.lean` has not been changed.
No proof or disproof is available for submission.

The pending error in `WeightedPrimeSelberg.lean` was repaired by qualifying
real `add_le_add` as `_root_.add_le_add`. The following three modules now
compile, with all 13 declarations independently axiom-audited:

- `WeightedSieveKernel.lean`: 4 lemmas. A weighted upper sieve retaining
  the sum of each support-pair discrepancy times its weight.
- `SieveUnionError.lean`: 5 lemmas/theorems. Grouping support pairs by their
  union costs at most `16^card(U)`; injective prime support products and a
  uniform subpower bound absorb this into `C*Q^epsilon` times the sum of
  discrepancies over all positive moduli up to Q.
- `WeightedPrimeSelberg.lean`: 4 declarations. The one-root weighted
  Selberg upper bound with an averaged progression error, uniform over
  the prime pool, sequence, nonnegative weights, and residue conditions.

Each module has a matching `*Check.lean`. Audit logs are
`/tmp/<Module>Check.log`; every audited declaration uses only
`propext`, `Classical.choice`, and `Quot.sound`. The temporary
`WeightedSieveProbe.lean` was removed. No pending repair is known.

The exported `Erdos821.Sieve.exists_weighted_selberg_mean_bound` proves

    sifted weighted mass <= X / oneRootDenominator(P,z)
      + C*(z^2)^epsilon * sum_{1<=d<=z^2} R(d),

assuming the simultaneous bad-condition count for each relevant prime
support U differs from `X/prod(U)` by at most `R(prod(U))`.

This preserves the previous cofactor progression mean's power saving
when epsilon is chosen sufficiently small. It is still an UPPER-sieve
bound, not a lower bound for prime successors. A sharp one-root denominator
estimate, an application to linear successors, and the variable-cutoff /
hyperbolic range extensions remain unproved in this continuation. More
fundamentally, no supply reaching arbitrarily small predecessor-smoothness
ratios has been established. The strongest unconditional multiplicity
threshold remains **2303/4351**, not the full conjecture.

The original Spec SHA-256 remains
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.

---

## Latest continuation: a power-saving ALL-MODULUS cofactor-averaged progression mean

**The original conjecture remains UNSOLVED.** The strongest unconditional
multiplicity threshold remains **2303/4351**. No proof/disproof is available
for submission; `Spec.lean` is unchanged with its original sorry and hash
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.

Unlike the preceding refinement-budget checks, this continuation establishes
new positive arithmetic input: averaging over a polynomially long COFACTOR
interval removes the small-conductor obstruction in a strict-half-level
all-modulus progression mean for the cofactor times a Mangoldt-weighted
variable. It is NOT a prime-only distribution theorem or a prime-pair lower
bound, and has not yet produced a new smooth-prime count.

### Verified modules and current build state

Ten new modules, **1429 lines**, with **77 declarations** independently
audited:

- `CofactorCharacterCancellation.lean`: 167 lines, 11 declarations.
- `CofactorAveragedProgression.lean`: 143 lines, 8 declarations.
- `CofactorConductorSplit.lean`: 165 lines, 8 declarations.
- `CofactorSmallConductorMean.lean`: 136 lines, 6 declarations.
- `CofactorLargeConductorMean.lean`: 142 lines, 5 declarations.
- `CofactorAllModulusMean.lean`: 121 lines, 8 declarations.
- `CofactorMeanScales.lean`: 206 lines, 14 declarations.
- `CofactorPrincipalCount.lean`: 133 lines, 8 declarations.
- `CofactorPrincipalMean.lean`: 104 lines, 6 declarations.
- `CofactorNaturalMean.lean`: 112 lines, 3 declarations.

Each has a matching `*Check.lean`. All ten were freshly rebuilt in dependency
order, then the independent audits were rerun in parallel. All result logs
are empty; all audit logs have no warnings/errors and only permitted axioms
{propext, Classical.choice, Quot.sound}. Logs are `/tmp/<Module>.log` and
`/tmp/<Module>Check.log`. No source repair or background build is pending.
The temporary API probes `CofactorCancellationProbe`, `CofactorMeanProbe`,
and `CofactorScaleProbe` were removed.

All new declarations are in namespace **Erdos821.AnalyticSieve**.

### Main completed result: multiplicative main term, explicit power saving

Define

    cofactorScale(t,m) = progressionScaleN(t*(4*m)) = 2^(256*t*m).

For a unit u modulo d, `cofactorCongruenceWeight d u A B N` is the REAL sum

    sum_{A<a<=B} sum_{1<=n<=N} Lambda(n) * 1_{u*a*n = 1 mod d}.

The cofactor a is unrestricted apart from the interval; n is weighted by
von Mangoldt, so prime powers are included. This must not be described as
an estimate for primes alone or as a supply of prime pairs.

`exists_cofactor_natural_main_power_saving` in `CofactorNaturalMean` proves:
for FIXED natural a,b,t,l satisfying

    1<=a<=b,  22<=t,  2*b+5<=t,  2*a+1<=l,

there exists a fixed K>0 such that for EVERY m,A,B with

    L = B-A >= cofactorScale(l,m),

and EVERY family of units u(d), setting

    Q=cofactorScale(b,m),  N=cofactorScale(t,m),

one has

    sum_{1<=d<=Q} |cofactorCongruenceWeight(d,u(d),A,B,N)
                    - L*psi(N)/d|
      <= K*(m+1)^6/2^m * L*N.

Thus the residue choices AND the interval endpoints may vary with m.
EVERY positive modulus d<=Q is included: there is no roughness restriction
on its prime factors. The upper modulus cutoff is still strictly below
the square-root level of the PRIME-WEIGHTED variable N. The primitive
conductor cutoff is R=cofactorScale(a,m), and the cofactor interval has a
fixed positive power length. No prime-counting asymptotic is assumed;
psi(N) is the ACTUAL Mangoldt mass.

The earlier `exists_cofactor_all_modulus_power_saving` in `CofactorMeanScales`
has the same error but the exact principal term

    coprimeCofactorCount(d,A,B)*(psi(N)-nonunitMangoldt(d,N))/phi(d).

`eventually_cofactor_all_modulus_relative_error` gives an arbitrary fixed
relative error delta>0 for that exact principal term. The stronger exported
power-saving estimate is available for later use with sieve weights.

### Why small conductors can now be handled

`cofactor_character_interval_bound` proves for a NONPRINCIPAL character chi
modulo d, of actual conductor c,

    |sum_{A<a<=B} chi(a)| <= 2^omega(d)*sqrt(c)*(1+log c).

The proof starts from the previously verified primitive Pólya--Vinogradov
bound. Removing one prime from the cofactor interval costs at most a factor
two. Multiples are reindexed exactly, including floor endpoints, and all
primes of d are then removed to obtain a lifted character. The bound is
uniform in A,B and the growing lifted modulus d.

`exists_uniform_cofactor_character_bound` absorbs 2^omega(d) into C*d^epsilon.
This is cancellation of an UNWEIGHTED cofactor sum. It does NOT assume any
small-conductor cancellation for Mangoldt sums.

`cofactor_congruence_orthogonality` keeps that cofactor sum inside the
character expansion before applying absolute values. The nonprincipal
remainder contains

    |sum_{A<a<=B} chi(a)| * |sum_{n<=N} Lambda(n)*chi(n)|.

For small conductors the second factor is bounded trivially by psi(N),
while the first factor supplies the saving independent of L=B-A.

### Finite conductor split and completion over all moduli

`cofactor_nonprincipal_conductor_split` retains three terms:

1. `2^omega(d)*psi(N)*smallConductorCofactorWeight(d,R)`, where

       smallConductorCofactorWeight(d,R)
         = sum_{c|d, 1<c<=R} c*sqrt(c)*(1+log c).

2. `L*largePrimitiveConductorMangoldt(d,R,N)`, the sum of primitive
   Mangoldt norms at divisors c>R of d.
3. `L*d*characterLiftError(d,N)`.

All are divided by phi(d) in the discrepancy estimate. The generic
`nonprincipal_sum_le_primitive_lifts` cover was also proved; no unproved
injectivity or conductor-preservation assertion is used in that cover.

The divisor constraint c|d is crucial when summing over d. The completed
small-conductor estimate is, for every epsilon>0 and a fixed C,

    sum_{d<=Q} 2^omega(d)/phi(d)*smallConductorCofactorWeight(d,R)
      <= C*Q^epsilon*H_Q*R*sqrt(R)*(1+log R).

It does NOT pay a factor Q for the small conductors. The elementary proof
uses d/phi(d)<=2^omega(d), a fixed subpower bound for 4^omega(d), and
sum_{d<=Q,c|d}1/d <= H_Q/c. The factor c in the conductor weight cancels.

Similarly the large-conductor completion is bounded by

    C*Q^epsilon*H_Q*primitivePoolMean(Ioc R Q,N).

`primitive_full_interval_mean_bound` subdivides the entire conductor
interval into adjacent logarithmic blocks and applies the existing
`wide_primitive_mean_bound` to each. Under 2*b+5<=t, it gives

    primitivePoolMean(Ioc N_a(m) N_b(m), N_t(m))
      <= (b-a)*wideMeanConstant(t)*(m+1)^5*2^((64*t-1)*m).

Here N_t(m)=progressionScaleN(t*m). This handles all conductors in the
interval, not only prime-product conductor pools.

`exists_cofactor_all_modulus_mean_bound` combines the finite estimates:

    sum discrepancy <= C*Q^epsilon *
      [psi(N)*H_Q*R*sqrt(R)*(1+log R)
       + L*H_Q*primitivePoolMean(Ioc R Q,N)
       + L*Q*(Nat.log 2 N)*log Q].

At the cofactorScale grid, epsilon=1/(256*b) makes Q^epsilon=2^m. The
primitive mean is applied at scale 4*m, retaining 2^(-4*m). The hypotheses
L>=cofactorScale(l,m), l>=2*a+1 absorb the small-conductor term; the lift
error is also power-saving. The exported loss is K*(m+1)^6/2^m.

### Replacing the exact principal cofactor count

`coprimeCofactorCount_density_error` proves

    |coprimeCofactorCount(d,A,B)-L*phi(d)/d| <= 3^omega(d).

This follows by deleting primes one at a time and retaining the exact
floor-interval length error. Using the number of reduced residue classes
instead would have lost too much. The base three is absorbed by the
proved general local-factor subpower bound.

`exists_cofactor_principal_mean_bound` proves

    sum_{d<=Q} |exactPrincipalMain(d)-L*psi(N)/d|
      <= C*Q^epsilon*H_Q*[psi(N)+L*(Nat.log 2 N)*log Q].

Its scale specialization is again K*(m+1)^6/2^m*L*N, which gives the main
completed theorem above by the triangle inequality.

### Active next route — NOT YET IMPLEMENTED

Use the all-modulus mean to sieve the LINEAR SUCCESSOR of a cofactor times
a prime, instead of sieving both prime conditions on an integer sequence.
This could sharpen the averaged upper bound used to remove rough shifted
primes. It is not yet a new smooth-prime count, and even an improved fixed
sieve constant would not by itself prove arbitrary epsilon in Erdős 821.

Concrete remaining steps:

1. Derive a weighted version of the finite Selberg bound using
   `weighted_square_sum_expansion` (in Sieve) and
   `exists_selberg_weights_local` (in SharpSelbergWeights).
2. Group pairs of sieve-weight supports by their union before using the
   progression mean. The number of pairs and the local weight bound can
   be bounded by B^omega(d) for a FIXED B, then absorbed by the subpower
   estimate. Do NOT multiply the unweighted mean by the total number of
   sieve-support pairs; that would lose the saving.
3. Establish the one-root denominator lower bound with the sharp half-log
   coefficient when sifting odd primes. The existing
   `sum_exact_prime_support_multiplicative_le` infrastructure, used in
   `MixedSieveDenominator`, may be reusable. The relevant harmonic mass is
   the sum over odd integers, at least half the full harmonic sum.
4. Apply to the condition `2*D*a*q+1` prime, retaining prime powers and
   small-prime exceptions correctly. If D is sufficiently rough, all
   relevant odd sieve moduli are coprime to 2*D, so the residue is a unit.
5. For the actual hyperbolic cofactor range, interval decomposition and/or
   uniform variable prime cutoffs are still needed. The newly exported
   mean is currently on the fixed geometric N grid, NOT at every N.
   A maximal-variable-cutoff extension must be justified from the existing
   primitive-character mean theorem, not assumed.
6. Integrating the actual Mangoldt masses over variable prime intervals
   might avoid losing a pointwise Chebyshev constant, but this has NOT been
   proved or used here. No numerical coefficient improvement is claimed.

The higher-divisor moment review at the start of this continuation found
no way to remove the previously documented cofactor correlation gap.
The all-modulus mean is a DIFFERENT, cofactor-averaged arithmetic input; it
must not be substituted for the missing prime-only near-full distribution
or critical higher-divisor moment hypothesis.

## Latest continuation: accumulated refinement budget and converted-density ceiling

**The original conjecture remains UNSOLVED.** `Spec.lean` is unchanged, with
its original sorry and hash
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No proof/disproof is available for submission. The strongest unconditional
multiplicity threshold remains **2303/4351**.

### Verified modules

- `CutoffRefinementBudget.lean`: 102 lines, 8 declarations.
- `SingleLogRefinementCeiling.lean`: 136 lines, 6 declarations.

Both have freshly compiled oleans and matching `*Check.lean` files. All
**14** declarations have been independently axiom-audited and use only
{propext, Classical.choice, Quot.sound}. The build logs are empty; the audit
logs contain no warnings/errors. Logs are `/tmp/<Module>.log` and
`/tmp/<Module>Check.log`. No source repair or background build is pending.
The temporary API probe `TmpCheck.lean` was removed.

### Accumulated cost of the actual proved refinement rule

`smoothPrimeLogMass_le_mangoldtSum` proves the pointwise upper bound on
weighted smooth prime mass by the full Mangoldt mass. Thus any normalized
weighted density at a positive-Mangoldt scale is at most one; an eventual
version handles the geometric scales used in this project.

In namespace `Erdos821.CutoffRefinementBudget`, for sequences of positive
ratios beta(i) and nonnegative retained densities c(i), assume

    log(beta(i)/beta(i+1)) <= c(i)-c(i+1).

Then `potential_monotone` proves that log(beta(i))-c(i) is monotone, and
`cutoff_lower_bound` gives for every n

    beta(n) >= beta(0)*exp(-c(0)).

The density-halving schedule is a special case.
`not_tendsto_cutoff_zero` explicitly rules out convergence to zero under
these hypotheses. With an initial ACTUAL normalized prime supply,
`cutoff_lower_bound_of_prime_supply` weakens the floor to beta(0)/e using
c(0)<=1.

**Scope:** this restricts chains satisfying the explicit charged sufficient
conditions. It is not an upper bound on the actual smooth-prime supply,
not a disproof of the conjecture, and not an obstruction to obtaining fresh
arithmetic density estimates by another method.

### Could one refinement nevertheless cross the current finite-local limit?

This possibility needed a separate check: merely saying the density tends
to zero at the limiting ratio does not logically rule out such a crossing.
The new check concerns the EXACT conversion currently proved in
`weighted_supply_of_single_log_count`, namely c(0)=1/(12*C).

`single_log_count_constant_lower` uses Mathlib's elementary Chebyshev
upper bound for the unrestricted prime count to prove that any eventual
single-log count

    N_t(m) <= C*m*card(smoothPrimePool(N_t(m),N_b(m)))

with t,C>=1 necessarily has **t<=4*C**. Consequently, the converted density
is strictly less than 1/t. The elementary inequality exp(-c)>=1-c then
shows that a starting ratio separated from a target by at least 1/t stays
strictly above that target under every charged refinement chain.

For the finite-local parametric family, with A=2*N+M,

    t=4*A*k+20,  b=4*N*k+21,

`finite_local_parametric_ratio_gap` proves

    N/A <= b/t-1/t.

For N=2048*D and M=255*(D-1), D>=2,
`finite_local_parametric_ratio_ge_limit` proves N/A>=2048/4351.
Combining these, `finite_local_converted_refinement_above_limit` proves
that EVERY charged chain starting from this family's ratio with the
converted initial density 1/(12*C) stays **strictly above 2048/4351**.

This is stronger than a statement that the current argument fails to
justify crossing: it is a formal restriction on this particular set of
certificates. **It does not exclude a stronger count-to-weight conversion,
a stronger direct weighted density, or a new prime-distribution argument.**
In particular it does not establish any new upper bound on g or on actual
smooth-prime counts.

### Remaining task

A full settlement still needs genuinely new arithmetic information, such
as the unproved near-full structured progression supply or the critical
higher-divisor moment criterion documented below. No such input was
established in this continuation, and no exponent above the prior
2303/4351 threshold was obtained.

## Latest continuation: actual-prime cutoff continuity and strict fixed-supply refinement

**The original conjecture remains UNSOLVED.** The strongest numerical
unrestricted exponent threshold is still 2303/4351. Spec.lean is unchanged,
with its original sorry, and no complete proof/disproof has been submitted.

### Verified new modules

Two new modules, **328 lines**, freshly rebuilt and independently audited:

- `SmoothCutoffContinuity.lean` (9 declarations)
- `DensityCutoffRefinement.lean` (6 declarations)

All **15** declarations depend only on {propext, Classical.choice, Quot.sound}.
Each has a matching `*Check.lean`; all result logs are empty, and all audit
logs have no warnings/errors. Logs are `/tmp/<Module>.log` and
`/tmp/<Module>Check.log`. No source repair or background build is pending.

### Actual arithmetic continuity estimate

Define `smoothPrimeLogMass(N,Y)` as the sum of log(p) over p<=N prime
with Y-smooth predecessor. A finite first-moment inequality proves that
lowering a smoothness cutoff from B to A loses at most the log-weighted
incidences of prime factors q in [A,B).

The previously verified exact first-binomial-moment theorem then gives:
for fixed 1<=a<=b, t>=22, **2*b+5<=t**, and any c>log(b/a), eventually m,

```
smoothPrimeLogMass(N_t(m),N_b(m))
  <= smoothPrimeLogMass(N_t(m),N_a(m)) + c*psi(N_t(m)).
```

Here N_t(m)=2^(64*t*m). This is a statement about ACTUAL shifted primes,
not an abstract model. The normalization is the actual Mangoldt mass.
The endpoint q=N_a(m) is handled by the fact that these powers of two
are not prime at m>=1, so the available open-lower power interval applies.

`smoothPrimeLogMass_transfer` retains a lower weighted density d from
an original density c whenever log(b/a)<c-d. No distribution-level
extension is used.

### A strictly smaller cutoff for every fixed positive weighted supply

`exists_strictly_smaller_weighted_cutoff` chooses a FIXED K>=2 so that

```
log((b*K)/(b*K-1)) < c/2.
```

After restricting the original eventual scale to K*m, it gives eventually

```
(c/2)*psi(N_(t*K)(m))
  <= smoothPrimeLogMass(N_(t*K)(m),N_(b*K-1)(m)).
```

The new ratio (b*K-1)/(t*K) is strictly smaller than b/t. The weighted
density has been HALVED; this loss is explicit, not silently reset.

### Conversion from and back to single-log count bounds

`weighted_supply_of_single_log_count` proves that, for t>=2 and C>0,

```
eventually N_t(m) <= C*m*card(smoothPrimePool(N_t(m),N_b(m)))
```

implies a normalized weighted lower density **1/(12*C)**.
The proof separates p<=N_(t-1)(m), bounds their number by that cutoff,
and absorbs the resulting m*N_(t-1)(m) by the existing power-saving lemma.
It also proves the elementary global psi(N)<=6*N bound from Chebyshev.

Conversely, `single_log_count_of_weighted_supply` turns any fixed positive
weighted density into an eventual single-log count, with a new fixed
natural constant. Only the already proved psi>=0.9*N eventual lower bound
and log(N_t(m))<=64*t*m are used.

Consequently:

- `exists_smaller_cutoff_single_log_count` strictly decreases the rational
  smoothness ratio of ANY FIXED supplied single-log count below the half
  level, while allowing its count constant to increase.
- `exists_larger_exponent_of_single_log_count` yields some gamma STRICTLY
  larger than 1-b/t with infinitely many g(n)>n^gamma, from that fixed
  supply.

### Important scope: no uniform iteration or improvement of the supremum

This is a strict improvement relative to EACH PARTICULAR supplied ratio.
It is NOT a proof of an exponent beyond 2303/4351, since the density/count
constants are not uniform as the old ratios approach their limiting value.
A strict pointwise improvement need not improve a supremum.

The initial investigation of typical output capacities suggested using
large-prime incidences. The verified result above uses the simpler direct
removal bound instead; no unproved independence, Shannon-entropy estimate,
or conditional prime-factor distribution inside the smooth pool is assumed.

Informally, repetitions that halve weighted density and charge less than
c_i/2 in logarithmic ratio decrease have total charged decrease bounded by
the initial density c_0. They do not justify ratios tending to zero. This
observation is a scope check, not a theorem excluding other refinements.
The near-full progression and critical higher-moment inputs remain missing.

Spec SHA-256 remains
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.


## Latest continuation: all finite local factors and exponent above 0.5293

**The original task is still UNSOLVED.** The new strongest unconditional
result is in `Submission/FiniteLocalLimit.lean`:

```lean
Erdos821.infinite_g_gt_finite_local_limit (γ : ℝ)
    (hγ : γ < 2303/4351) :
  {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite
```

Here **2303/4351 = 0.5293036083658929...**, improving the prime-three-only
threshold 29599/56223 = 0.5264571438735037....
`infinite_g_gt_point_five_two_nine_three` attains 5293/10000 = 0.5293.
`erdos_821_finite_local_range` proves the original conclusion for

```
ε > 2048/4351 = 0.4706963916341071...
```

This remains a fixed positive lower threshold on epsilon, NOT the full
original quantifier. Spec.lean is unchanged with its original sorry.
No proof/disproof has been submitted.

### Verification

Nine new modules, **1337 lines**, were freshly rebuilt in dependency order.
All **65** definitions/lemmas/theorems were independently axiom-audited,
and each axiom list is a subset of {propext, Classical.choice, Quot.sound}:

- `FiniteLocalDenominator.lean` (10 declarations)
- `FiniteLocalProducts.lean` (13)
- `FiniteLocalAverage.lean` (10)
- `FiniteLocalPrimePair.lean` (5)
- `FiniteLocalCofactorMass.lean` (6)
- `FiniteLocalCofactorSieve.lean` (4)
- `FiniteLocalBlockSieve.lean` (8)
- `FiniteLocalDensity.lean` (3)
- `FiniteLocalLimit.lean` (6)

Each has a matching `*Check.lean`. All result logs are empty; all check
logs have no warnings/errors. Logs are `/tmp/<Module>.log` and
`/tmp/<Module>Check.log`. No source repair or background build is pending.

### Generic finite local-factor comparison

For an odd prime q, define

```
singularCorrection(q) = q*(q-2)/(q-1)^2,
finiteLocalCorrection(Q,a) = product_{q in Q} (if q|a then 1 else singularCorrection(q)),
finiteLocalLength(Q) = sum_{q in Q} q.
```

Every local correction is positive and <=1. For any fixed finite pool Q
of odd primes, the exact denominator lower bound is

```
(phi(a)/a) * ((L-finiteLocalLength(Q))*log 2)^2 / 2
  <= finiteLocalCorrection(Q,a) * mixedPairDenominator(a,2^L,primes<=2^L),
```

for positive even a and L>=finiteLocalLength(Q).
The proof inducts over Q, using the already verified truncated-product
comparison at each prime q, coefficient q*a, and reference length L-q.
The length loss is coarse but FIXED before L grows.

The prime-pair theorem retains this correction while preserving the
1020*J^2 squared denominator and existing exponential error budget. Its
explicit eventual length threshold is J>=100*(finiteLocalLength(Q)+1).
The ambient endpoint theorem is uniform over coefficients and cutoffs
as before; the correction does not increase the endpoint error.

### Exact cancellation of the retained Euler factors

Put

```
w_Q(p) = if p in Q then 1/(p-2) else 1/(p-1),
C_Q = product_{q in Q} singularCorrection(q).
```

The corrected even reciprocal-totient weight has the exact identity

```
finiteLocalCorrection(Q,2*n)/phi(2*n)
  = C_Q/n * product_{p|n,p!=2} (1+w_Q(p)).
```

At every retained q, the averaged factor cancels:

```
singularCorrection(q) * (1+1/(q*(q-2))) = 1.
```

Consequently, when Q is contained in an averaging pool P, the corrected
average Euler product equals the product of the ORIGINAL factors over
P minus Q, with no retained factors remaining. The endpoint product is
no larger than the original endpoint product.

Take Q to be all odd primes <=D, where D>=2 is fixed. A telescoping upper
bound on the unretained prime sum gives, for every averaging endpoint B>=D,

```
corrected average Euler product <= exp(1/D) <= D/(D-1).
```

`localAverageConstant D = D/(D-1)` therefore tends to one. Both the direct
INTERVAL and separate PREFIX estimates are proved. The latter handles the
first exponential block; no difference of prefix upper bounds is used.
The endpoint error remains exp(primeTotientMass B)/A.

### Propagation and quantifiers

For each fixed D>=2, all cofactor blocks eventually have corrected mass
at most

```
localAverageConstant(D)*(1+64*m*log 2).
```

The wide pair moduli have no prime divisor <=D once m>=D, by their
previously verified roughness. Therefore the local correction of d*k
reduces exactly to the correction of k. The block main coefficient is

```
(2048/255)*localAverageConstant(D).
```

The bounded-ratio unit-slope cutoff argument and uniform progression error
bounds remain unchanged. There is NO distribution-level improvement or
interchange of the fixed local cutoff with the growing scale.

For a given target gamma<2303/4351, choose D FIRST, then set

```
N=2048*D,
M=255*(D-1).
```

Choose a second fixed integer k>=1 and use

```
a=(2*N+M)*k,
t=4*(2*N+M)*k+20,
b=4*N*k+21,
c=4*N*k+16,
h=2*M*k.
```

The cleared budget margin is exactly

```
(72*N+28*M)*k + 196 > 0.
```

The limiting complementary ratio at fixed D is (N+M)/(2*N+M), which
approaches 2303/4351 as D increases. The proof chooses D and k explicitly
by strict real inequalities, and ONLY THEN applies the eventual scale
bound. The fixed enlargement is absorbed by the existing fixed-shift lemma.

### Remaining scope

All finite local factors have now been accounted for in this average.
The fixed 1020 squared-denominator approximation still has slight slack
relative to 32^2=1024. Removing only that slack would at most make the
corresponding formal budget approach 9/17, still far below one; no theorem
with that newer threshold has yet been proved. The strict half-level
progression restriction remains unchanged.

The cofinal near-full structured progression estimate, critical high-order
shifted-prime moment input, and root-3 endpoint series are all still unproved.
No full settlement or exponent-increasing iteration follows from the
fixed-constant improvement.

Spec SHA-256 is still
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.


## Latest continuation: averaged arity coefficients do not bootstrap by positivity alone

**The original conjecture remains UNSOLVED.** The strongest unconditional
multiplicity result is still `infinite_g_gt_three_unit_slope_limit`, with
threshold 29599/56223. No proof/disproof has been submitted, and Spec.lean
is unchanged with its original sorry.

### Scale-averaging review

Rechecked `ShiftedDivisorPole`, `ShiftedPrimeMomentPole`, and
`CofinalMomentCriterion`. The fixed-modulus lower bound still has an error
constant depending on the divisor cutoff Q, with no bound on that dependence.
Its consequence `(s-1)*shiftedPrimeDirichlet(k,s) -> infinity` has no rate.
It cannot simply be substituted for the critical higher-order pole/moment
bound. Choosing a cutoff growing with the analytic scale would require a
new uniform estimate, not a quantifier exchange. No such estimate was found.

### New verified abstract averaged model

`Submission/PoissonArityCoefficientModel.lean` (136 lines) compiles cleanly.
Its 17 definitions/lemmas/theorems are independently axiom-audited in
`PoissonArityCoefficientModelCheck.lean`, and every axiom list is a subset
of {propext, Classical.choice, Quot.sound}. Result log
`/tmp/PoissonArityCoefficientModel.log` is empty; the corresponding Check
log has no warnings/errors. No source repair or build is pending.

For a nonnegative real rate mu, use the genuine nonnegative Poisson weights

```
w_mu(n) = exp(-mu)*mu^n/n!,    sum_n w_mu(n)=1.
```

For each fixed natural forced arity r, define

```
M_r(k,mu) = sum_n w_mu(n)*k^(n+r),
T_r(mu) = 2^r*exp(mu).
```

The verified exact identity, at every k>=1, is

```
M_r(k,mu)/T_r(mu)^(k-1) = (k/2^(k-1))^r.
```

Thus every positive order has exactly the corresponding scale power and
a positive coefficient. Nevertheless:

- the coefficients at k=1 and k=2 are BOTH exactly 1;
- the coefficient at k=3 is (3/4)^r, so normalized log-convexity fails
  for every r>=1;
- for fixed r and every theta>2^(-r), the coefficient divided by theta^k
  tends to zero as k tends to infinity;
- consequently, for ANY theta>0, some fixed r>=1 has first two coefficients
  one but all sufficiently high coefficients less than theta^k, uniformly
  in the scale parameter mu.

The last assertion is
`Erdos821.ArityModel.exists_positive_model_with_small_geometric_coefficients`.

This model addresses an AVERAGED shortcut, unlike the previous pointwise
n=6 counterexample. It is NOT a model of actual primes, does NOT assert
that shifted-prime moments have these coefficients, and does NOT disprove
Erdős 821. It only shows that positivity, correct scale powers, and the first
two leading coefficients do not by themselves force the required higher
coefficient lower bounds. No new estimate on actual shifted primes follows.

Spec SHA-256 remains
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.


## Latest continuation: exact prime-three correction and exponent above 0.52645

**The original task remains UNSOLVED.** `Submission/Spec.lean` is unchanged,
with its original `sorry`. No complete proof/disproof has been submitted.
The new strongest unconditional result is:

```lean
Erdos821.infinite_g_gt_three_unit_slope_limit (γ : ℝ)
    (hγ : γ < 29599/56223) :
  {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite
```

The threshold is **29599/56223 = 0.5264571438735037...**, improving
14587/27899 = 0.5228502813720922....
`infinite_g_gt_point_five_two_six_four_five` attains 10529/20000 = 0.52645.
`erdos_821_three_unit_slope_limit_range` proves the original conclusion for

```
ε > 26624/56223 = 0.4735428561264963...
```

This is still a FIXED positive epsilon threshold, not the full conjecture.

### New verified modules

Nine modules, **1209 lines**, freshly rebuilt in dependency order. All **61**
definition/lemma/theorem declarations were independently axiom-audited, and
each list is a subset of {propext, Classical.choice, Quot.sound}:

- `LocalDenominatorComparison.lean` (17 declarations)
- `ThreePrimePairBound.lean` (5)
- `ThreeIntervalTotient.lean` (9)
- `RestrictedHarmonicWeights.lean` (1)
- `ThreeCofactorMass.lean` (6)
- `ThreeCofactorSieve.lean` (6)
- `ThreeBlockSieve.lean` (8)
- `ThreeUnitSlopeDensity.lean` (3)
- `ThreeUnitSlopeLimit.lean` (6)

Every module has a matching `*Check.lean`. All result logs are empty,
all check logs contain no warnings/errors, and no source repair or
background build is pending. Logs are `/tmp/<Module>.log` and
`/tmp/<Module>Check.log`. Spec hash remains
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.

### Exact local denominator comparison

`truncatedProductMass` is the weighted subset sum subject to product<=z.
It has an exact insertion split at a prime q (indeed any positive integer):

```
T(insert q P,w,z) = T(P,w,z) + w(q)*T(P,w,z/q).
```

The verified local-comparison theorem says that if two nonnegative weights
agree outside q and 1+u(q)=K*(1+v(q)), then

```
K*T(P,v,z) <= T(P,u,Z), provided q*z<=Z and q in P.
```

For the mixed prime-pair sieve, when 3 does not divide a, the local weights
for a and 3*a are respectively 2 and 1/2 at 3. Hence

```
2*G_(3a)(z) <= G_a(Z), 3*z<=Z.
```

Using phi(3*a)/(3*a)=(2/3)*phi(a)/a and z=2^(L-2) yields the corrected
lower denominator with

```
threeCorrection a = if 3|a then 1 else 3/4.
```

The original two-unit length loss is absorbed for J>=300 at
L=floor(639*J/20); the existing squared denominator 1020*J^2 and sieve
error budget remain valid. The prime-pair and ambient endpoint main terms
retain `threeCorrection a`. The endpoint error does not increase, since
the correction is positive and at most one.

### Corrected average, including the first block

When 3 does not divide a modulus d, `threeCorrection(d*k)=threeCorrection k`.
The wide pair moduli have no divisor 3 at every scale m>=1, as follows
from their already verified roughness bound.

For even k=2*n, the exact product identity is

```
threeCorrection(2*n)/phi(2*n)
  = (3/4)/n * product_{p|n,p!=2} (1+w(p)),
w(3)=1, w(p)=1/(p-1) for p!=3.
```

In the averaged Euler product the local factor at three is 4/3, which
cancels the outer 3/4. Removing the original factors at 2 and 3 from the
39/20 Euler-product upper bound leaves **39/35**, in place of 13/10.
The corrected endpoint product is no larger than the old endpoint product,
so its error remains exp(primeTotientMass B)/A.

`corrected_reciprocal_totient_double_interval` is a DIRECT interval bound;
no subtraction of prefix upper bounds is used. The separate generic
`harmonic_average_restricted_prime_product` supplies a prefix estimate
for the FIRST block. Consequently every fixed cofactor block eventually
has corrected mass at most

```
(39/35)*(1+64*m*log 2).
```

### Unit-slope propagation and parameters

The corrected block main term is exactly **6/7** of the previous sharp main
term. Its telescoping coefficient is **26624/2975**, instead of 13312/1275.
The previous bounded-ratio unit-slope cutoff and uniform-error argument
is retained; no distribution-level or quantifier relaxation is made.

For each fixed k>=1 the parameter family is

```
a=56223*k,
t=224892*k+20,
b=106496*k+21,
c=106496*k+16,
h=5950*k.
```

After clearing the positive denominator, the strict block-budget margin
is `2000228*k+196`. The fixed enlargement of the prime cutoff is absorbed
by the previously verified fixed-shift lemma. Then k is chosen FIRST as
a function of gamma; the scale subsequently tends to infinity.

### Remaining gap

This improvement retains an exact arithmetic local factor, but it does
not cross the strict half-level restriction on modulus distribution.
The cofinal near-full structured progression lower bound and the critical
higher-divisor moment lower bound are still unproved. The root-3 endpoint
series remains unresolved. There is no valid exponent-increasing iteration
or inference from a fixed threshold to exponents approaching one.

Further finite local factors would improve the coefficient only by a fixed
amount; that observation is not a proof of any general impossibility and
has not been used as a theorem. A full settlement still needs stronger
arithmetic information, not merely this constant refinement.


## Latest continuation: unit-slope cutoffs and a stronger limiting exponent

**The original task remains UNSOLVED.** The strongest unconditional result
has improved. The new theorem is:

```lean
Erdos821.infinite_g_gt_unit_slope_limit (γ : ℝ)
    (hγ : γ < 14587/27899) :
  {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite
```

Here 14587/27899 = 0.5228502813720922..., improving the previous
694837/1333334 = 0.5211274894362553.... An explicit attained exponent
is 10457/20000 = **0.52285**, via
`infinite_g_gt_point_five_two_two_eight_five`.

The original conclusion is now proved for

```
ε > 13312/27899 = 0.47714971862790784...
```

by `erdos_821_unit_slope_limit_range`. This is still a fixed positive
lower threshold on epsilon, NOT the full original quantifier.

### Verified new modules

Twelve new modules, **1460 lines**, freshly rebuilt in dependency order:

- `Submission/CofinalMangoldtUnit.lean` (11 lemma/theorem declarations)
- `Submission/CofinalGeometricGrid.lean` (4)
- `Submission/BoundedGapMangoldtUnit.lean` (5)
- `Submission/UniformRoughHalfMean.lean` (3)
- `Submission/UniformRoughHalfError.lean` (1)
- `Submission/UniformScaleError.lean` (6)
- `Submission/UniformBlockSieve.lean` (1)
- `Submission/UniformBlockBounds.lean` (8)
- `Submission/UniformWideIncidences.lean` (3)
- `Submission/UnitSlopeWideDensity.lean` (2)
- `Submission/UnitSlopeMultiplicity.lean` (6)
- `Submission/UnitSlopeLimit.lean` (5)

Each has a matching `*Check.lean` file. All **55** declarations were
independently axiom-audited after the final rebuild, and every axiom list
is a subset of {propext, Classical.choice, Quot.sound}. All twelve result
logs are empty. Logs are `/tmp/<Module>.log` and `/tmp/<Module>Check.log`.
There is no background build or source repair pending.

### New arithmetic input: bounded-ratio unit-slope good cutoffs

The sharp logarithmic prime mass from `MertensPrimeLog` gives:

```
for every c<1, cofinally many N satisfy theta(N)>c*N and psi(N)>c*N.
```

`CofinalMangoldtUnit` proves this through a general finite weighted-prefix
comparison and an Abel contradiction. It also proves the corresponding
cofinal prime-count lower bound `c*N < log(N)*pi(N)`.

`CofinalGeometricGrid` proves that for every base b>1 and c<1 there is ONE
fixed positive integer multiplier j such that

```
c*(j*b^m) < psi(j*b^m)
```

at cofinally many m. It uses finite upper rounding and a finite pigeonhole;
j is fixed before m tends to infinity. This is not needed by the final
stronger bounded-gap argument, but is independently verified.

The main improvement is `exists_bounded_gap_theta_unit` and
`exists_bounded_gap_mangoldt_unit` in `BoundedGapMangoldtUnit`:

```
forall c<1, exists integer K>=2, forall A>=1,
  exists N in [A,K*A], theta(N)>c*N (respectively psi(N)>c*N).
```

The proof retains a direct Abel estimate on the interval. An upper bound
of slope c throughout [A,B] would bound the reciprocal logarithmic weight
by c*(1+log(B/A)), while Mertens gives log(B/A)-O(1). A sufficiently large
fixed K gives the contradiction. NO pointwise prime number theorem is
asserted.

### Uniform estimates at the selected cutoffs

The old progression estimates were only stated at exact geometric scales.
The new `UniformRoughHalfMean` proves all the needed primitive means with
an arbitrary initial cutoff X below the ambient scale, using the original
cutoff-uniform Vaughan theorem. `UniformRoughHalfError` carries this through
to composite discrepancies. It retains the restriction 2*b+5<=t.

`UniformScaleError` absorbs a fixed enlargement K into a fixed shift of
the scale variable, using lower roughness exponent a-1 instead of a.
It proves uniformly for X<=K*2^(64*t*m) that the error is at most
C*(m+1)^7*2^((64*t-1)*m), with C fixed after K is fixed. It includes the
wide-pair application `eventually_uniform_widePair_error`.

`UniformBlockSieve` retains the ACTUAL X in the sieve main term, rather
than replacing it by the largest ambient cutoff. `UniformBlockBounds`
proves that a fixed enlargement does not change the limiting main
coefficient and keeps the power-saving error uniform. The cofactor
coverage uses an extra exponent unit; the sieve error budget is kept
at the original ambient exponent. The incidence bound 16 is verified
at the enlarged exponent, requiring a>=22.

`widePair_unit_slope_smooth_count` consequently gives eventually

```
N_t(m) <= C*(m+1)*#smoothPrimePool(K*N_t(m), N_b(m))
```

with fixed K,C whenever the block coefficient is <1, instead of merely
<chebyshevRatioConstant. The progression main term is obtained at a good
N in [N_t(m),K*N_t(m)], using `exists_bounded_gap_mangoldt_unit`.

`eventual_single_log_count_of_fixed_enlargement` absorbs K by a FIXED
shift of m and returns an eventual single-log count at the original
exact cutoff. Thus no limiting smoothness exponent is lost.

### Parameters and limiting family

A concrete count is available at

```
t=40000020, b=19086009,
a=10000000, c=19086004, h=914012.
```

Its fixed multiplicity threshold is
6971337/13333340 = 0.5228500135749932....

`UnitSlopeLimit` improves this to the limiting rational threshold using
for each fixed k>=1:

```
a=27899*k,
t=111596*k+20,
b=53248*k+21,
c=53248*k+16,
h=2550*k.
```

The exact sufficient budget is verified algebraically. After clearing
the denominator, its positive margin is 994164*k+196. The complementary
ratio tends to 14587/27899. For any gamma below this threshold, k is
chosen FIRST, then the eventual prime supply at that fixed k is used.

### What is still missing

The full statement and its negation are still unproved. Improving the
Mangoldt main constant to its unit limsup does not extend the modulus
level beyond one half. Neither `CofinalGeometricMomentLower` nor
`CofinalNearFullStructuredLower` has been established. In the endpoint
smooth-series characterization, integer root k=3 remains unresolved by
this development.

`Submission/Spec.lean` is unchanged and still contains its original
`sorry`, with SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No `submit_proof()` call has been made. The older consequence modules
(such as `SharpDensityConsequences`) remain valid but have not yet been
updated to the newest limiting threshold.

---

## Latest continuation: exact two-interval joint moments (still unresolved)

Two new supporting modules compile successfully:

- `Submission/CoprimeProductPools.lean`: 9 lemmas extending finite product-pool
  identities to arbitrary positive integer pools with cross-coprimality.
- `Submission/JointShiftedMoments.lean`: 6 results giving exact two-interval
  prime-only binomial moment limits.

All 15 lemma/theorem declarations were independently axiom-audited through
`CoprimeProductPoolsCheck.lean` and `JointShiftedMomentsCheck.lean`. Every
axiom list is a subset of {propext, Classical.choice, Quot.sound}.
Both build exit codes and both audit exit codes are zero. Logs are in
`/tmp/<Module>.log` and `/tmp/<Module>Check.log`.

The new main theorem is
`tendsto_powerInterval_primeJointBinomialMoment`. For fixed natural
parameters with

```
1 <= a <= b <= c <= d,
1 <= r+s, 22 <= t, 2*(b*r+d*s)+5 <= t,
```

it establishes, as m tends to infinity, the exact limit

```
sum_{p<=X prime} binom(A(p),r)*binom(B(p),s)*log(p) / mangoldtSum(X)
  -> log(b/a)^r/r! * log(d/c)^s/s!,
```

where X=2^(64*t*m), A(p) counts prime factors of p-1 in
(2^(64*a*m),2^(64*b*m)], and B(p) uses the disjoint interval
(2^(64*c*m),2^(64*d*m)]. Zero order in either individual interval is
allowed. The level bound applies to the SUM b*r+d*s, not the two
products separately.

The proof uses exact multiplication injectivity, totient-mass
factorization, divisor-incidence factorization, preservation of
roughness, and the already proved below-half normalized prime limit.
The generic product-pool lemmas can be iterated, but no explicit
arbitrary-finite-family joint theorem has been added yet.

**No settlement:** this does not prove `CofinalGeometricMomentLower`
or `CofinalNearFullStructuredLower`. In particular, these fixed-order
constant coefficients do not supply the missing log(X)^(k-2) higher
moment lower bound. The finite partition model already in
`HalfPartitionMomentModel.lean` also warns against inferring smooth
outcomes from low-total-size moments alone; that model is not a model
of primes and is not a disproof.

`Submission/Spec.lean` has not been altered. Its conjecture still has
its original `sorry`. The strongest unconditional multiplicity
exponent in this development remains 694837/1333334 (~0.5211274894).
No `submit_proof()` call has been made. No repair or background build
is pending.

---

## Latest continuation: sharp Mertens limits and exact below-half prime moments

Ten new modules have been freshly rebuilt in dependency order, then all
49 lemma/theorem declarations audited. Every axiom list is a subset of
{propext, Classical.choice, Quot.sound}. All result logs are empty.
No Lean repair or background build is pending.

Modules (each has a corresponding `*Check.lean`):

- `Submission/MertensPrimeLog.lean`
- `Submission/MertensAbel.lean`
- `Submission/MertensPrimeIntervals.lean`
- `Submission/ElementaryMassLimit.lean`
- `Submission/MertensSubsetModuli.lean`
- `Submission/RoughHalfMean.lean`
- `Submission/RoughHalfError.lean`
- `Submission/RoughHalfLimits.lean`
- `Submission/RoughHalfPrimeLimits.lean`
- `Submission/MertensShiftedMoments.lean`

Fresh logs are `/tmp/<Module>.log` and `/tmp/<Module>Check.log`.

### Elementary Mertens estimates, without a prime number theorem

Define primeLogMass(N)=sum_{p<=N prime} log(p)/p. The factorial identity,
Stirling's already formalized limit, and Mathlib's summability of higher
prime-power Mangoldt contributions give

```
exists C>0, forall N>=1, |primeLogMass(N)-log N| <= C.
```

`reciprocal_log_weight_sum_bound` is a general quantitative Abel lemma for
arbitrary real coefficients c(n), not necessarily nonnegative. If their
floor-indexed prefix sums differ from log x by at most C on [A,B], then

```
|sum_{A<n<=B} c(n)/log n - log(log B/log A)| <= 2*C/log A.
```

Both endpoint errors are retained. This gives
`exists_primeReciprocalInterval_log_bound`, uniformly in B>=A>=2, with
an existential absolute constant D and error D/log A.

For fixed integers 1<=a<=b, as m tends to infinity:

```
sum_{2^(a*m)<p<=2^(b*m), p prime} 1/p       -> log(b/a)
sum_{2^(a*m)<p<=2^(b*m), p prime} 1/phi(p)  -> log(b/a).
```

The difference of these two interval sums is between zero and 1/2^(a*m).
This sharpens the former coarse prime-totient mass estimates.

### Exact fixed-order subset mass

`elementaryMass_succ_upper` complements the existing lower recurrence.
`tendsto_elementaryMass_of_small_weights` proves that if nonnegative total
weight tends to mu and every individual weight is bounded by beta(m)->0,
then the r-element elementary symmetric mass tends to mu^r/r! for every
FIXED r.

`powerIntervalPrimes(a,b,m)` is the prime pool in (2^(a*m),2^(b*m)].
`tendsto_powerInterval_subset_mass` proves

```
poolTotientMass(primeSubsetModuli(powerIntervalPrimes(a,b,m),r))
  -> log(b/a)^r/r!.
```

The positive eventual lower mass and actual modulus size bounds are also
proved. No prime distribution claim is hidden in this main-term limit.

### Arbitrary rough pools at a strict half level

`interval_primitive_mean_below_half` covers a broad conductor interval by
finitely many narrow intervals before applying the established primitive
mean. It allows any fixed positive lower exponent a, not only lower and
upper exponents close to each other.

`rough_pool_below_half_combined_error` applies to a pool D of positive
moduli <=Q whose every nontrivial divisor is >=L, where

```
L=2^(64*a*m), Q=2^(64*b*m), X=2^(64*t*m),
1<=a<=b, 22<=t, 2*b+5<=t, m>=1.
```

It proves the uniform bound

```
sum_{d in D} compositeProgressionError(d,X) + 2*Q*sqrt(X)*log(X)
 <= 10^15 * ((t+1)*(m+1))^7 * 2^((64*t-1)*m).
```

This improves the former small-rough-pool restriction 32*b<=t to a strict
below-square-root condition. It does NOT extend beyond half.

`RoughHalfLimits` normalizes by the ACTUAL mangoldtSum(X), using only the
proved Chebyshev lower bound. `RoughHalfPrimeLimits` explicitly removes
proper prime powers and proves that the prime-only incidence mean has the
same limit as the reciprocal-totient modulus mass.

### New exact prime-only binomial moments

Define

```
primeBinomialMoment(P,r,X)
  = sum_{p<=X prime} log(p) * choose(#{q in P : q | p-1}, r).
```

For every fixed a,b,r,t satisfying

```
1<=a<=b, 1<=r, 22<=t, 2*(b*r)+5<=t,
```

`tendsto_powerInterval_primeBinomialMoment` proves, with
P=powerIntervalPrimes(64*a,64*b,m) and X=2^(64*t*m),

```
primeBinomialMoment(P,r,X)/mangoldtSum(X) -> log(b/a)^r/r!.
```

There is also an eventual lower bound with half this coefficient when a<b.
The order r is fixed BEFORE m tends to infinity. The modulus product is
at most X^(b*r/t), strictly below sqrt(X). This result does not assert the
near-full-modulus or critical higher-divisor moment input needed for the
original conjecture.

### Review of the all-orders inference

An informal useful obstruction: append a single part N-R>R to the cycle
partition of a uniform permutation on R points. Every joint cycle-count
moment whose selected total size is <=R retains the smaller permutation's
reference value, while the augmented partition always has a part >N/2.
This explains why collecting all moments at a fixed strict half level is
not by itself a smoothness argument. This general permutation model was
NOT Lean-formalized here, is not asserted to represent the primes, and is
not a disproof of Erdos 821. The old finite models should still not be
promoted to an asymptotic prime distribution.

A bounded reference lookup again failed DNS. No updated external result
on the conjecture was obtained.

### Original task still UNSOLVED

There is no new unrestricted multiplicity exponent in this continuation.
The strongest proved threshold remains gamma<694837/1333334 (~0.52112749).
The full theorem and its negation remain unproved. Spec.lean is unchanged,
retains its original sorry, and has SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof/disproof has been submitted.

## Latest strongest unconditional result: sharper cofactor mass, exponent above 0.52112

Six new modules compile cleanly with fresh oleans:

- `Submission/TightReciprocalTotient.lean`
- `Submission/TightIntervalTotient.lean`
- `Submission/SharpCofactorSieve.lean`
- `Submission/SharpFamilyDensity.lean`
- `Submission/SharpWideDensity.lean`
- `Submission/SharpDensityConsequences.lean`

All **29** theorem/lemma declarations pass permitted-axiom audits in their
corresponding `*Check.lean` modules. Result logs `/tmp/<Module>.log` are
empty. Axiom logs `/tmp/<Module>Check.log` contain only propext,
Classical.choice, and Quot.sound. No repair or background build is pending.

### Exact finite Euler product and interval estimate

The full reciprocal-totient Euler product is at most **39/20**. The finite
product through 299, multiplied by 299/298, is proved at type Rat with
`decide +kernel`, then explicitly cast to Real. This is kernel-checked
reduction, NOT native_decide or an externally trusted computation. The
remaining tail uses the existing telescoping reciprocal-successive sum
and exp(x)<=1/(1-x). The finite rational comparison is audited normally.

This gives:

```
sum_{1<=n<=A} 1/phi(n) <= (39/20)*harmonic(A)
evenReciprocalTotient(A) <= (13/10)*harmonic(A)
```

The odd-prime Euler product has coefficient 13/10. Direct prime-product
interval averaging consequently gives

```
sum_{A<n<=B} 1/phi(2*n)
  <= (13/10)*log(B/A) + exp(primeTotientMass(B))/A.
```

No subtraction of two prefix upper bounds is used. Exponential block
endpoint errors and all prime-pair estimates are unchanged. The cofactor
block coefficient is now **13/5100**, the scale relative to the original
block main term is **117/136**, and its telescoped coefficient is
**13312/1275**.

### New strongest unrestricted exponent and prime count

`infinite_g_gt_sharp_wide_uniform` proves

```
forall gamma < 694837/1333334,
  {n | (g n : Real) > (n : Real)^gamma}.Infinite.
```

The threshold is approximately **0.5211274894362553**, improving
2082485/4000002 (~0.5206209896895). There is a direct theorem at
3257/6250 = 0.52112, and `erdos_821_sharp_wide_range` proves the original
conclusion for **epsilon > 638497/1333334** (~0.4788725105637447).

`exists_sharp_wide_smooth_prime_count` supplies

```
exists C>0, eventually m,
  independentN(40000020,m) <=
    C*m*card(smoothPrimePool(independentN(40000020,m),
                            independentN(19154910,m))).
```

Wide-family parameters:

```
a=10000000, b=19154910, c=19154906, h=845110.
```

The coefficient comparison uses the proved lower bound
chebyshevRatioConstant > 92129/100000 and exact Lean rational arithmetic.

### Updated consequences

- `sharp_wide_prime_reciprocal_divergence`: 1/p is nonsummable on
  rationalSmoothShiftedPrimes(40000019,19154910).
- `sharp_wide_eventual_polynomial_count`: exports the count with
  t=64*40000020, b=64*19154910, K=1, and logarithmic degree 1.
- `polylog_critical_exponent_sharp_wide_interval`: the exact critical
  exponent for gPolylog(kappa,n) is 1-1/kappa for
  1<kappa<=1333334/638497.
- `infinite_gPolylog_gt_sharp_wide_interval`: all strict subcritical
  exponents in that interval.
- `sharp_wide_polylog_input_fibers`: for gamma<694837/1333334 and every N,
  a squarefree fiber F at some n>N has size >n^gamma and all input primes
  <=(4*log n)^(1333334/638497).

### Original task remains UNSOLVED

These are fixed-ratio improvements, not exponents approaching one. The
full theorem or its negation has not been proved. Spec.lean is unchanged,
retains its original sorry, and has SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof/disproof has been submitted.

## Latest strongest unconditional result: longer prime-pair sieve, exponent above 0.52062

Five new result modules (653 lines) compile cleanly with fresh oleans:

- `Submission/TighterPrimePairBound.lean` (171 lines)
- `Submission/TighterCofactorSieve.lean` (118 lines)
- `Submission/TighterFamilyDensity.lean` (217 lines)
- `Submission/TighterWideDensity.lean` (74 lines)
- `Submission/TighterDensityConsequences.lean` (73 lines)

All 26 theorem/lemma declarations pass permitted-axiom audits in the
corresponding `*Check.lean` modules. All five `/tmp/<Module>.log` build logs
are empty. Audit logs are `/tmp/<Module>Check.log`. The entire dependency
chain was rebuilt in order, then all audit files checked. No build or
source repair is pending.

### NEW strongest unrestricted multiplicity exponent

`infinite_g_gt_tight_wide_uniform` proves

```
forall gamma < 2082485/4000002,
  {n | (g n : Real) > (n : Real)^gamma}.Infinite.
```

The threshold is approximately **0.5206209896895**, strictly stronger than
the previous 1036568/2000001 (~0.518283740858). There is also a direct
`infinite_g_gt_point_five_two_zero_six_two` theorem at gamma=26031/50000.
`erdos_821_tight_wide_range` supplies the original conclusion for

```
epsilon > 1917517/4000002  (approximately 0.4793790103105).
```

### Arithmetic source of the improvement

The earlier pair estimate used sieve length 2^(30*J), discarding room in
its error allowance. The new proof uses

```
L=floor(639*J/20), z=2^L, fixed error exponent 2+1/1000.
```

For J>=100, exact integer inequalities give

```
1597*J <= 50*L,
2001*L <= 1000*(64*J-1),
L <= 64*J-1.
```

Thus the squared logarithmic denominator improves from 900*J^2 to
1020*J^2 while z^(2+1/1000)+z still fits below 2^(64*J). The error exponent
is FIXED before the eventual scale threshold; there is no interchange of
quantifiers. The estimate remains uniform in the prime-pair coefficient a
and interval length N.

`eventually_tight_endpoint_pair_ambient` retains the uncapped ambient
uniformity and replaces denominator 450 by 510. The blockwise main term
is consequently multiplied by 15/17, and its telescoped coefficient becomes
8192/765 instead of 8192/675. All error terms and existing progression
estimates are retained. This is a genuine unconditional arithmetic gain.

### NEW single-logarithm prime count

`exists_tight_wide_smooth_prime_count` proves

```
exists C>0, eventually m,
  independentN(40000020,m) <=
    C*m*card(smoothPrimePool(independentN(40000020,m),
                            independentN(19175170,m))).
```

Here independentN(t,m)=2^(64*t*m). The parameters are

```
a=10000000, b=19175170, c=19175166, h=824850.
```

The coefficient inequality is verified using the already proved
chebyshevRatioConstant > 92129/100000. No new progression-level assumption
was introduced.

### NEW reciprocal and restricted-spectrum consequences

`TighterDensityConsequences.lean` proves:

- `tight_wide_prime_reciprocal_divergence`: nonsummability of 1/p on
  rationalSmoothShiftedPrimes(40000019,19175170).
- `tight_wide_eventual_polynomial_count`: an export to the generic density
  transfer at t=64*40000020, b=64*19175170, K=1, logarithmic loss degree 1.
- `polylog_critical_exponent_tight_wide_interval`: for every
  1<kappa<=4000002/1917517, the exact supremum of infinite-exceedance
  exponents for gPolylog(kappa,n) is 1-1/kappa.
- `infinite_gPolylog_gt_tight_wide_interval`: every strict subcritical
  exponent in that interval has infinite exceedance.
- `tight_wide_polylog_input_fibers`: for every gamma<2082485/4000002 and N,
  there is n>N with a finite squarefree fiber F of cardinality >n^gamma,
  all of whose input prime factors are <=(4*log n)^(4000002/1917517).

These are fixed-ratio improvements. They do NOT give exponents approaching
one, and the full conjecture remains UNSOLVED. Spec.lean is unchanged,
retains its original sorry, and has hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof/disproof has been submitted.


## Latest continuation: review of full-settlement reductions (no new theorem)

Reviewed the exact hypotheses of the full-statement implications in Work,
Progressions, ReciprocalDensity, RelativeDiscrepancyTransfer, and the
higher-root series characterization. No hypothesis was found that the
existing unconditional estimates can discharge for arbitrarily small
smoothness ratios. Fixed-modulus infinitude does not supply the requested
growing-modulus bounds; the fixed reciprocal-divergence scale does not
supply all root parameters. No quantifier interchange is justified.

Also reconsidered the finite collision-energy recurrence. Its diagonal
Euler-product lower bound does not force divergence at every exponent
below one; the needed off-diagonal correlation lower bound remains missing.
No new arithmetic estimate or result module was produced in this review.
This is not a proof that these methods cannot work.

The original conjecture remains UNSOLVED, and Spec.lean is unchanged with
its original sorry. No proof or disproof has been submitted. The strongest
unconditional exponent remains 1036568/2000001.


## Latest continuation: averaged profile identity in the short-cofactor regime

`Submission/AveragedPrimeProfile.lean` (168 lines) compiles cleanly with a
fresh olean. All ten declarations pass permitted-axiom audits in
`Submission/AveragedPrimeProfileCheck.lean`. Result log
`/tmp/AveragedPrimeProfile.log` is empty. Audit log is
`/tmp/AveragedPrimeProfileCheck.log`. No source repair or build is pending.

The upper prime-factor mass is additive on nonzero products. Its vanishing
is equivalent to smoothness for positive inputs. The new full-multiplicity
bound `smooth_divisor_upperFactorMass_power_le` proves

```
d is y-smooth, d|n, n>0 => d*y^upperFactorMass(n,y) <= n.
```

Consequently, if n<d*y^k then upperFactorMass(n,y)<k (for y>=1).
In particular, when n<d*y^2, the mass equals the roughness indicator,
INCLUDING prime-power multiplicities:

```
upperFactorMass(n,y) = if n is y-smooth then 0 else 1.
```

For a finite prime pool P in this short-cofactor regime,
`predecessorProduct_upperFactorMass_eq_rough_card` and
`predecessorProduct_arity_deficit_eq_smooth_card` prove the exact identities

```
upperFactorMass(product_{p in P}(p-1), y) = #{p in P : p-1 is not y-smooth},
|P|-upperFactorMass(product_{p in P}(p-1), y) = #{p in P : p-1 is y-smooth}.
```

`structuredPredecessor_arity_deficit_eq_smooth_card` applies the second
identity to the existing pool structuredWitnessPrimes(r,m,2^(64*t*m))
at y=2^(64*b*m), assuming b>=2, m>=2, t<=r+2*b. It is an IDENTITY, not a
lower estimate for its smooth-prime side.

Thus the proposed averaging step, in precisely this regime, does not yet
supply independent arithmetic information: a lower arity deficit is exactly
the missing smooth-prime count. The existing large-prime divisor-switching
identities still leave the corresponding prime-correlation estimate unproved.
This is not an impossibility theorem about other coloring or averaging methods.

The original conjecture remains UNSOLVED. The strongest unconditional exponent
is still 1036568/2000001. Spec.lean is unchanged, retains its original sorry,
and has hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof/disproof has been submitted.


## Latest continuation: prime-exponent profile and arity-deficit bounds

`Submission/ColoringPrimeProfile.lean` (137 lines) compiles cleanly with a
fresh olean. All six lemma/theorem declarations pass permitted-axiom audits
in `Submission/ColoringPrimeProfileCheck.lean`. Build log
`/tmp/ColoringPrimeProfile.log` is empty; audit log is
`/tmp/ColoringPrimeProfileCheck.log`. No repair or build is pending.

Definitions:

```
upperFactorMass(n,y) = sum_{q|n, q>=y} v_q(n)
lowerDivisorCost(n,y) = product_{q|n, q<y} (v_q(n)+1)
```

`tau_le_split_prime_profile` proves, uniformly for every integer r>=1,

```
tau_r(n) <= lowerDivisorCost(n,y)^(r-1) * r^upperFactorMass(n,y).
```

`admissibleSupport_rough_card_le_upperFactorMass` proves that the number of
input support primes whose predecessors are NOT y-smooth is bounded by the
large-factor multiplicity of the output. This applies to all admissible
supports, without a squarefree restriction. It uses a finite union bound
and the already verified prime-by-prime valuation bound.

`smoothPrimePool_card_ge_arity_deficit` consequently proves:

```
phi(m)=n>0, omega(m)>=k, every p|m satisfies p<=X
  => k-upperFactorMass(n,y) <= card(smoothPrimePool(X,y)).
```

`exists_divisor_large_g_of_prime_profile` extracts d|n with g(d)>C*d^s
from a finite squarefree fiber F of arity >=k if E=upperFactorMass(n,y)<=k
and the EXPLICIT inequality

```
C^r*n^s*lowerDivisorCost(n,y)^(r-1) < |F|*r^(k-E)
```

holds. The two prime-power tau bounds used in the split estimate are also
exported. No required arity deficit or coloring excess at a smaller cutoff
has been established. In particular, a large deficit would already supply
new smooth shifted primes by the preceding finite theorem. This is NOT an
unconditional exponent improvement, nor a general impossibility theorem
about coloring.

The original conjecture remains UNSOLVED. The strongest unconditional
multiplicity exponent remains 1036568/2000001. Spec.lean remains unchanged,
with its original sorry and hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof or disproof has been submitted.


## Latest continuation: exact higher-divisor cost for all integer color counts

`Submission/ExactColoringCost.lean` (105 lines) compiles cleanly with a fresh
olean. Its five declarations pass the permitted-axiom audit in
`Submission/ExactColoringCostCheck.lean`. The result log is
`/tmp/ExactColoringCost.log` (empty); the check log is
`/tmp/ExactColoringCostCheck.log`. No source repair or build is pending.

The old color estimate overcounted ordered divisor outputs by tau(n)^(r-1).
The new `coloredFiber_le_tau_of_divisor_bound` proves, for EVERY integer r>=1,
not only powers of two,

```
[forall d|n, g(d)<=C*d^s] =>
  coloredFiber(r,n) <= C^r * n^s * tau_r(n),
```

where C>=0, n>0, and s is any real. `coloredFiber_add_le` supplies the
underlying convolution inequality for arbitrary r+s. A global-power-bound
specialization is also included.

`exists_divisor_large_g_of_exact_coloring` now extracts d|n with g(d)>C*d^s
from any finite squarefree fiber F of n, of input arity at least k, provided

```
C^r*n^s*tau_r(n) < |F|*r^k.
```

`tau_color_cost_product` identifies the exact finite cost:

```
tau_r(n) = product_{p|n} binomial(v_p(n)+r-1,r-1).
```

The excess condition has NOT been proved for arbitrarily large C at any
exponent above the existing threshold. Informal optimization makes clear
that controlling this sharper cost requires information about the output
prime-exponent profile beyond the supplied smoothness cutoff. No numerical
model or informal profile calculation was used as a theorem. In particular,
this module does NOT establish unconditional exponent amplification.

The original conjecture remains UNSOLVED. Spec.lean retains its original
sorry and hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
The strongest unconditional multiplicity exponent remains
1036568/2000001. No complete proof/disproof has been submitted.


## Latest continuation: uniform squarefree-coloring and divisor extraction inequalities

`Submission/SquarefreeColoring.lean` (241 lines) compiles cleanly with a fresh
olean. All twelve declarations pass permitted-axiom audits in
`Submission/SquarefreeColoringCheck.lean`. The result log
`/tmp/SquarefreeColoring.log` is empty; the audit log is
`/tmp/SquarefreeColoringCheck.log`. No source repair or build is pending.

Definitions:

```
squarefreeFiber(n) = {m | Squarefree(m) and phi(m)=n}, as a Finset
coloredFiber(r,n) = sum_{m in squarefreeFiber(n)} tau_r(m)
```

For r>=1 and squarefree m, `tau_squarefree` proves tau_r(m)=r^omega(m).
`coloredFiber_eq_color_sum` and `coloredFiber_one` identify the coloring
count and its r=1 case.

`squarefree_convolution_push_le` proves a general finite convolution push
inequality. Divisor pairs of a squarefree input are coprime, so phi is
multiplicative on them. Their injection into pairs of input fibers is
proved by disjoint finite unions; no factorization collisions are ignored.
Consequently

```
coloredFiber(2*r,n) <= sum_{d|n} coloredFiber(r,d)*coloredFiber(r,n/d).
```

For r=2^j, `coloredFiber_two_pow_le_of_divisor_bound` proves

```
[forall d|n, g(d)<=C*d^s] =>
  coloredFiber(r,n) <= C^r * n^s * tau(n)^(r-1),
```

with C>=0, n>0, and ANY real s. The number of colors is not fixed before n;
the inequality is finite and uniform. A global-power-bound specialization
and a finite-family arity lower bound are also supplied.

`exists_divisor_large_g_of_coloring` is an actual finite extraction criterion:
if F is a squarefree fiber of n, every input has at least k prime factors,
and

```
C^r*n^s*tau(n)^(r-1) < |F|*r^k,  r=2^j,
```

then some divisor d of n has g(d)>C*d^s. The excess condition is EXPLICIT
and has NOT been established at exponents above the existing lower bound.
This is not a proved unconditional amplification.

The product/interpolation review found no justified convexity law for the
restricted spectrum. The informal scale comparison for the current
pigeonhole construction suggests the coloring gain spends the slack between
the selected subset size and output prime support, rather than extending
beyond the complementary smoothness cutoff. No method-impossibility theorem
or new arithmetic lower bound is claimed from that informal comparison.

The original conjecture remains UNSOLVED. Spec.lean retains its original
sorry and hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
The best unrestricted exponent and proved restricted-kappa interval are
unchanged. No complete proof/disproof has been submitted.


## Latest continuation: sharp restricted spectrum on the whole supplied interval

`Submission/PolylogSpectrumInterval.lean` (193 lines) compiles cleanly with a
fresh olean. All seven declarations pass permitted-axiom audits in
`Submission/PolylogSpectrumIntervalCheck.lean`. The build log
`/tmp/PolylogSpectrumInterval.log` is empty; the audit log is
`/tmp/PolylogSpectrumIntervalCheck.log`. No source repair/build is pending.

For EVERY real kappa with 1<kappa<=2000001/963433, the theorem
`polylog_critical_exponent_wide_interval` proves

```
sSup {gamma | {n | gPolylog(kappa,n) > n^gamma}.Infinite} = 1-1/kappa.
```

`infinite_gPolylog_gt_wide_interval` explicitly supplies all exponents strictly
below that boundary. `finite_gPolylog_exceedance` supplies the matching finite
exceedance above the boundary, for every kappa>1. Endpoint exceedance remains
unspecified. Recall gPolylog counts only inputs with every prime factor at most
(4*log n)^kappa; it is NOT the unrestricted g.

The generic `infinite_gPolylog_gt_of_polynomial_count` and
`polylog_critical_exponent_of_polynomial_count` transfer any existing count with
scale t and smoothness scale b to every kappa>1 satisfying b*kappa<=t. The new
finite parameter lemma chooses c=floor(t*k/kappa)+1 and sufficiently large k,
with all truncation, output-exponent, and input-exponent inequalities verified.
There is no quantifier exchange and no new prime distribution assumption.

The earlier weighted-moment/partition review did not supply a new arithmetic
lower bound. Numerical tests (NOT Lean proofs) found the cube-root-excluding
half-level partition LP infeasible at N=12,18,24 with all single-part means;
N=12 and N=24 also tested infeasible without above-level single-part means.
The strict-half test N=24, level=11, without above-level singles was numerically
feasible (max residual about 2.54e-8, max density ratio about 109.34); no exact
certificate was reconstructed. The N=36 half-level test returned Unknown,
not infeasible. Temporary scripts/logs are in /tmp. These finite boundary
phenomena were NOT promoted to claims about actual prime moments or their
limits. No new sufficient lower estimate was established.

The proved interval of kappa is bounded. It does NOT allow exponents tending
to one, and the original conjecture remains UNSOLVED. The strongest unrestricted
lower exponent is unchanged. Spec.lean retains its original sorry and hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof/disproof has been submitted.


## Latest continuation: exact critical exponent for a polylogarithmically restricted fiber

Two new result modules (346 lines) compile cleanly with fresh oleans:

- `Submission/PolylogSmoothInputFibers.lean` (182 lines)
- `Submission/PolylogMultiplicitySpectrum.lean` (164 lines)

All thirteen theorem/lemma declarations pass permitted-axiom audits in their
corresponding `*Check.lean` modules. Build logs `/tmp/PolylogSmoothInputFibers.log`
and `/tmp/PolylogMultiplicitySpectrum.log` are empty; check logs have the same
names with `Check`. There is no pending build or source repair.

`wide_block_polylog_input_fibers` strengthens the retained INPUT properties
at every gamma < 1036568/2000001. For every N there are n>N and a finite set F
with n^gamma < |F|, every m in F squarefree with phi(m)=n, and

```
∀ p in primeFactors(m), (p : Real) <= (4*log n)^(2000001/963433).
```

The finite argument retains k=2^((b+1)*L) inputs primes, uses
n>=2^(k-1) to obtain k<=4*log n, and bounds each input prime by
k^(t/(b+1)). The eventual polynomial-loss transfer preserves the exponent
and yields the displayed fixed power of log n.

The second module defines gPolylog(kappa,n) to count ALL preimages with
prime factors <= (4*log n)^kappa (without a squarefree restriction).
`eventually_gPolylog_le` proves, for kappa>1 and alpha>1-1/kappa,

```
eventually n, gPolylog(kappa,n) <= n^alpha.
```

The upper bound uses the existing finite-fiber Rankin inequality and the
new bound poolWeight(primesBelow(y)) <= y*log 4. Together with the new lower
construction, it proves that the exact supremum of exponents gamma for which

```
{n | gPolylog(2000001/963433,n) > n^gamma}.Infinite
```

is 1036568/2000001. The exact theorem is
`polylog_critical_exponent_wide_block`. All exponents strictly below the
threshold give infinite exceedance; all strictly above give finite exceedance.
No claim is made at the endpoint itself.

This is a result for a RESTRICTED multiplicity, not an upper bound on the
unrestricted g and not a settlement of Erdős 821. The stronger structural
input information did not furnish a new prime-progression lower estimate.
The original conjecture remains UNSOLVED. Its strongest unrestricted lower
exponent is unchanged, and the cofinal near-full arithmetic inputs remain
unproved. Spec.lean still has its original sorry and hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof/disproof has been submitted.


## Latest continuation: raw moment coefficient gap without any admissibility conditions

`Submission/UnrestrictedMomentCoefficientGap.lean` (92 lines) compiles cleanly.
Its four lemmas pass the permitted-axiom audit in
`Submission/UnrestrictedMomentCoefficientGapCheck.lean`. Fresh oleans exist;
logs are `/tmp/UnrestrictedMomentCoefficientGap.log` (empty) and
`/tmp/UnrestrictedMomentCoefficientGapCheck.log`. No source repair/build is pending.

The new theorem `nearMoment_raw_coefficient_gap_unrestricted` proves, for
EVERY w>=1 and every A,m, without the old R/order/scale or error-budget conditions,

```
E^(w*(A+8)) / log(nearMomentX(w,A,m))^w <
  (1/2)^(w+1)/(w+1)!,   E=logMomentScale(m).
```

The explicit scale formula gives `log(X)>=16*w*E^(A+8)`, while
`2^(w+1)*(w+1)! < (16*w)^w`. Thus merely weakening the construction's
admissibility constraints cannot permit its raw coefficient to reach the
half-geometric factorial benchmark. The theorem bounds ONLY the explicit
lower certificate, not the actual shifted-prime moment. It does not exclude
other arithmetic constructions and is not a disproof of Erdős 821.

The interrupted small-radical review was also completed:
`SmallRadicalMiddleFibers.lean` already supplies the restricted counting bound;
there is no new amplification there. The finite partition models were reviewed,
but no infinite-scale moment argument or stronger arithmetic lower bound was found.

Spec.lean remains unchanged with its original sorry and hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
The original conjecture is still UNSOLVED. The strongest unconditional
multiplicity exponent remains 1036568/2000001, and no complete proof/disproof
has been submitted. The sufficient cofinal arithmetic hypotheses remain unproved.


## Latest continuation: pointwise divisor-moment bootstrap checked and rejected

`Submission/ArityMomentPositivityAudit.lean` (78 lines) compiles cleanly.
All six declarations pass the permitted-axiom audit in
`Submission/ArityMomentPositivityAuditCheck.lean`. Both logs are in /tmp,
named after the modules; the result build log is empty. No placeholder or
new axiom occurs, and no repair/build is pending.

A proposed convexity/positive-moment bootstrap does not hold pointwise.
For n=6 (which is the predecessor of the prime 7), tau(k+1,6)=(k+1)^2.
For a_j=j!*tau(j+1,6), the first five entries are 1,4,18,96,600 and

```
900*a_0 - 720*a_1 + 204*a_2 - 24*a_3 + a_4 = -12.
```

These are the coefficients of (x^2-12*x+30)^2. Hence the 3-by-3 Hankel
quadratic form is not nonnegative. The failure persists after any positive
overall scaling and division of the j-th entry by T^j for T>0.
The k!-normalized variant b_j=(j+1)!*tau(j+1,6) already fails pointwise
log-convexity: b_0*b_2=54 < 64=b_1^2.

These exact counterexamples only reject the proposed POINTWISE properties.
They are not estimates for prime-averaged moments, do not exclude a separate
asymptotic argument, and do not disprove Erdős 821. No sufficient new
arithmetic lower bound or improved multiplicity exponent was obtained.

Spec.lean remains unchanged with its original sorry and hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
The exact conjecture is still UNSOLVED and no complete proof/disproof has
been submitted. The strongest unconditional exponent and closed-output
result remain those recorded below.


## Latest continuation: uniform-exponent closed small-radical fibers

New result module `Submission/UniformClosedFibers.lean` (213 lines) compiles
cleanly, with a fresh olean and empty `/tmp/UniformClosedFibers.log`.
All five declarations have permitted-axiom audits in
`Submission/UniformClosedFibersCheck.lean`; the audit log is
`/tmp/UniformClosedFibersCheck.log`. No placeholder or new axiom occurs.

The main theorem, `Erdos821.ClosedPadding.wide_block_closed_small_radical_fibers`,
proves that for every 0 <= gamma < 1036568/2000001 and all natural r,N,
there exists n>N with

```
(n : Real)^gamma < g n,
radical(n)^r <= n,
totient(radical(n)) divides n.
```

This upgrades the earlier closed-small-radical theorem, which retained only
a much weaker fixed positive exponent. The new generic transfer preserves
every exponent below the complementary cutoff of an eventual polynomial-loss
smooth-prime count. Its finite argument uses primorial(y)<=4^y to make the
closed support core subpower at the selected output. Padding costs and
collisions are still explicitly charged; no exponent amplification is claimed.

Reconsidering support completion, prime-power buffers, and iterated inverse
fibers did not produce an amplification. The large optional input primes
cannot be reused as predecessor factors without a new supply of primes;
small radical of the output alone does not provide that supply. These
observations are scope checks, not a disproof or a new arithmetic theorem.

The strongest unconditional exponent is UNCHANGED. The cofinal near-full
structured progression lower bound remains unproved. The exact conjecture
is still UNSOLVED; Spec.lean is unchanged with its original sorry and hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof/disproof has been submitted, and no source repair or
background build is pending in the new module.


## Latest continuation: endpoint cap removed; near-full arithmetic gap isolated

Four new result modules (523 lines) compile cleanly with fresh oleans:

- `Submission/UncappedEndpoint.lean`
- `Submission/UncappedCofactorSieve.lean`
- `Submission/UncappedFamilyDensity.lean`
- `Submission/NearFullStructuredCriterion.lean`

All fifteen theorem/lemma declarations pass permitted-axiom audits in
`Submission/UncappedEndpointCheck.lean` and
`Submission/NearFullStructuredCheck.lean`. All four build logs in /tmp
are empty. No placeholder or added axiom occurs in these modules.

The old fixed cap a<=2^(256J) in the prime-pair endpoint estimate is now
unnecessary at any FIXED ambient exponential scale. The new proof gives

```
n/phi(n) <= exp(primeTotientMass N), 0<n<=N,
```

and, for N=2^(64*t*m), bounds the right side by
exp(1024)*(t*m)^8. Consequently it is eventually at most 2^m. This
absorbs the endpoint correction uniformly for every sieve length J>=m.
`EndpointPairUpTo X J` and `eventually_endpoint_pair_ambient` replace the
old fixed coefficient cap with uniformity over X<=2^(64*t*m).

`fixed_mass_block_smooth_count_ambient` is the general fixed-mass theorem
WITHOUT the old condition t+4<=5*c. Its genuine progression lower bound
is still an explicit hypothesis. Removing the endpoint cap DOES NOT
prove distribution at any larger modulus level, improve the current
unconditional multiplicity exponent, or remove the main-coefficient
limitation at a half modulus level.

A separate sufficient arithmetic criterion is now formalized without
using the second sieve at all. Define

```
structuredWeightLower r t m :=
  N/(16*primeProductMassConstant(r)*(m+1)^r)
    <= sum_{d in primeProductModuli r m} residueOneMangoldt d N,
N=2^(64*t*m).
```

`CofinalNearFullStructuredLower` asserts that for every order lower bound
B there is a FIXED t>=max(B,3) for which structuredWeightLower(t-2,t,m)
holds at arbitrarily large m. This input is NOT proved.

`erdos_821_of_cofinal_near_full_structured` proves that this input would
settle the exact original conjecture. The argument converts progression
weight to a prime count using bounded incidence, then uses the large
smooth divisor directly: the residual cofactor has size at most
2^(128*m), so no second sieve is needed. The fixed-order and cofinal-scale
quantifiers are kept in the required order.

`negation_forces_near_full_structured_deficit` proves the conditional
contrapositive: a failure of Erdős 821 would force an eventual strict
deficit in these progression sums at every sufficiently high fixed
order. This is NOT a proof of such a deficit and NOT a disproof.
The existing unconditional lower theorem is only available under
2*r+1<=t; for r=t-2 that reaches only t<=3, not cofinally many t.

The strongest unconditional results are UNCHANGED from the section
below: multiplicity exponent gamma<1036568/2000001 and reciprocal
divergence at relative smoothness ratio 19268660/40000019.
The exact conjecture remains UNSOLVED. Spec.lean is unchanged with its
original sorry and hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof/disproof has been submitted. No new source repair or
background build is pending.

## Latest strongest result: fixed-mass blockwise smooth-prime density

Six new result modules (811 lines) compile cleanly with fresh oleans, and
all 35 new theorem/lemma declarations have permitted-axiom audits in
`Submission/WideBlockCheck.lean`:

- `Submission/FamilyBlockSieve.lean`
- `Submission/FixedMassBlockDensity.lean`
- `Submission/ParametricWidePools.lean`
- `Submission/ParametricWideDistribution.lean`
- `Submission/ParametricWideDensity.lean`
- `Submission/WideBlockReciprocal.lean`

The main new arithmetic result removes the large logarithmic loss from
the narrow product-modulus count. There exists a FIXED positive natural
C such that, eventually for m,

```
X <= C*m*card{p<=X prime : p-1 is Y-smooth},
X=2^(64*40000020*m), Y=2^(64*19268660*m).
```

Thus the count is of order X/log X, not X/log(X)^r. The modulus pool is
the product of two disjoint wide prime intervals, with parameter
a=10000000 and ambient index t=4*a+20. The blockwise sieve uses physical
smoothness index b=19268660, effective index c=b-4=19268656, and
cofactor index h=731360. Primitive one-prime and two-prime conductor
errors are separately power-saving. The pool has fixed reciprocal mass
and at most sixteen incidences at any nonzero n<X.

`wide_block_prime_reciprocal_divergence` proves

```
not Summable ((rationalSmoothShiftedPrimes 40000019 19268660).indicator
  (fun p : Nat => 1/(p : Real))).
```

The relative smoothness ratio is about 0.4817162712, improving the older
19400/40019 (about 0.48477). The transfer explicitly removes primes below
2^(64*40000019*m) by a power saving. It does NOT infer reciprocal
divergence from the earlier higher-logarithmic-loss count.

A short decimal version, `wide_block_decimal_reciprocal_divergence`,
proves reciprocal divergence for primes p satisfying

```
q^25000 <= (p-1)^12043 for every prime factor q of p-1,
```

that is, relative smoothness ratio 0.48172.

The direct count also slightly improves the strongest verified
multiplicity theorem. `infinite_g_gt_wide_block_uniform` establishes

```
for every gamma < 1036568/2000001,
  {n : Nat | (g n : Real) > (n : Real)^gamma}.Infinite.
```

The threshold is approximately 0.518283740858, strictly above the previous
2073135/4000001 (approximately 0.518283620429). Equivalently, the original
inequality is proved for epsilon>963433/2000001. This threshold comes
from the absolute count ratio b/t, while the reciprocal theorem uses the
slightly larger relative ratio b/(t-1).

Reusable generic results now separate fixed-mass distribution from the
block sieve:
- `fixed_mass_progression_lower` retains any lower constant below the
  Chebyshev factorial-ratio constant under an explicit power-saving error.
- `fixed_mass_block_smooth_count` yields a one-logarithm count from a
  fixed-mass family, its actual distribution lower bound, bounded
  incidences, and the blockwise main coefficient condition.
- `not_summable_relative_of_single_log_count` supplies reciprocal
  divergence from a genuine one-logarithm count.
- `rationalSmoothShiftedPrimes_mono_ratio` transfers rational smoothness
  along a proved cross-product inequality.

All result build logs in /tmp (named after the modules) are empty.
`/tmp/WideBlockCheck.log` contains only permitted-axiom audit results.

The exact conjecture remains UNSOLVED. No arithmetic input for arbitrary
small smoothness ratios, or near-unit geometric shifted-prime moments,
has been proved. The existing block-method limitation below 0.51829 is
not an upper bound on g and does not disprove the conjecture.
Spec.lean is unchanged with its original sorry and hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof/disproof has been submitted. No source repair or
background build is pending in the new result modules.

## Latest strongest multiplicity exponent: direct blockwise sieve

`Submission/BlockChebyshevSpecialization.lean` now proves

```
for every gamma < 2073135/4000001,
  {n : Nat | (g n : Real) > (n : Real)^gamma}.Infinite.
```

The threshold is approximately 0.5182836204, strictly improving the
previous 2070643/4000001 (approximately 0.5176606206). Equivalently, the
original inequality is established for epsilon>1926866/4000001, and in
particular for epsilon>0.48172. THIS IS STILL ONLY A FIXED EXPONENT RESULT.

Seven result modules (837 lines) compile cleanly with fresh oleans:

- `Submission/IntervalTotientScales.lean`
- `Submission/BlockCofactorSieve.lean`
- `Submission/BlockCompositeScales.lean`
- `Submission/BlockCompositeGain.lean`
- `Submission/BlockSieveBudget.lean`
- `Submission/BlockChebyshevSpecialization.lean`
- `Submission/BlockSieveBarrier.lean`

All 42 new theorem/lemma declarations have permitted-axiom audits in
`Submission/BlockCompositeCheck.lean` and
`Submission/BlockSieveBarrierCheck.lean`. Build and audit logs are in
`/tmp/`, named after the respective module.

The direct interval reciprocal-totient estimate has now been specialized
to exponential cofactor blocks. Its endpoint error is bounded by a fixed
constant times m^8/2^m, and therefore tends to zero. The cofactor sum is
partitioned BEFORE applying upper bounds; there is no subtraction of
prefix upper bounds. For block j (0<=j<h), the sieve length is

```
J = (b+h-j-2)*m.
```

The limiting normalized main coefficient is

```
blockMainLimit t b h
  = (8192/675)*t * sum_{j<h} 1/(b+j-1)^2.
```

It lies between the telescoping bounds

```
(8192/675)*t*h/((b-1)*(b+h-1))
  <= blockMainLimit t b h
  <= (8192/675)*t*h/((b-2)*(b+h-2)),
```

with b>=2 for the lower bound and b>=3 for the upper bound. The generic
multiplicity theorem `infinite_g_gt_block_parameters` applies when
r+b+h=t, 2*r+1<=t, b>=2, h>=1, t+5<=5*b, and
blockMainLimit t b h < chebyshevRatioConstant. The explicit specialization
is r=2000000, t=4000001, b=1926866, h=73135.

The NEW method budget has also been checked separately:
`block_parameters_exponent_bound` bounds every threshold from these
actual blockwise conditions below 0.51829. Its normalized necessary
condition is C*kappa <= c0*beta*(beta+kappa), C=8192/675. Cutoffs tending
to zero under this budget require modulus levels tending to one.
These are method limitations, NOT upper bounds on g and NOT a disproof.
Old bounds below 0.51767 or 0.5161 concern earlier sufficient conditions.

Review of the moment route found no sufficient new arithmetic input:
sharpening small-prime mass or the number-of-factors truncation might
improve its lower certificate, but the currently proved certificate
still does not supply the near-unit geometric coefficient in
CofinalGeometricMomentLower. No such sharpening has been asserted as a
completed result.

The exact conjecture remains UNSOLVED. Spec.lean is unchanged, retains
its original sorry, and has SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof/disproof has been submitted. There is no pending
source repair or background build in the new result modules. Disposable
API probes may still contain failed #check commands.

## Latest continuation: direct interval reciprocal-totient bound verified

`Submission/IntervalPrimeWeights.lean` and
`Submission/IntervalReciprocalTotient.lean` now compile with fresh oleans.
All eleven declarations pass the permitted-axiom audit in
`Submission/IntervalReciprocalTotientCheck.lean`.

For positive A<=B, the principal new estimate is

```
sum_{2*A<n<=2*B, Even n} 1/totient(n)
  <= (4/3)*log(B/A) + exp(primeTotientMass B)/A.
```

This is proved directly on the interval via a prime-product expansion;
there is no subtraction of two prefix upper bounds. It is suitable for
logarithmic cofactor blocks, but no block-sieve specialization or new
multiplicity exponent has been proved from it. In particular, this does
not supply the critical shifted-prime moment lower bound or the smooth
shifted-prime series divergence required to settle the conjecture.

The four pending repairs from the previous continuation are completed
(and the analogous remaining product-positivity step is repaired too).
Logs: `/tmp/IntervalPrimeWeights.log`,
`/tmp/IntervalReciprocalTotient.log`, and
`/tmp/IntervalReciprocalTotientCheck.log`.

The exact conjecture remains UNSOLVED. The strongest verified exponent
is still gamma<2070643/4000001. Spec.lean is unchanged and retains its
original sorry. No complete proof or disproof has been submitted. There
is no pending interval-module repair or background build.

## Latest strongest multiplicity exponent: flexible Chebyshev constant

`Submission/FlexibleChebyshevSpecialization.lean` now proves

```
for every gamma < 2070643/4000001,
  {n : Nat | (g n : Real) > (n : Real)^gamma}.Infinite.
```

The new threshold is approximately 0.51766062, strictly improving the
previous 2064/4001 (approximately 0.515871). Equivalently, the original
inequality is established for epsilon>1929358/4000001, and in particular
for epsilon>0.48234. This remains a FIXED exponent improvement, not a
settlement of the original conjecture.

Three new result modules (401 lines) compile cleanly with fresh oleans.
Twenty declarations pass the permitted-axiom audit. The proof retains the
full Chebyshev factorial-ratio constant and replaces fixed error margins
and the coarse harmonic coefficient by arbitrary margins and its limiting
coefficient. The old 27/32 RetentionBudget bound in SieveIterationBudget
concerns the OLD sufficient conditions, not these new ones.

A subsequent audited result, `Submission/FlexibleSieveBudget.lean`, now
bounds thresholds from the NEW flexible conditions below 0.51767. It also
proves that cutoffs tending to zero in this budget require modulus levels
tending to one. These are method limitations, not upper bounds on g and
not a disproof. The strongest attained exponent above is unchanged.

Spec.lean is unchanged and still has its original sorry. No complete
proof/disproof is ready, and no submission, source repair, or background
build is pending. Full details are at the end of this log.

## Latest continuation: uniform coefficient gap for the near-moment construction

`Submission/NearMomentCoefficientGap.lean` proves that, under the SAME finite
R+1<=E condition used for the near-moment lower bounds, both their raw
normalized coefficient and the displayed log-log-loss coefficient are
STRICTLY smaller than 2^(-K)/K!, uniformly in the admissible divisor order
K=w+1. Thus allowing that order to grow does not let these lower certificates
meet the geometric-loss criterion with theta>=1/2.

This compares explicit LOWER CERTIFICATES, not the actual prime moments;
it is neither an arithmetic upper bound nor a disproof. The 135-line result
module compiles cleanly; six declarations pass the permitted-axiom audit.
The original conjecture is still UNSOLVED. Spec.lean is unchanged, retaining
its original sorry. No proof/disproof has been submitted and no build or
source repair is pending. Details are at the end of this log.

## Latest continuation: critical moment power with an explicit log-log loss

`Submission/LogLogMomentLower.lean` now proves, for every FIXED integer
K>=2, arbitrarily large X with

```
X*(log X)^(K-2)/(log(log X))^(30*(K-1))
  <= sum_{p<=X prime} tau_K(p-1).
```

The same bound holds cofinally on every prescribed scale family
`X=2^(128*t*L)`, t>=2. Three new result modules (570 lines) compile cleanly;
25 declarations have a clean permitted-axiom audit. The auxiliary parameter
now GROWS with the scale, justified by new finite budget estimates, while
the divisor order remains fixed.

The denominator still tends to infinity. Thus this does NOT provide the
positive critical coefficient required by CofinalGeometricMomentLower,
does not settle Erdos 821, and does not improve the strongest verified
multiplicity exponent. Spec.lean remains unchanged with its original sorry.
There is no pending source repair or build. Full details at the end.

## Latest continuation: every subcritical logarithmic moment power

`Submission/NearSharpMomentPowers.lean` now proves, for every FIXED integer
K>=2 and every real alpha<K-2, arbitrarily large X with

```
X*(log X)^alpha <= sum_{p<=X prime} tau_K(p-1).
```

The same result is proved on a cofinal set of the exact prescribed scales
`X=2^(128*t*L)` for every fixed t>=2. Thus every positive loss from the
critical logarithmic power is now available; the previous small fixed
linear coefficient is superseded at each fixed order.

Five new modules (837 lines) compile cleanly, and 29 declarations have a
clean permitted-axiom audit. This is still NOT the critical power K-2 with
a positive coefficient. It does not establish CofinalGeometricMomentLower,
settle Erdos 821, or improve the strongest verified multiplicity exponent.
Spec.lean remains unchanged with its original sorry. No repair/build is
pending. Details and exact theorem names are at the end.

## Latest continuation: growing subset moments, linear logarithmic exponent

`Submission/GrowingSubsetMoments.lean` now proves, for every fixed K>=32769,
arbitrarily large X with

```
X*(log X)^((K-1)/524288 - 1) <= sum_{p<=X prime} tau_K(p-1).
```

This is a genuine unconditional arithmetic lower bound with a logarithmic
exponent LINEAR in K, replacing the previous log(K) dependence at large
orders. Five new result modules (938 lines) compile cleanly. Twenty-four
declarations have a clean axiom audit using only propext, Classical.choice,
and Quot.sound. The exact scale for the basic order 32768*k+1 is
`X_m = 2^((k*m)*2^(2*m+22))`, with k FIXED and m tending to infinity.

This is still weaker than the power K-2 required by the cofinal moment
criterion. It does not settle Erdos 821 or improve the strongest verified
multiplicity exponent. Spec.lean remains unchanged with its original sorry.
There is no incomplete source proof or pending build. Details at the end.

## Latest continuation: quantitative shifted-prime divisor moments

Three new result modules now prove a genuine positive logarithmic-power
lower bound, uniform over every divisor order k>=2, at
`X_m = 2^(2^(2*m+16))`:

```
X_m * (log X_m)^(log(k)/131072 - 1)
  <= sum_{p<=X_m, p prime} tau_k(p-1), eventually in m.
```

In particular, order two has exponent `1/262144-1`, improving the older
unspecified unbounded multiplier of X/log X to an explicit positive power
of log X. This does not give the exponent k-2 needed in the cofinal moment
criterion and does not improve the strongest multiplicity exponent.

The modules compile cleanly; fifteen declarations were audited with only
the permitted axioms. Full details and file names are in the final section.
The exact conjecture is still UNSOLVED and Spec.lean still has its sorry.

## Latest continuation: wide prime-modulus pools, now completed

`Submission/WideReciprocalDensity.lean` now proves unconditional reciprocal
divergence over primes p with every prime divisor q of p-1 satisfying
`q^40019 <= (p-1)^19400`. The ratio is 19400/40019, approximately 0.48477.
The new count is of order X/log X, not X/log(X)^r for a large fixed r.
Seven new result modules compile cleanly; fifteen audited declarations
use only propext, Classical.choice, and Quot.sound. See the final section.

This does NOT improve the strongest multiplicity exponent below, and it
does NOT settle the conjecture. Spec.lean remains unchanged with its sorry.
No auxiliary Lean proof repair or background build is pending.

## Latest verified fixed exponent: Chebyshev factorial-ratio improvement

The strongest completed unconditional result is now
`infinite_g_gt_chebyshev_uniform` in `Submission/ChebyshevCompositeGain.lean`:

```
for every gamma < 2064/4001,
  {n : Nat | (g n : Real) > (n : Real)^gamma}.Infinite.
```

Equivalently, the original inequality holds for every
`epsilon > 1937/4001` (approximately 0.484129), in particular every
`epsilon > 97/200`. This supersedes the earlier exponent 2041/4001.

The new arithmetic input is the eventual lower bound
`mangoldtSum N >= (9/10)*N`, proved from Chebyshev's factorial ratio and
Mathlib's Stirling theorem. It improves the structured progression lower
weight from 9/16 to 7/8 and the permitted rejected main weight from 17/32
to 27/32. The specialization is r=2000, t=4001, b=1937, h=64.

All new modules compile; the axiom audit uses only propext,
Classical.choice, and Quot.sound. No conditional lower bound was used as
an unconditional fact. The earlier IndependentCompositeBarrier bound
below 0.511 concerns the OLD coefficient condition with 17/32; it does
not apply to the new condition with 27/32.

The exact conjecture remains UNSOLVED. Spec.lean is unchanged with its
original sorry. There is no incomplete auxiliary proof or background
build pending. Full details are in the final section below.

## Latest verified fixed exponent: independent structured parameters

The strongest completed unconditional result is now
`Submission/IndependentCompositeGain.lean`:

```lean
infinite_g_gt_independent_uniform (γ : ℝ) (hγ : γ < 2041/4001) :
  {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite
```

Thus the original inequality is established for `ε > 1960/4001`,
in particular for every `ε > 49/100`, only. The exact original conjecture
is **UNSOLVED**. `Submission/Spec.lean` is unchanged and retains its
original `sorry`. No complete proof or disproof has been submitted.

The numerical conditions in this method cannot give thresholds even as
large as `511/1000`; this limitation is proved in
`Submission/IndependentCompositeBarrier.lean`. It is not an upper bound
on the actual multiplicities and does not disprove the conjecture.
There is no pending Lean repair or background build. See the final section
for the construction and its audit.

---

## Latest verified fixed exponent: endpoint correction retained

The strongest completed unconditional result is now
`Submission/EndpointCompositeGain.lean`:

```lean
infinite_g_gt_endpoint_composite_uniform (γ : ℝ) (hγ : γ < 53/105) :
  {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite
```

Thus the original inequality is established for `ε > 52/105` only.
The exact original conjecture is **UNSOLVED**. `Submission/Spec.lean`
is unchanged and retains its original `sorry`. No complete proof or
disproof has been submitted. See the final section for the development
and axiom audit. There is no pending Lean repair or background build.

---

# Status of the Erdős 821 development

The original theorem in `Spec.lean` is **not proved or disproved**. The file is unchanged
and retains its original `sorry`. Do not submit the auxiliary results as a settlement.

## Current strongest fixed exponent: binomial improvement

`BinomialCompositeGain.lean` and its check file compile cleanly, with fresh
result olean and permitted axioms only. The new unconditional range is

    gamma < 1/2 + 1/(2400000*Sieve.totientRatioAverageConstant + 10).

The gain above one half is more than 33 times the earlier gain with
80000000 in the denominator. This is a CONSTANT improvement, not an
exponent-increasing iteration and not a settlement. Detailed notes are at
the end of this log. Older references to the strongest 80000000 range
are now historical; dependent restricted-fiber files still state their
older ranges unless separately updated.

## Latest continuation: a uniform growing-cofactor reciprocal estimate

`GrowingCofactorReciprocals.lean` now compiles with a fresh olean and a clean
exact-type/axiom audit. For every fixed natural R, it proves reciprocal
convergence for prime parents p=a*q+1, q prime, with

    a <= 2^(R*Nat.sqrt(Nat.log 2 p)).

Unlike the previous fixed-cofactor result, the allowed cofactor genuinely grows
with p. The averaged sieve gives a summable normalized count O_R(m^(-3/2)) +
O(2^(-m)) at p<2^(128*m). The complementary primes retain reciprocal divergence
and satisfy cutoff(p)*q<p-1 for every prime factor q of p-1.

This remains a near-full-size factor bound: for fixed R the cutoff is subpower
in p. It does not provide the arbitrary fixed root smoothness needed for the
conjecture, and choosing R after p is not licensed by the theorem. `Spec.lean`
is unchanged and still contains its original `sorry`. Details are at the end.

## Latest continuation: unconditional reciprocal convergence for fixed cofactors

`PrimePairReciprocals.lean` compiles with a fresh olean and a clean type/axiom
audit. Using the existing two-prime Selberg bound, it proves reciprocal
convergence for q prime and a*q+1 prime at every fixed a>0. It also proves
convergence for the larger parent primes, for all cofactors in any fixed
bounded range, and for the corresponding canonical parents.

In particular, the locally admissible ten-form test pattern from the preceding
continuation is unconditionally reciprocal-summable, whether or not it occurs
infinitely often. Thus it does not obstruct an averaged estimate by itself.
The required estimate for cofactors growing with q remains unproved. The
finite-cofactor bounds cannot be summed over an unbounded union without an
additional argument. `Spec.lean` is unchanged with its original `sorry`.

## Latest continuation: an admissible-pattern test of pointwise contraction

`CanonicalParentMassTest.lean` now compiles and has a clean type/axiom audit.
It tests a proposed upper bound for the reciprocal mass of parents assigned to
their unique largest predecessor factor. The locally admissible coefficient
set {2,6,8,12,20,30,42,56,72} has reciprocal sum 73/72. Whenever q>=73 and q
and all nine forms a*q+1 are prime, these parents alone have normalized mass
strictly greater than one, already with the root parameter k=2.

An eventual pointwise contraction M_k(q)<=c/q with c<1 would therefore imply
that this admissible prime pattern occurs only finitely often. Infinitude of
the pattern was NOT proved or assumed, so this is not an unconditional
refutation of the proposed contraction, much less a disproof of Erdős 821.
It exposes an additional strong consequence of that candidate estimate.
No useful averaged contraction estimate was obtained. Details are in the last
section. `Spec.lean` remains unchanged with its original `sorry`.

## Latest continuation: growing-depth ancestor layers and full avoiding trees

The previously unfinished `GrowingLargeChildDepth.lean` now compiles cleanly.
`LargeChildMass.lean`, `GrowingLargeChildDepth.lean`,
`LargeChildAvoidingTrees.lean`, and `GrowingSmoothPrimeChains.lean` have fresh
oleans and clean exact-type/axiom audits. The propagation refactor and
`SparseSmoothPrimeChains.lean` were also rebuilt/rechecked. There is no pending
unfinished auxiliary Lean proof from this continuation.

Under the explicit hypothetical negation, some k>=3 and R>=1 satisfy, at
X_L = 2^(R*(2k)^(2L)), every fixed logarithmic saving for the depth-L ancestor
layer. Eventually at least half the primes <=X_L avoid that layer. In fact,
every eligible large-child branch from each such prime avoids the root-smooth
set through depth L; merely exhibiting one avoiding path is a weaker statement.
No contradictory upper bound on these full trees was proved. These remain
conditional results, not a proof or disproof of the conjecture. Details appear
in the final section below. `Spec.lean` is unchanged with its original `sorry`.

## Latest arithmetic application: structured predecessor prime factors

`StructuredPrimeFactors.lean` now converts the below-square-root distribution
estimate into a prime-count theorem. For every r,t with `2*r+1<=t`, eventually
at N=2^(64*t*m), there are at least `N/[C(r,t)*(m+1)^(r+1)]` primes p<=N whose
predecessors have at least r distinct prime divisors in
`(2^(64m), 2^(64(m+1))]`. Their prime-power contamination and overcount are both
controlled by the constant binomial coefficient `choose(t-1,r)`, not by the
number of moduli.

For r>=1 these predecessors are also `2^(64*(t-r)*m)`-smooth. The smoothness
exponent `(t-r)/t` remains greater than 1/2, so this does not improve the earlier
above-half multiplicity exponent or settle the conjecture. The file compiles
and its audit uses only the permitted axioms. Details are in the final section.
`Spec.lean` is still unchanged with its original `sorry`.

## Latest positive result: product-modulus distribution below square root

`UnbalancedVaughanMajorant.lean` and `CompositeBelowHalfScales.lean` now compile
and pass their exact-type/axiom audits. For every fixed r,t with `2*r+1<=t`
and every A, the absolute Mangoldt progression discrepancies over
`primeProductModuli r m`, at N=2^(64*t*m), are eventually at most
`N/(m+1)^A`. There is also an explicit error bound
`C(r,t)*(m+1)^5*N/2^m`.

This is an unconditional positive distribution result for the composite
modulus families. It is limited to the strictly below-square-root range.
It does not establish the cofinal near-full-level criterion and does not
improve the strongest previously proved multiplicity exponent. `Spec.lean`
is still unchanged with its original `sorry`. Detailed statements and the
cutoff choices are in the final section below.

## Latest continuation: grouped conductors and an exact cutoff barrier

Three new files compile and pass their exact-type/axiom audits:
`ConductorCompletionWeights.lean`, `ProductConductorMean.lean`, and
`ProductVaughanBarrier.lean`. They regroup the composite-modulus remainder
exactly, prove reciprocal completion bounds, apply the general Vaughan mean
estimate to each conductor group, and prove that the resulting majorant is
at least N at the cofinal-criterion scales with t>=4 **for every choice of
Vaughan cutoff functions**. Thus optimizing those cutoffs cannot close the
remaining gap using this particular bound.

This is a limitation of an explicit upper-bound formula, not a lower bound
on the actual prime error and not a disproof of the original conjecture.
No new multiplicity exponent was established. `Spec.lean` is unchanged and
still contains its original `sorry`. Detailed definitions and theorem names
are recorded in the final section below.

## Refined conditional route: only a cofinal one-sided smooth-modulus estimate is needed

`OneSidedDistributionCriterion.lean` proves

```lean
Erdos821.erdos_821_of_cofinal_smooth_modulus_condition :
  CofinalSmoothModulusCondition →
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite
```

The new sufficient condition only asks for an aggregate **signed deficit** over
the constructed smooth composite moduli. It needs arbitrarily large scales for
an unbounded set of parameters, not eventual absolute-error control over every
modulus at every parameter. The earlier geometric distribution hypothesis
implies it.

**This condition is still unproved.** No new unconditional multiplicity exponent
or higher-root shifted-prime estimate was obtained in this refinement. The
original conjecture in `Spec.lean` is unchanged and retains its `sorry`.

The new file compiles, has a built olean, and is audited in
`OneSidedDistributionCriterionCheck.lean`. All theorem types visibly retain
unresolved hypotheses, and all printed axiom dependencies are the permitted
three. The earlier `GeometricDistributionCriterion` was refactored to expose
the one-sided finite transfer; its previous public statements were preserved
and its audit rerun successfully.

## New conditional route: near-full progression distribution would settle the conjecture

`GeometricDistributionCriterion.lean` proves the complete implication

```lean
Erdos821.erdos_821_of_geometric_progression_distribution :
  GeometricProgressionDistribution →
    ∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite
```

**The distribution proposition remains unproved.** It is an explicit hypothesis,
not an axiom and not an unconditional theorem. Consequently this implication
cannot replace the `sorry` in `Spec.lean`.

The hypothesis asserts arbitrarily high logarithmic savings in the summed
absolute residue-one prime-count discrepancies, at geometric scales
`N=2^(64tm)` and modulus levels `Q=N^(1−1/t)`, for every fixed t≥3. This is an
Elliott–Halberstam-type input substantially stronger than the available
unconditional estimates. No equivalence with a standard external formulation
of Elliott–Halberstam has been claimed or formalized.

`SmoothCompositeModuli.lean` unconditionally supplies the large smooth squarefree
moduli and their polynomial reciprocal-mass lower bounds. Both new files compile,
have built oleans and dedicated `...Check.lean` audits showing only the permitted
axioms. The exact type of the full conditional implication visibly retains the
unproved distribution hypothesis.

## Latest series result: the full root-2 case, including reciprocal divergence

`SquareRootReciprocal.lean` now proves:

```lean
Erdos821.square_root_prime_reciprocal_divergence :
  ¬Summable ((rationalSmoothShiftedPrimes 2 1).indicator
    (fun p : ℕ => 1 / (p : ℝ)))

Erdos821.square_root_predecessor_series_divergence (s : ℝ) (hs : s ≤ 1) :
  ¬Summable ((smoothShiftedPredecessors 2).indicator
    (fun d : ℕ => (d : ℝ) ^ (-s)))
```

Thus the exact series criterion for the original conjecture is established at
root parameters 1 and 2, even at the reciprocal endpoint. It is **not**
established for arbitrary root parameters. `HigherRootReduction.lean` proves:

```lean
Erdos821.erdos_821_iff_higher_root_series :
  (∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite) ↔
    ∀ k : ℕ, 3 ≤ k → ∀ s : ℝ, s < 1 →
      ¬Summable ((smoothShiftedPredecessors k).indicator
        (fun d : ℕ => (d : ℝ) ^ (-s)))
```

The higher-root side remains an unproved hypothesis. The strongest verified
multiplicity lower bound is still the fixed exponent above one half described
below. **`Spec.lean` remains unchanged and unproved.**

New files `PrimeModulusReciprocals`, `SquareRootReciprocal`, and
`HigherRootReduction` compile and have built oleans and dedicated exact-type
and axiom audits (`...Check.lean`), all with only the three permitted axioms.
`SievedProgressionScales` was refactored to export its stronger reciprocal-weighted
count; its previous public count theorem is unchanged, and `AboveHalfLowerExponent`
was rebuilt successfully against it.

## Latest unconditional result: a fixed exponent above one half

`AboveHalfLowerExponent.lean` now proves:

```lean
Erdos821.exists_multiplicity_exponent_above_half :
  ∃ δ : ℝ, 1 / 2 < δ ∧ δ < 1 ∧
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ δ}.Infinite

Erdos821.exists_epsilon_cutoff_below_half :
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 2 ∧ ∀ ε : ℝ, ε₀ ≤ ε →
    {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite
```

This strictly improves the previous one-half limit. It remains a **fixed**
exponent improvement, not a sequence of exponents tending to one. The original
conjecture is still unresolved for `0 < ε < ε₀`, where ε₀ is the fixed positive
cutoff supplied by this result. `Spec.lean` is unchanged with its original
`sorry`; no purported settlement has been submitted.

The new files `StrongMangoldt`, `RoughProgressions`, `SievedProgressionScales`,
and `AboveHalfLowerExponent` compile and have built oleans. Their principal
results have audited exact types and depend only on `propext`, `Classical.choice`,
and `Quot.sound`. Audit files are `RoughProgressionsCheck` (also audits the two
main `StrongMangoldt` results), `SievedProgressionScalesCheck`, and
`AboveHalfLowerExponentCheck`.

## Earlier unconditional result: every exponent below one half

`HalfLowerExponent.lean` now proves, with no additional hypotheses:

```lean
Erdos821.infinite_g_gt_rpow_of_lt_half (γ : ℝ) (hγ : γ < 1 / 2) :
  {n : ℕ | (g n : ℝ) > (n : ℝ) ^ γ}.Infinite

Erdos821.erdos_821_of_half_lt (ε : ℝ) (hε : 1 / 2 < ε) :
  {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite
```

The range not covered by these particular theorems is `0 < ε ≤ 1/2`.
The newer fixed improvement above is stronger, but neither settles the
original conjecture. `Spec.lean` remains unchanged, and no proof has been
submitted. All newly listed files compile, have built oleans, and have exact-type
and axiom audits (`...Check.lean`) showing only `propext`, `Classical.choice`,
and `Quot.sound`.

## Verified files

- `Work.lean`: counting, exact support description, upper bounds, conditional reductions.
  Imports only `FormalConjecturesUtil`.
- `Sieve.lean`: a finite Selberg sieve, prime-pair bounds, and an unconditional fixed-scale
  estimate for smooth shifted primes. Imports only `FormalConjecturesUtil`.
- `Combined.lean`: imports `Submission.Work` and `Submission.Sieve` and combines their
  results. This is an auxiliary file, not the final submission.

The printed axiom dependencies of the results below are only `propext`,
`Classical.choice`, and `Quot.sound`.

## Main unconditional partial result

`Erdos821.exists_positive_power_multiplicity` in `Combined.lean` proves:

```lean
∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
  {n : ℕ | (g n : ℝ) > (n : ℝ) ^ δ}.Infinite
```

`Erdos821.exists_epsilon_cutoff` proves:

```lean
∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε : ℝ, ε₀ ≤ ε →
  {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite
```

The missing range is `0 < ε < ε₀`. Neither result gives exponents approaching one.

## Sieve results

The following are in namespace `Erdos821.Sieve`:

- `powerset_weighted_sum_moment`: first moment of a product-weighted subset.
- `half_euler_product_le_truncated_of_log_moment`: retains half the Euler product below
  a multiplicative cutoff if the logarithmic first moment is at most half its logarithm.
- `sum_prime_log_div_dyadic_le`: sum of `log p / p` over primes at most `2^L` is at most
  `2 * log 4 * L`, using Mathlib's Chebyshev upper bound.
- `pair_sieve_denominator_log_lower`: for even positive `M`, primes at most `2^L`
  not dividing `M`, and sieve level `2^(16L)`, the denominator is at least
  `(φ(M)/M * L * log 2)^2 / 2`.
- `prime_pair_explicit_bound`: bounds the number of `q < N` with both `q` and `a*q+1`
  prime by
  `2*N/(φ(2a)/(2a)*L*log 2)^2 + 2^(64L) + 2^(16L) + 1`.
- `totient_ratio_two_mul_harmonic_average`: bounds
  `sum_{1≤a≤A} (2a/φ(2a))^2/a` by `4*K*H_A`, where
  `K = exp(8 * sum_{n≥0} 1/n^2)` (the zero summand is zero).
- `dyadic_prime_count_lower`: `2^(L+1) ≤ (L+1)*(π(2^(L+1))+1)`.
- `rough_shifted_prime_explicit_bound`: combines prime-pair and average bounds.
- `smooth_shifted_primes_dyadic_count`: if `u` is a sufficiently large fixed integer,
  then for every sufficiently large `L`, at least `2^((128*u-1)*L)` primes at most
  `2^(128*u*L)` have predecessors `2^((128*u-5)*L)`-smooth.
- `exists_fixed_smooth_shifted_prime_density`: packages this as existence of one
  fixed `t ≥ 6`, with arbitrarily large scales `L` and at least `2^((t-1)*L)` such primes
  below `2^(t*L)`, with smoothness bound `2^((t-5)*L)`.

`Work.infinite_g_gt_fixed_power_of_weak_density` turns the last statement into the
exponent `2/t`. Increasing `t` decreases this exponent. Increasing `L` only produces
larger witnesses. No exponent-improving iteration has been proved.

## Exact characterization of the full conjecture

In `Work.lean`:

```lean
def smoothShiftedPredecessors (k : ℕ) : Set ℕ :=
  {d | (d + 1).Prime ∧ ∀ q ∈ d.primeFactors, q ^ k ≤ d}
```

`erdos_821_iff_smooth_shifted_nonsummable` proves equivalence of the original conjecture
with:

```lean
∀ k : ℕ, 1 ≤ k →
  ¬ Summable ((smoothShiftedPredecessors k).indicator
      (fun d : ℕ => (d : ℝ) ^ (-(1 - 1 / (2 * (k : ℝ))))))
```

Neither side of this equivalence is established unconditionally.

The necessity proof uses `g_le_of_summable_smooth_shifted` and
`exists_sum_primeFactors_rpow_le_log`: if the smooth shifted-prime series is summable
at a suitable exponent below one, rough contributions are subpower and `g(n)` has an
eventual fixed power upper bound below one.

The sufficiency proof uses `summable_indicator_rpow_of_dyadic_count`,
`dyadic_density_of_not_summable_smooth_shifted`, and
`erdos_821_of_dyadic_smooth_prime_density`.

The latter density hypothesis requires, for **every** `t ≥ 5`, arbitrarily large `L`
and at least `2^((t-1)*L)` primes below `2^(t*L)` with predecessors `2^L`-smooth.
This differs crucially from the unconditional sieve estimate, whose bound is
`2^((t-5)*L)` for one fixed large `t`.

## Strengthened reductions in `Density.lean`

`Submission/Density.lean` imports `Submission.Work` and compiles without `sorry`.
The printed axioms of its main results are only `propext`, `Classical.choice`,
and `Quot.sound`.

- `smoothShiftedPredecessors_antitone` gives monotonicity in the root parameter.
- `erdos_821_iff_smooth_shifted_all_exponents` strengthens the series formulation:
  the original conjecture is equivalent to divergence of the smooth shifted-prime
  series for **every** `k ≥ 1` and **every real exponent** `s < 1`.
- `infinite_smooth_shifted_of_erdos_821` records the weaker consequence that each
  root-smooth shifted-prime set is infinite.
- `erdos_821_iff_full_dyadic_density` gives another exact equivalent formulation:
  for every independent pair `k ≥ 1`, `t ≥ 2`, and every `M`, some `L ≥ M` satisfies
  ```lean
  2 ^ ((t - 1) * L) ≤
    ((Finset.range (2 ^ (t * L))).filter
      (fun d => d ∈ smoothShiftedPredecessors k)).card
  ```
  Thus, at each fixed root-smoothness scale, the counting exponent must approach
  one along arbitrarily large scales.

These are new verified reductions, not new unconditional arithmetic estimates.
Neither the series nor the density side has been established. In particular,
ordinary prime infinitude or divergence of the prime reciprocal sum does not
supply the corresponding statement on these restricted shifted-prime sets.

Build with `lake env lean Submission/Density.lean` after building `Work.lean`.

## Large smooth moduli route in `Progressions.lean`

`Submission/Progressions.lean` imports `Submission.Work`, compiles without
`sorry`, and its printed axiom dependencies are the permitted three.

Unconditional finite lemmas:
- `smooth_of_large_smooth_divisor`: if a positive integer `m` has a `y`-smooth
  divisor `d` and `m < d*y`, then `m` is itself `y`-smooth.
- `squarefree_divisor_count_le_choose`: squarefree divisors with exactly `r`
  prime factors inject into the `r`-element subsets of the prime support of `m`.
- `card_primeFactors_le_of_le_two_pow`: `0 < m ≤ 2^E` implies at most `E`
  distinct prime factors.
- `large_smooth_moduli_ap_sum_le`: if all `d ∈ D` are squarefree and `y`-smooth,
  have `r` prime factors, and satisfy `2^E ≤ d*y`, then
  ```text
  sum_{d in D} #{p in P : d divides p-1}
    ≤ #{p in P : p-1 is y-smooth} * E^r
  ```
  for any finite family `P` of primes at most `2^E`.

`erdos_821_of_large_smooth_moduli_ap_counts` gives a new conditional application.
For every `t ≥ 5`, at arbitrarily large `L`, it asks for smooth squarefree moduli
`D`, each with `t` prime factors and `2^(tL) ≤ d*2^L`, whose summed progression
counts up to `2^(tL)` are at least `(tL)^t * 2^((t-1)L)`. The finite lemmas
then supply the dyadic smooth-prime density criterion and hence the conjecture.

**The progression-count lower bound is unproved.** The library's Dirichlet
theorem gives infinitude for each fixed modulus, not uniform bounds as the
moduli grow with the prime cutoff. No proof of the needed distribution estimate
was found. This route therefore has not settled the original theorem.

Build: `lake env lean Submission/Progressions.lean` (requires the `Work` olean).

## New unconditional valuation bounds in `Valuation.lean`

`Submission/Valuation.lean` imports `Submission.Work` and compiles with only the
permitted axioms. It contains new unconditional upper bounds, not a settlement.

- `polynomial_le_constant_mul_two_pow`: `(e+1)^k ≤ k! * 2^k * 2^e`, proved
  using ascending factorials and the binomial coefficient bound.
- `card_divisors_pow_le`: for `n ≠ 0`,
  ```text
  (# divisors of n)^k ≤ (k! * 2^k)^(2^k) * n.
  ```
- `eventually_card_divisors_le_rpow`: the divisor count is eventually at most
  `n^ε` for every fixed positive real `ε`.
- `admissibleSupport_card_le_two_valuation`: an admissible support has at most
  `n.factorization 2 + 1` primes, because each odd prime contributes a factor
  of two to the product of predecessors dividing `n`.
- `g_le_divisor_polynomial_of_two_valuation_le`: if `v₂(n) ≤ K` and `n > 0`,
  ```text
  g(n) ≤ (K+2) * (τ(n)+1)^(K+1).
  ```
- `finite_g_gt_rpow_of_two_valuation_le`: for every `K` and `δ > 0`, only
  finitely many `n` with `v₂(n) ≤ K` have `g(n) > n^δ`.
- `finite_g_gt_rpow_on_squarefree`: in particular squarefree output values
  cannot witness any positive-power lower bound infinitely often.
- `finite_g_gt_rpow_not_dvd_two_pow`: all but finitely many witnesses to any
  fixed positive-power lower bound are divisible by `2^K`, for every fixed `K`.
- `infinite_g_gt_rpow_and_dvd_two_pow`: any infinite positive-power witness set
  remains infinite after requiring divisibility by a prescribed `2^K`.

This excludes a new family (bounded 2-adic valuation, even with unbounded prime
support), but does not disprove the original conjecture: witness valuations
can tend to infinity. No uniform bound in growing `K` settles the full exponent.

Build: `lake env lean Submission/Valuation.lean` (requires the `Work` olean).




## Sharp constant bound in `SmallValuation.lean`

`Submission/SmallValuation.lean` imports `Submission.Valuation` and compiles with
only `propext`, `Classical.choice`, and `Quot.sound`.

- `g_le_four_of_not_four_dvd`: `¬4 ∣ n → g n ≤ 4`.
- `g_le_four_of_squarefree`: `Squarefree n → g n ≤ 4`.
- `g_six_eq_four`: `g 6 = 4`, so the constant is sharp.

The argument classifies admissible supports when `4 ∤ n`. There is at most one
odd prime in a support. That prime must be either `n+1` or the largest prime
factor of `n`. For `n > 2` a support must contain an odd prime, leaving at most
four possibilities (the two odd-prime choices, with or without the prime 2).
The cases `n = 1, 2` are handled by the existing finite support bound.

This is a new unconditional exact bound on a restricted family, not a disproof
of Erdős 821. The original conjecture remains unproved for unrestricted outputs.

Build: `lake env lean Submission/SmallValuation.lean`; its `Valuation` olean
must be built first.

## Build notes

To refresh auxiliary imports after changing source proofs:

```sh
mkdir -p .lake/build/lib/lean/Submission
lake env lean -o .lake/build/lib/lean/Submission/Work.olean Submission/Work.lean
lake env lean -o .lake/build/lib/lean/Submission/Sieve.olean Submission/Sieve.lean
lake env lean Submission/Combined.lean
```

For a genuine final solution, all needed helpers must be copied into `Spec.lean`.
Its original import must remain unchanged; auxiliary imports must not be added.

## Doubling is not a monotone amplification (`Doubling.lean`)

`Submission/Doubling.lean` imports `Submission.Work` and compiles without
`sorry`. Its printed axiom dependencies are exactly the permitted three.

New exact results:

```lean
g_two_pow_31 : g (2 ^ 31) = 33
g_two_pow_32 : g (2 ^ 32) = 32
exists_g_double_lt : ∃ n : ℕ, 0 < n ∧ g (2 * n) < g n
```

The proof classifies shifted-prime divisors of both outputs as
`{2, 3, 5, 17, 257, 65537}`. The next possible Fermat number,
`4294967297`, is composite because it is divisible by `641`. The exact
support formula then reduces each cardinality calculation to a finite
powerset of six primes; ordinary kernel-checked `decide` completes the counts.
No `native_decide` is used.

This rules out monotonicity under doubling (and hence unrestricted
monotonicity under divisibility) as an elementary amplification principle.
It does **not** disprove the original conjecture, nor does it improve the
known fixed positive exponent.

Build: `lake env lean Submission/Doubling.lean` (requires `Work.olean`).

## Prime-factor stripping (`PrimeStripping.lean`)

`Submission/PrimeStripping.lean` imports `Submission.Valuation`, compiles without
`sorry`, and its main theorems have only the three permitted axiom dependencies.

New finite estimate, for a prime `q`, `n > 0`, and `v_q(n) ≤ K`:

```text
g(n) ≤ (K+1) (τ(n)+1)^K ∑_{d | n/q^{v_q(n)}} g(d).
```

Lean name: `g_le_valuation_factor_mul_sum_ordCompl`.

The support is split into the primes `p` with `q | p-1` and the remaining primes.
The first part has at most `v_q(n)` elements. The product of the predecessors
of the remaining primes is a divisor of the `q`-free part of `n`, and this
remaining support is admissible for that divisor. The pair of support parts
recovers the original support injectively.

Combining this with the divisor subpower estimate and the global
`g(d) ≤ C_η d^(1+η)` upper bound proves:

```lean
eventually_g_le_rpow_of_large_prime_factor (K : ℕ) (hK : 1 ≤ K)
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, q.Prime → q ∣ n → n ≤ q ^ K →
      (g n : ℝ) ≤ (n : ℝ) ^ (1 - 1 / (K : ℝ) + η)
```

`finite_large_prime_factor_g_gt_rpow` states the corresponding finiteness result.
Thus a prime divisor at least the `K`-th root of the output forces a loss of
`1/K` in the multiplicity exponent, up to any fixed positive error.

**This is not a disproof:** it excludes only outputs with a relatively large
prime divisor. Smooth outputs remain possible. It does not supply new smooth
shifted-prime density estimates or amplify the unconditional lower exponent.
`Spec.lean` remains unproved and unchanged.

Other reusable helpers:
- `admissibleSupport_filter_card_le_valuation`
- `admissibleSupport_prime_free_part`
- `exists_g_le_constant_mul_rpow`
- `eventually_const_mul_divisors_pow_le_rpow`
- `g_le_constant_mul_divisors_pow_mul_ordCompl_rpow`
- `ordCompl_le_rpow_of_le_prime_pow`

Build: `lake env lean Submission/PrimeStripping.lean` (requires `Valuation.olean`).

## Global sublinearity (`Sublinear.lean`)

`Submission/Sublinear.lean` imports `Submission.Work` and `Submission.Sieve`,
compiles without `sorry`, and its principal theorems use only `propext`,
`Classical.choice`, and `Quot.sound`. An olean has been built.

New **unconditional global** results:

```lean
eventually_g_le_mul (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ ε * n

g_isLittleO_id :
    (fun n : ℕ => (g n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ))

tendsto_g_div_self :
    Tendsto (fun n : ℕ => (g n : ℝ) / n) atTop (nhds 0)

eventually_g_lt_self : ∀ᶠ n : ℕ in atTop, g n < n
```

This improves the previous global upper bound `g(n) ≤ n^(1+ε)` eventually.
**It is NOT a disproof of the original conjecture:** a function can be `o(n)`
and still exceed `n^(1-ε)` infinitely often for every fixed `ε > 0`.
`Spec.lean` remains unchanged with its original `sorry`.

Proof details:

1. `average_prime_product_le` proves an unweighted average bound by expanding
   a prime-factor product over subsets and counting multiples.
2. `totient_ratio_average` shows
   ```text
   ∑_{1≤m≤M} (m/φ(m))² ≤ C M,
   C = exp(8 * ∑_{j≥0} 1/j²).
   ```
   This uses the same constant as `Sieve.totientRatioAverageConstant`.
3. `totient_fiber_tail_card_le` uses dyadic intervals to bound the number of
   preimages of `n` at least `B` by `4 C n²/B`.
4. `bounded_totient_fiber_card_le` bounds the preimages at most `M` by
   ```text
   3 M/y + 2^(# primes < y) * sqrt(M).
   ```
   Split them into fixed-`y`-smooth inputs; inputs divisible by a square
   `d²` with `d≥y`; and inputs with a prime factor `p≥y` appearing once.
   In the last class, writing `m=a*p` determines
   `p=n/φ(a)+1`, giving at most `M/y` inputs. The square-divisor class has
   at most `2M/y` elements by a telescoping reciprocal-square estimate.
5. Splitting at `A*n` yields `g_le_linear_coeff_sqrt`:
   ```text
   g(n) ≤ (4C/A + 3A/y)n + 2^(# primes < y) sqrt(A*n).
   ```
   Choose `A`, then `y`, then let `n` grow.

Other helper names:
- `card_multiples_Icc_le_div`
- `totient_fiber_block_card_le`
- `sum_Icc_inv_sq_le`
- `card_large_square_divisor_le`
- `card_fiber_large_prime_once_le`
- `eventually_const_mul_sqrt_mul_le`

Build: `lake env lean Submission/Sublinear.lean` (requires `Work.olean` and
`Sieve.olean`). There is one harmless linter warning.

### Quantitative sublinearity threshold (verified)

`Sublinear.g_le_div_of_two_pow_sq_le` now compiles, and its printed dependencies
are only `propext`, `Classical.choice`, and `Quot.sound`. The `Sublinear` olean
has been refreshed.

```lean
g_le_div_of_two_pow_sq_le (n k : ℕ) (hk : 2 ≤ k)
    (hn : 2 ^ (4 * k ^ 2) ≤ n) :
    (g n : ℝ) ≤ (4 * Sieve.totientRatioAverageConstant + 4) * n / k
```

The proof applies the finite estimate with `A = k`, `y = k²`, bounds
`2^(# primes < k²)` by `2^(k²)`, and absorbs the square-root term into `n/k`.
This gives an order `n / sqrt(log n)` upper bound. It is **not** a fixed power
saving, so it neither disproves nor proves the conjecture. `Spec.lean` is still
unchanged with its original `sorry`.

## Coprime fiber-product obstruction (`FiberProducts.lean`)

New auxiliary file, importing `Submission.Valuation`:

- `card_coprime_totient_fiber_le_divisors`: for `n > 1`, a pairwise-coprime
  finite family `S` with `φ(m)=n` for all `m∈S` has `|S| ≤ τ(n)`.
  Map each member to `minFac(m)-1`, a divisor of `n`; coprimality makes this
  map injective.
- `eventually_card_coprime_totient_fiber_le_rpow`: for every `e>0`, eventually
  all such families have `|S| ≤ n^e`, uniformly over `S`.
- `eventually_choose_coprime_totient_fiber_le_rpow`: uniformly also over every
  `r`, the number `choose(|S|,r)` of subset-product choices is at most `(n^r)^e`.
- `eventually_exists_not_coprime_of_large_totient_fiber`: every polynomial-size
  finite fiber family at sufficiently large outputs contains distinct members
  that are not coprime.

This excludes amplification by first extracting a polynomial-size *mutually*
coprime family from a single fiber. It does **not** bound all coprime tuples in
a large fiber, nor rule out other correlated constructions. For noncoprime
products the identity
`φ(gcd(a,b))*φ(a*b) = φ(a)*φ(b)*gcd(a,b)` introduces a nonconstant correction,
so the naive product argument does not preserve one common output.
No exponent-improving lower bound has been obtained. `Spec.lean` remains
unchanged, and the conjecture remains unproved and undisproved.

The file compiles and its main results depend only on the permitted axioms.
Build: `lake env lean Submission/FiberProducts.lean` (requires `Valuation.olean`).

## Check of the converse reduction

`Submission/CheckTypes.lean` was used to inspect the elaborated statements of
both the series/counting equivalences and the fixed-scale sieve theorem. The
equivalences have no additional implicit mathematical hypotheses. This check
did not identify a defect or supply any new unconditional density estimate.
The weak fixed smoothness bound remains compatible with sparsity at a much
smaller root scale, so no contradiction proving the full conjecture was found.

## Every logarithmic saving (`Rankin.lean`)

`Submission/Rankin.lean` imports `Submission.Sublinear`, compiles, and has a
fresh olean. All six printed main theorem dependencies are exactly the three
permitted axioms. There are three harmless linter warnings.

New unconditional results:

```lean
eventually_g_le_div_log_pow (r : ℕ) (hr : 1 ≤ r) :
  ∀ᶠ n : ℕ in atTop,
    (g n : ℝ) ≤ (4 * Sieve.totientRatioAverageConstant + 4) * n /
      (Nat.log 2 n : ℝ)^r

g_mul_log_pow_isLittleO_id (r : ℕ) :
  (fun n : ℕ => (g n : ℝ) * (Nat.log 2 n : ℝ)^r) =o[atTop]
    (fun n : ℕ => (n : ℝ))

tendsto_g_mul_log_pow_div_self (r : ℕ) :
  Tendsto (fun n : ℕ => ((g n : ℝ) * (Nat.log 2 n : ℝ)^r) / n)
    atTop (nhds 0)
```

These improve `Sublinear`'s logarithmic upper estimate to every fixed power of
the logarithm. They still do **not** imply a fixed power upper bound below one,
and therefore do not disprove Erdős 821. They supply no new lower bound.
`Spec.lean` is unchanged and still contains its original `sorry`.

### Proof components

- `smoothRankinConstant s u` is
  `(1 - 2^(-s))⁻¹ * ∑' a : ℕ, (a : ℝ)^(-u)`.
- `smooth_euler_product_le_rankin`: for `s>0`, `s≤u`, `u>1`, the smooth
  Euler product is at most `exp(C(s,u) * y^(u-s))`.
  The pointwise inequality `(1-z)⁻¹ ≤ exp(z/(1-z))` and the convergent
  series at exponent `u` suffice; no new prime-distribution estimate is used.
- `card_smooth_family_le_rankin`: a family of `y`-smooth positive integers
  at most `M` has size at most `M^s * exp(C(s,u)*y^(u-s))`.
- `bounded_totient_fiber_card_le_rankin` and `g_le_linear_coeff_rankin`
  replace the earlier square-root smooth-count bound in the three-way split.
- `eventually_pow_mul_exp_sqrt_le_exp`: fixed powers times `exp(C sqrt(L))`
  are absorbed by `exp(b L)`, for every fixed `b>0`.
- `g_le_div_pow_of_two_pow_le`: for each `r≥1`, eventually in `L`, uniformly
  for every `n≥2^L`, `g(n) ≤ (4C+4)*n/L^r`. Choose
  `A=L^r`, `y=L^(2r)`, `e=1/(8r)`, `s=1-e`, `u=1+e`.
  Then `y^(u-s)=sqrt(L)`; the smooth term is at most `n/A`.
- Choose `L=Nat.log 2 n`, and use the bound with `r+1` to obtain little-o
  at exponent `r`.

At a polynomial cutoff `y=n^a` with fixed `a>0`, the exponential error in
this Rankin estimate overwhelms a fixed power saving. Thus the current method
has not closed the gap to a proof or disproof.

Build: `lake env lean Submission/Rankin.lean` (requires `Sublinear.olean`).
`RankinCheck.lean` is only a disposable API diagnostic file, not a proof file.

## Improved fixed-exponent lower bounds (`LowerExponent.lean`)

`Submission/LowerExponent.lean` imports Work and Sieve, compiles, and has a
fresh olean. Its six printed main theorem dependencies are only the permitted
three axioms. The main new unconditional result is:

```lean
exists_fixed_scale_full_exponents :
  ∃ t : ℕ, 6 ≤ t ∧ ∀ δ : ℝ, 0 < δ → δ < 5 / (t : ℝ) →
    {n : ℕ | (g n : ℝ) > (n : ℝ)^δ}.Infinite
```

This improves the previous exponent `2/t` from the same elementary sieve
scale, by preserving its stronger prime count and reducing integer rounding
losses in the pigeonhole step. **The parameter `t` is fixed by the sieve's
large constant and cannot be chosen freely or made near five.** Increasing
the new rescaling parameter `m` gives exponents tending to `5/t`, NOT to one.
The full conjecture is still unproved and undisproved. Spec remains unchanged
with its original `sorry`.

### Proof components

1. `general_smooth_prime_counting_margin` and
   `large_g_of_general_dyadic_smooth_primes` use parameters `(t,a,b)`:
   primes up to `2^(tL)`, at least `2^(aL)` choices, predecessors
   `2^(bL)`-smooth. With `k=2^((b+1)L)`, the finite construction supplies
   multiplicity above `2^((a-b-2)Lk)` at an output at most `2^(tLk)`.
2. `infinite_g_gt_of_general_dyadic_density` converts this to exponent
   `(a-b-2)/t`. The assumptions are `b+4≤t`, `b+3≤a`, and `a≤t`.
3. `Sieve.exists_eventual_fixed_smooth_shifted_prime_density` records that
   the old weak sieve count holds at EVERY sufficiently large scale, enabling
   substitution of `mL`. This alone gives every exponent below `4/t` via
   `infinite_g_gt_of_scaled_eventual_weak_density` and
   `exists_fixed_scale_improved_exponents`.
4. `Sieve.smooth_shifted_primes_dyadic_full_count` retains a stronger conclusion
   already available inside the old proof:
   ```text
   2^(tL) ≤ 2(tL)(#P + 1),   t=128u,
   P = {p≤2^(tL) prime : p-1 is 2^((t-5)L)-smooth}.
   ```
   The proof reuses the same prime-pair upper bound, harmonic average,
   prime-count lower bound and constants. No new analytic input is supplied.
5. `Sieve.exists_eventual_full_smooth_shifted_prime_density` packages the
   stronger count for all large scales.
6. At scale `mL`, for sufficiently large `L`, the logarithmic denominator
   costs less than `2^L`. Thus use parameters
   `T=tm`, `a=tm-1`, `b=(t-5)m` in the general construction.
   `infinite_g_gt_of_scaled_eventual_full_density` gives exponent
   `(5m-3)/(tm)`. Taking `m` sufficiently large gives every `δ<5/t`.

This is a genuine improvement of the counting transfer, but leaves the same
missing analytic input: arbitrarily small root-smoothness scales for shifted
primes. It is not an exponent-improving iteration toward one.

Build: `lake env lean Submission/LowerExponent.lean` (requires Work and Sieve
oleans). There are three harmless unused-variable linter warnings.

## Search for an additional arithmetic input

A search of Mathlib's number-theory and analysis modules found no applicable
Bombieri–Vinogradov, Elliott–Halberstam, large-sieve, or averaged growing-modulus
prime-count estimate. The inspected `LSeries/PrimesInAP.lean` proves fixed-modulus
Dirichlet infinitude (via a divergent weighted prime series); `SelbergSieve.lean`
provides an upper-bound sieve framework. Neither supplies the progression lower
bound required by `Progressions.lean`.

The scale mismatch is substantive: to force a predecessor `p-1≤X` to be
`X^θ`-smooth using a smooth divisor `d`, the existing criterion needs
`d ≳ X^(1-θ)`. Taking `X` arbitrarily large for a fixed modulus `d`, as allowed
by qualitative Dirichlet, does not maintain this inequality. No new uniform
arithmetic estimate or settlement was obtained in this investigation.

## Common input-factor reduction (`CommonFactor.lean`)

`Submission/CommonFactor.lean` imports `Submission.Valuation`, compiles with
only the three permitted axioms, and has a fresh olean.

The main finite reduction is:

```lean
exists_reduced_totient_fiber_of_common_factor (S : Finset ℕ) (n d : ℕ)
    (hd : 0 < d) (hS : ∀ m ∈ S, totient m = n ∧ d ∣ m) :
    ∃ n' : ℕ, n' ≤ n / totient d ∧ S.card ≤ d.divisors.card * g n'
```

For a fixed overlap `c = gcd(d,m/d)`, the exact identity is

```text
φ(m/d) = φ(c) n / (φ(d) c).
```

Division by `d` is injective on multiples of `d`, so the subfamily with this
fixed overlap injects into one smaller fiber. The possible overlaps are
positive divisors of `d`, giving the factor `τ(d)`. The reduced output is at
most `n/φ(d)` because `φ(c)≤c`.

If every quotient is coprime to `d`, there is no multiplicity loss:
`card_totient_fiber_le_g_div_of_common_coprime_factor` gives
`|S| ≤ g(n/φ(d))`.

A verified finite obstruction to inferring a common prime from pairwise
noncoprimality is recorded as `common_factor_obstruction`:

```text
φ(21)=φ(28)=φ(36)=12,
gcd(21,28)=7, gcd(21,36)=3, gcd(28,36)=4,
gcd(21,28,36)=1.
```

**No general extraction theorem supplying a sufficiently large common input
divisor has been proved.** High valuations in the *output* do not supply such
a divisor in the inputs; squarefree products of odd primes can have totients
with large 2-adic valuation. The finite reduction therefore does not improve
the unconditional exponent or settle Erdős 821. Spec remains unchanged with
its original `sorry`.

Other theorem names:
- `totient_div_of_common_factor_gcd`
- `card_totient_fiber_le_g_div_of_fixed_gcd`
- `common_factor_reduced_output_le`

Build: `lake env lean Submission/CommonFactor.lean` (requires Valuation.olean).
`CommonFactorCheck.lean` is a disposable API diagnostic, not a proof file.

## Squarefree-input equivalence (`SquarefreeInput.lean`)

`Submission/SquarefreeInput.lean` imports `Submission.Valuation`, compiles
without warnings or errors, and has a fresh olean. Its printed axiom lists
contain only `propext`, `Classical.choice`, and `Quot.sound`.

Define
```lean
noncomputable def gSquarefree (n : ℕ) : ℕ :=
  {m : ℕ | Squarefree m ∧ totient m = n}.ncard
```

The radical map `m ↦ ∏ p ∈ m.primeFactors, p` is injective on a fixed totient
fiber: prime support plus totient determines the input. Its image is squarefree
and its totient divides the original output. Partitioning this image by its
totient proves, for `n>0`,

```text
gSquarefree(n) ≤ g(n) ≤ ∑_{d|n} gSquarefree(d).
```

Consequently there is a divisor `d|n` such that
`g(n) ≤ τ(n) gSquarefree(d)`.

The transfer lemma `infinite_gSquarefree_gt_of_infinite_g_gt` proves that for
any `α>0`, `β>0`, infinitude of `g(n)>n^(α+β)` implies infinitude of positive
`d` with `gSquarefree(d)>d^α`. It uses the eventual divisor bound `τ(n)≤n^β`.
To show that the selected divisors are unbounded, the proof chooses `n^α`
above the maximum of `gSquarefree` on any prescribed finite initial segment.

Finally, `erdos_821_iff_squarefree_inputs` proves the exact equivalence
```lean
(∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite) ↔
  ∀ ε > (0 : ℝ),
    {n : ℕ | (gSquarefree n : ℝ) > (n : ℝ) ^ (1 - ε)}.Infinite
```

This restriction concerns squarefree **inputs**, not squarefree outputs.
It supplies no new lower bound on smooth shifted primes and does not settle
the conjecture. `Spec.lean` remains unchanged with its original `sorry`.

Other theorem names:
- `finite_squarefree_totient_fiber`
- `gSquarefree_le_g`
- `squarefree_prod_of_primes`
- `radical_injOn_totient_fiber`
- `g_le_sum_gSquarefree_divisors`
- `exists_divisor_large_gSquarefree`

Build: `lake env lean Submission/SquarefreeInput.lean` (requires Valuation.olean).
`SquarefreeInputCheck.lean` is a disposable API diagnostic.

## Audit of parameter optimization (`SieveBarrier.lean`)

`Submission/SieveBarrier.lean` imports `Submission.Sieve`, compiles without
warnings or errors, and has a fresh olean. Printed axioms are only the three
permitted axioms.

The file defines the EXACT dyadic specialization of the existing upper bound:

```text
B(E,a,J) = 16 C 2^E H_(2^a)/(J log 2)^2
           + 2^a (2^(64J) + 2^(16J) + 1),
C = Sieve.totientRatioAverageConstant.
```

`rough_shifted_prime_card_le_dyadicRoughSieveBound` verifies its connection to
the rough-prime bound at `X=2^E`, `A=2^a`, `Y=2^(E-a)` (assuming `a≤E`, `J>0`).

Two limitations of this particular numerical bound are now formalized:

1. If `E≤2a`, `E>0`, and `J>0`, then `B(E,a,J)≥2^E/E`, for EVERY sieve parameter
   `J`. Thus the direct certificate is nonpositive for `Y≤sqrt(X)`.
2. More sharply,
   ```lean
   positive_direct_sieve_certificate_requires_small_cofactor (E a J : ℕ)
       (hE : 0 < E) (hJ : 0 < J)
       (hbound : dyadicRoughSieveBound E a J < (2 : ℝ)^E / E) :
       65536 * a < E
   ```

For (2), the error term forces `a+64J<E`. The main term, using `C≥1`,
`H_(2^a)≥a log 2`, and `0<log 2≤1`, forces `16aE<J^2`. Together these imply
`65536a<E`. This bound is deliberately conservative: it ignores the large
actual value of `C` and retains only `C≥1`.

The prime-count estimate used earlier is `π(2^E)+1≥2^E/E`, so the actual direct
lower bound for the smooth-prime count is `2^E/E - 1 - B(E,a,J)`. The obstruction
even applies to the more generous certificate without the `-1`.

**These are statements about a proved upper-bound expression, not upper bounds
on the true smooth-prime count.** They do NOT disprove the conjecture, do NOT
show a limitation of all sieve methods, and do NOT bound the true maximal
multiplicity exponent. They rule out obtaining the missing near-one exponents
merely by optimizing parameters in this particular direct-subtraction bound.

No new arithmetic lower bound was obtained. `Spec.lean` remains unchanged with
its original `sorry`. Build: `lake env lean Submission/SieveBarrier.lean`.

## Popular-prime extraction (`PopularPrime.lean`)

`Submission/PopularPrime.lean` imports `Submission.CommonFactor` and
`Submission.SquarefreeInput`. It compiles without warnings or errors, has a
fresh olean, and its printed axiom lists contain only the permitted axioms.

The initial idea was to use a maximal pairwise-coprime subfamily to obtain a
small prime transversal. Inspection revealed that the simpler existing bound
is stronger: every input prime belongs to `shiftedPrimeDivisors n`, whose
cardinality is at most `τ(n)`. No maximal-subfamily argument is needed.

The new finite results are:

1. `exists_popular_prime_of_totient_fiber_cover`: if every member of a nonempty
   finite fiber `S` has a prime factor at least `y`, then some prime `p≥y` with
   `p-1|n` satisfies
   ```text
   |S| ≤ τ(n) * #{m∈S : p|m}.
   ```
   The cutoff assumption is explicit, not established unconditionally.
2. `exists_popular_prime_of_totient_fiber`: the unqualified version for `n>1`.
3. `exists_popular_prime_reduction`: combining with `CommonFactor.lean` gives
   an output `n'≤n/(p-1)` with `|S|≤2τ(n)g(n')`. The extra factor two accounts
   for the possible gcds `1` and `p` between the removed prime and its quotient.
4. `exists_popular_prime_reduction_squarefree_odd`: for squarefree odd inputs,
   there is a prime `p≥3`, `p-1|n`, such that
   ```text
   n/(p-1) < n,
   |S| ≤ τ(n) g(n/(p-1)).
   ```
   Squarefreeness removes the overlap loss and oddness rules out `p=2`.
5. `eventually_popular_prime_reduction_squarefree_odd`: for every fixed `ε>0`,
   replace the loss `τ(n)` in (4) by `n^ε` once `n` is sufficiently large.

**The size of the selected prime is still uncontrolled.** A prime bounded
independently of `n` gives only a constant-factor decrease in output, whereas
the multiplicity loss may grow with `n`. Strict descent of the output is not
an exponent-improving iteration. No lower bound `p-1≥n^η` for fixed `η>0` was
proved, and no large common composite divisor was extracted with a suitable
loss bound. This investigation does not settle the conjecture.

`Spec.lean` remains unchanged and retains its original `sorry`.
Build: `lake env lean Submission/PopularPrime.lean`.

## Polynomial-size fibers with no polynomially large input primes

`Submission/SmoothInputFamilies.lean` imports `Submission.SquarefreeInput` and
`Submission.Sieve`. It compiles without warnings or errors, has a fresh olean,
and its printed axiom lists contain only the three permitted axioms.

This follows the actual inputs in the old lower-bound construction. It does
not improve the multiplicity exponent or prove the full conjecture.

1. `large_squarefree_fiber_of_smooth_shifted_primes` strengthens the finite
   pigeonhole result by retaining the selected finite fiber `R`. Each input
   is squarefree and has exactly `k` prime factors drawn from `P`. The output
   additionally satisfies `2^(k-1)≤n`: all but possibly the prime 2 contribute
   at least a factor of two to its totient.
2. `root_smooth_input_fibers_of_weak_density` uses the old fixed-scale sieve
   with `k=2^((t-4)L)`. Taking `L≥tr+2` ensures `tLr≤k-1`. Thus every input
   prime `p≤2^(tL)` satisfies `p^r≤2^(k-1)≤n`.
3. `exists_fixed_power_root_smooth_input_fibers` proves unconditionally:
   ```lean
   ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ r N : ℕ,
     ∃ (n : ℕ) (R : Finset ℕ), N < n ∧ (n : ℝ)^δ < R.card ∧
       ∀ m ∈ R, Squarefree m ∧ totient m = n ∧
         ∀ p ∈ m.primeFactors, p^r ≤ n
   ```
   Here `δ=2/t` for the fixed sieve parameter. The exponent does not depend
   on `r` or `N`.
4. `exists_fixed_power_fibers_without_large_input_primes` converts the last
   assertion to strict real bounds: for every fixed `η>0`, every input prime
   in the selected polynomial-size family satisfies `p<n^η`.
5. `exists_odd_squarefree_subfiber` removes a possible factor of two. This
   preserves totients, squarefreeness, and divisibility into an original
   input, and loses at most a factor of two in cardinality.
6. `exists_fixed_power_odd_fibers_without_large_input_primes` proves the same
   obstruction even for squarefree ODD inputs, with fixed exponent `δ/2`:
   ```lean
   ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ η : ℝ, 0 < η → ∀ N : ℕ,
     ∃ (n : ℕ) (R : Finset ℕ), N < n ∧ (n : ℝ)^δ < R.card ∧
       ∀ m ∈ R, Squarefree m ∧ Odd m ∧ totient m = n ∧
         ∀ p : ℕ, p.Prime → p ∣ m → (p : ℝ) < (n : ℝ)^η
   ```

**Consequence for the previous approach:** polynomial cardinality alone does
not guarantee a polynomially large input prime in an arbitrary squarefree odd
subfamily. The missing prime-size hypothesis in `PopularPrime.lean` is not a
general consequence of polynomial family size.

**Scope:** these are selected subfamilies, not necessarily the entire totient
fiber. The result does not rule out a large common COMPOSITE divisor, which
could be a product of many small primes. It also does not exclude specialized
extraction arguments using additional hypotheses. It is not a disproof of
Erdős 821. `Spec.lean` remains unchanged with its original `sorry`.

Build: `lake env lean Submission/SmoothInputFamilies.lean`.

## Fixed common-core cost (`CommonCore.lean`)

`Submission/CommonCore.lean` imports `Submission.SquarefreeInput` and
`Submission.Sieve`, compiles without warnings or errors, and has a fresh olean.
All printed axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`.

This investigates common COMPOSITE divisors in the prime-subset construction;
it does not settle the original conjecture.

### Finite combinatorics

`choose_common_core_pow_bound` proves, for `h≤k≤M`,
```text
M^h * choose(M-h,k-h) ≤ k^h * choose(M,k).
```
The proof compares descending factorials termwise and uses `Nat.choose_mul`.

For a family `R` of squarefree inputs with exactly `k` prime factors in a
finite prime pool `P`, let `M=P.card`, `h=d.primeFactors.card`. Then
`common_divisor_subfamily_pow_bound` gives
```text
M^h * #{m∈R : d|m} ≤ k^h * choose(M,k).
```
Deletion of the fixed core `d.primeFactors` supplies the injection. If the
filtered family is nonempty, `d` is automatically squarefree and its prime
support is contained in the support of each selected member.

### Weighted cost and the reduced output

`common_divisor_subfamily_rpow_bound` proves, under `k>0`, `X≥0`, `s≥0`,
`p≤X` for all `p∈P`, and `k X^s≤M`,
```text
d^s * #{m∈R : d|m} ≤ choose(M,k).
```

If `choose(M,k)≤D|R|`, then `common_divisor_relative_frequency_bound` gives
```text
d^s * #{m∈R : d|m} ≤ D|R|.
```

For `φ(d)|n`, `common_divisor_reduction_score_bound` compares the divided
family `R'={m/d : m∈R, d|m}` with its reduced output:
```text
|R'| n^s ≤ D |R| (n/φ(d))^s.
```
For positive outputs this says that the multiplicity normalized at exponent
`s` increases by at most `D`. It uses `φ(d)≤d`, the exact product identity for
`n/φ(d)`, and the fact that an image has cardinality at most its source.

`exists_fiber_with_common_divisor_score_bound` selects a largest totient fiber
from a finite input pool `A` mapping into `T`. If `A.card=choose(M,k)`, then the
selected fiber has `choose(M,k)≤T.card*R.card`, so `D=T.card` is a valid concrete
choice. All structural and mapping hypotheses are explicit.

### The dyadic dimension loss is subpower

`dyadic_output_bound_pow_le_totient_lower` proves the exact integer inequality
```text
[(t L 2^((t-4)L)+1)^(2^((t-5)L))]^r
  ≤ 2^(2^((t-4)L)-1)
```
for `t≥6`, `L≥4`, `t≤L`, and `tr+2≤L`.

The bracketed expression is the existing upper bound for the number of smooth
outputs in the pigeonhole construction. The right side is the lower bound
for any output arising from a product of `k=2^((t-4)L)` distinct primes, as
proved in `SmoothInputFamilies.lean`. Thus this part of the dimension loss
is subpower relative to the original output, for every prescribed fixed root
parameter `r` at large enough scale.

### Scope and unresolved points

These are finite bounds for the specified subset construction, not a global
upper bound on `g`. The unconditional family-existence statement with uniform common-divisor
frequency bounds was subsequently assembled in `CompositeCoreFamilies.lean`,
as recorded below.
No universal impossibility theorem for common-factor amplification is claimed.
In particular, bounds relative to the original output must not be confused
with bounds relative to a much smaller reduced output.

No exponent-improving construction, new shifted-prime lower bound, proof, or
disproof of Erdős 821 was obtained. `Spec.lean` remains unchanged with its
original `sorry`.

Build: `lake env lean Submission/CommonCore.lean`.

## Uniform composite-core counterfamilies (`CompositeCoreFamilies.lean`)

`Submission/CompositeCoreFamilies.lean` imports `Submission.CommonCore` and
`Submission.SmoothInputFamilies`, compiles without warnings or errors, and has
a fresh olean. All printed axiom lists contain only the three permitted axioms.

The finite bounds have now been assembled into unconditional constructions.

### Main squarefree result

`exists_fixed_power_fibers_with_sparse_large_common_divisors` proves:
```lean
∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ η : ℝ, 0 < η → ∀ N : ℕ,
  ∃ (n : ℕ) (R : Finset ℕ), N < n ∧ (n : ℝ)^δ < R.card ∧
    (∀ m ∈ R, Squarefree m ∧ totient m = n) ∧
    ∀ d : ℕ, (n : ℝ)^η ≤ d →
      (n : ℝ)^(δ*η/2) * ((R.filter (fun m => d ∣ m)).card : ℝ) ≤ R.card
```

Thus a common divisor at least `n^η` occurs on at most the fraction
`n^(-δη/2)` of this polynomial-size family. The bound is uniform over ALL such
divisors, not just primes. The fixed exponent is `δ=2/t` for the old sieve
parameter; it does not approach one.

### Odd version

`exists_fixed_power_odd_fibers_with_sparse_large_common_divisors` proves the
same statement with `Odd m` added to the input properties. Its fixed exponent
is half the preceding one. The conversion uses
`odd_squarefree_subfiber_with_divisor_control`, which removes a possible
factor of two, loses at most a factor of two in cardinality, and does not
increase the cardinality of any divisor-filtered subfamily. Choosing a large
enough output absorbs the constant factor of two.

### Intermediate results

- `large_squarefree_fiber_with_core_control`: choose a largest fiber in the
  finite prime-subset construction; retain the pool-to-fiber bound and apply
  the fixed-core inequality to every divisor.
- `weak_dyadic_fiber_with_core_control`: specializes to the old sieve scale.
  For each prescribed natural `r`, the dimension bound gives
  ```text
  (d^(2/t) * #{m∈R : d|m})^r ≤ n * |R|^r.
  ```
- `core_controlled_fibers_of_weak_density`: produces arbitrarily large outputs
  satisfying that bound from the explicit fixed-scale density hypothesis.
- `exists_fixed_power_core_controlled_fibers`: discharges the density
  hypothesis using the previously proved unconditional sieve.
- For the final real-exponent statement choose `r>2/(δη)`. If `d≥n^η`, then
  `d^δ≥n^(δη)` and the displayed power bound gives the claimed loss after
  cancelling positive powers and taking the `r`-th root.

### Interpretation and scope

This rules out a GENERAL inference from polynomial family cardinality to a
polynomially large common divisor retaining a subpower fraction of the family.
It applies even to squarefree odd families, where common-factor removal has
no overlap loss.

**These are selected subfamilies, not necessarily whole totient fibers.**
No claim is made that the full fiber has the same divisor-frequency bounds.
The result does not rule out specialized extraction using additional full-fiber
structure, nor amplification allowing a suitable positive-power loss. It does
not disprove the original conjecture or provide exponents approaching one.

`Spec.lean` remains unchanged with its original `sorry`. No valid final proof
or disproof has been produced.

Build: `lake env lean Submission/CompositeCoreFamilies.lean`.

## Normalized records in FULL odd squarefree fibers (`RecordFibers.lean`)

`Submission/RecordFibers.lean` imports `Submission.SmoothInputFamilies`, compiles
without warnings or errors, has a fresh olean, and its printed axiom dependencies
are only `propext`, `Classical.choice`, and `Quot.sound`.

This investigation removes the selected-subfamily limitation of the preceding
common-divisor constructions, for the FULL odd squarefree fiber.

### Definitions and positive-power input

```lean
noncomputable def gOddSquarefree (n : ℕ) : ℕ :=
  {m : ℕ | Squarefree m ∧ Odd m ∧ totient m = n}.ncard

noncomputable def oddSquarefreeFiber (n : ℕ) : Finset ℕ :=
  (finite_odd_squarefree_totient_fiber n).toFinset
```

`exists_positive_power_gOddSquarefree` supplies one fixed `δ∈(0,1)` with
infinitely many `gOddSquarefree(n)>n^δ`, using the already proved unconditional
odd-family construction. There is no circular use of Erdős 821.

### Abstract record principle

`exists_large_normalized_record` proves that if `f(n)>n^δ` infinitely often,
with `δ>0`, then for every `N` there is `n>N` with `f(n)>n^δ` AND
```text
f(j)/j^(δ/2) ≤ f(n)/n^(δ/2) for every j≤n.
```

Choose a large witness `m`, then maximize the normalized function on `[0,m]`.
Its value at `m` is greater than `m^(δ/2)` and therefore dominates every fixed
initial segment. The maximizing index `n≤m` retains the original exponent
since `m^(δ/2)n^(δ/2)≥n^δ`.

### Full-fiber common-divisor bound

`card_oddSquarefreeFiber_dvd_le` proves
```text
#{m in oddSquarefreeFiber(n) : d|m} ≤ gOddSquarefree(n/φ(d)), d>0.
```
Division is injective, and the quotient is squarefree, odd, and coprime to `d`.

At a normalized record with exponent `s`,
`normalized_record_odd_fiber_core_bound` then gives
```text
φ(d)^s * #{m in oddSquarefreeFiber(n) : d|m} ≤ gOddSquarefree(n).
```
The reduced output is positive and at most `n` whenever the selected subfamily
is nonempty, so the record inequality applies directly.

`le_totient_sq_of_squarefree_odd` proves `d≤φ(d)^2` for odd squarefree `d`, by
multiplying `p≤(p-1)^2` over its prime support. Combining these results gives:

```lean
exists_large_full_odd_fibers_with_sparse_common_divisors :
  ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ N : ℕ,
    ∃ n : ℕ, N < n ∧ (n : ℝ)^δ < (gOddSquarefree n : ℝ) ∧
      ∀ (η : ℝ) (d : ℕ), (n : ℝ)^η ≤ d →
        (n : ℝ)^(δ*η/4) *
          (((oddSquarefreeFiber n).filter (fun m => d ∣ m)).card : ℝ) ≤
            (gOddSquarefree n : ℝ)
```

The SAME record output controls all `η` and all `d`. For `η>0`, any divisor
at least `n^η` occurs on a polynomially small fraction of the full restricted
fiber. This is stronger than the earlier selected-subfamily examples.

### Equivalence with the original conjecture

The file also proves
```text
gOddSquarefree(n) ≤ gSquarefree(n) ≤ 2 gOddSquarefree(n)
```
and, using the previous squarefree-input equivalence,
```lean
erdos_821_iff_odd_squarefree_inputs :
  (∀ ε > (0 : ℝ), {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite) ↔
    ∀ ε > (0 : ℝ),
      {n : ℕ | (gOddSquarefree n : ℝ) > (n : ℝ)^(1-ε)}.Infinite
```
This is an equivalence, not a proof of either assertion.

### Scope

The result concerns the entire odd squarefree fiber, not necessarily the
entire unrestricted fiber counted by `g`. It rules out a general common-divisor
extraction with subpower loss based only on polynomial cardinality, even in
the full odd squarefree setting. It does not rule out suitable positive-power
losses, extra hypotheses, or other arithmetic constructions.

**The multiplicity exponent is still one fixed positive exponent.** Neither
the record principle nor the common-divisor bounds improve it toward one.
No new shifted-prime density theorem or settlement of Erdős 821 was obtained.
`Spec.lean` remains unchanged with its original `sorry`.

Build: `lake env lean Submission/RecordFibers.lean`.

## Continuation audit (no new theorem)

Re-examined `g_le_of_summable_smooth_shifted`, the strengthened density equivalence,
and the optimized fixed-scale lower-bound construction. No exponent-improving
implication or disproof was obtained. `Density.lean` was recompiled successfully;
its three printed axiom lists still contain only `propext`, `Classical.choice`,
and `Quot.sound`.

A DNS-independent reference-access check also failed: direct connections using
`curl --resolve` to Cloudflare DNS (1.1.1.1) and arXiv (151.101.3.42) both timed
out after eight seconds. No new reference or claimed resolution was accessed.
Do not repeat these access attempts without a reason to expect changed network
availability.

`Spec.lean` remains unchanged with the original `sorry`. There is still no valid
complete proof or disproof to submit.

## Quantitative fixed-exponent feedback audit

For the existing summability-to-upper-bound argument, write `u = 1 + η`
with `η > 0`. Its rough-term condition is

```
k * (u - s) - u < 0,
```

which, for `k >= 1`, permits `η > 0` exactly when `s > 1 - 1/k`
(the case `k = 1` requires `s > 0`). To contradict infinitely many
`g(n) > n^α`, the upper exponent must also be chosen below `α`, so the
resulting series-divergence deduction requires

```
1 - 1/k < s < α.
```

In particular, a fixed multiplicity exponent does not make this argument
available at arbitrary root parameters. The density information obtained
this way does not improve the original exponent when fed into the existing
smooth-prime counting construction, which loses a positive smoothness term.
This is a limitation of this feedback argument, not of every possible
argument for the conjecture. No new formal theorem or settlement resulted.

## LCM-pair amplification investigation (informal; no new Lean theorem)

For two inputs with totient `n`, the identity
`φ(lcm(a,b)) * φ(gcd(a,b)) = n^2` suggests grouping pairs by
`e = φ(gcd(a,b))`, a divisor of `n`. A fixed LCM has at most the square
of its divisor count many ordered input pairs. Thus, after subpower losses,
a supply of about `n^(2α-λ)` pairs with `φ(gcd(a,b)) >= n^η` would give
an output at most `n^(2-η)` with multiplicity about `n^(2α-λ)`.
The exponent would improve on `α` if `λ < αη`.

No lower bound for this many large-overlap pairs was obtained. Existing
record-fiber common-divisor results are upper-frequency bounds and cannot
be substituted for the missing lower bound. This is an uncompleted route,
not a new formal result or a settlement. `Spec.lean` is unchanged.

## Verified LCM-pair reduction (`LcmFibers.lean`)

The preceding informal LCM-pair route is now formalized. `LcmFibers.lean`
imports `Submission.Valuation`, compiles cleanly, and has a fresh olean.
`LcmCheck.lean` inspects the exact types and axioms without errors.
All five printed principal axiom lists contain only `propext`,
`Classical.choice`, and `Quot.sound`.

### Finite collision bounds

- `totient_lcm_mul_totient_gcd` proves the exact LCM/GCD identity.
- `card_pairs_with_fixed_lcm_le`: a fixed nonzero LCM `l` has at most
  `τ(l)^2` ordered input pairs.
- `card_pairs_with_fixed_gcd_totient_le`: if all inputs have totient `n`,
  the GCD totient is fixed at `e`, and all LCM divisor counts are at most
  `D`, then `P.card <= D^2 * g(n^2/e)`.
- `exists_lcm_fiber_of_pair_family`: some GCD totient `e | n` satisfies
  `P.card <= τ(n) * D^2 * g(n^2/e)`.
- `exists_small_lcm_fiber_of_pair_family`: if every GCD totient is at
  least a positive natural `Y`, there is a positive output `m <= n^2/Y`
  with the same multiplicity bound.

### Uniform subpower losses

`lcm_le_polynomial_of_equal_totient` gives `lcm(a,b) <= 576*n^4` from the
previous input bound `a,b <= 24*n^2`.

`eventually_uniform_lcm_divisor_bound` proves that for every `ε>0`,
eventually **all** `l <= 576*n^4` satisfy `τ(l) <= n^ε`. This is uniform
over the polynomial-sized range, not a pointwise asymptotic substitution.

`eventually_lcm_pair_amplification` proves, for every real `η` and `ζ>0`,
that eventually every nonempty pair family `P` satisfying

```
φ(a)=φ(b)=n,   n^η <= φ(gcd(a,b))
```

has some positive output `m` such that

```
m <= n^(2-η),   P.card <= n^ζ * g(m).
```

### Explicit conditional exponent improvement

`infinite_g_gt_of_large_overlap_pairs` assumes arbitrarily large `n` with
more than `n^ρ` such pairs. It gives infinitely many `g(m)>m^β` whenever
`β>0`, `η<2`, and `β*(2-η)<ρ`.

`improved_exponent_of_large_overlap_pairs` specializes to `ρ=2α-ℓ`:
if `α>0`, `η<2`, and `ℓ<αη`, the explicit pair-supply hypothesis yields
an exponent `β>α` with infinitely many witnesses.

**The pair-supply hypothesis has not been proved.** Diagonal pairs alone
reach only the boundary `ℓ=αη` when `η=1`; they do not satisfy the strict
improvement condition. No suitable off-diagonal lower bound has been found.
The existing common-divisor frequency upper bounds do not provide one.

This is a verified conditional mechanism, not an unconditional exponent
improvement or a settlement. `Spec.lean` remains unchanged with its original
`sorry`; there is still no complete proof or disproof to submit.

Build: `lake env lean Submission/LcmFibers.lean`.

## Smoothness-bootstrap density check (informal; no new theorem)

Investigated the transformation `r-1 = a*(p-1)`: if `p-1` is
`x^(1/k)`-smooth and `a <= x^(1/k)`, then `r-1` stays smooth to that
absolute bound while the new prime scale can be `X=x^(1+1/k)`.
This improves the smoothness ratio at the new scale, but a construction
producing only one successor per old prime has at most `x=X^(k/(k+1))`
outputs. It does not retain a counting exponent near one.

This route would need roughly `x^(1/k-o(1))` appropriately sized prime
successors per old prime on average (with overlap controlled). That is a
new quantitative progression-count input at growing moduli, not a
consequence of fixed-modulus Dirichlet infinitude. The finite smooth-divisor
and progression-count framework in `Progressions.lean` does not establish
that lower bound. No unconditional exponent improvement or settlement was
obtained; `Spec.lean` is unchanged.

## Full record-fiber pair bounds (`RecordPairs.lean`)

`RecordPairs.lean` imports `Submission.RecordFibers` and `Submission.LcmFibers`
and compiles cleanly. All printed principal axiom lists contain only
`propext`, `Classical.choice`, and `Quot.sound`.

### Generalized record principle

`exists_large_normalized_record_at` strengthens the earlier half-exponent
record lemma: if `f(n)>n^δ` infinitely often, then for **any** `s<δ` there
are arbitrarily large `n` retaining `f(n)>n^δ` and maximizing `f(j)/j^s`
over `j<=n`. The proof uses divergence of `n^(δ-s)`; it does not improve `δ`.

### Pair-count definition and finite bound

`oddLargeOverlapPairs n η` is the full set of ordered pairs of inputs in
`oddSquarefreeFiber n` satisfying `n^η <= φ(gcd(a,b))`.

`normalized_record_odd_overlap_row_bound` groups the partners of a fixed
input `a` by the divisor `gcd(a,b)` of `a`. At an `s`-normalized record,
with `s>=0`, it proves

```
n^(sη) * #{b : (a,b) is a large-overlap pair} <= τ(a) * G(n),
```

where `G=gOddSquarefree`.

`normalized_record_odd_overlap_pair_bound` sums this over the full fiber:

```
n^(sη) * |P| <= G(n) * sum_{a in the fiber} τ(a).
```

### Uniform asymptotic and unconditional families

`eventually_normalized_record_odd_overlap_bound` uses the uniform divisor
bound from `LcmFibers.lean` (odd squarefree inputs are at most `n^2`) to get

```
n^(sη) * |P| <= n^ζ * G(n)^2
```

for every `ζ>0`, eventually at all such records and simultaneously for
all real `η`.

`exists_full_odd_fibers_with_sparse_overlap_pairs` combines this with the
previous unconditional positive-power lower bound. It gives one fixed
`δ in (0,1)` such that, for every `0<=s<δ`, every `ζ>0`, and every `N`,
some `n>N` has `G(n)>n^δ` and the displayed pair bound for **all** `η`.

These are upper-frequency estimates, not a source of the missing lower
bound in the conditional LCM amplification theorem. They concern full odd
squarefree fibers, not the entire unrestricted fiber. No claim is made
that they exclude amplification at other outputs or disprove the original
conjecture. The multiplicity exponent is still fixed below one.

`Spec.lean` remains unchanged with its original `sorry`.

## Smooth normalized record outputs (`RecordOutputs.lean`)

This continuation added `RecordOutputs.lean`, importing `RecordPairs` and
`PrimeStripping`. It compiles cleanly with a fresh olean. The five principal
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
`RecordOutputsCheck.lean` audits exact types, including implicit parameters.

### Finite record bound

At an `s`-normalized record of the **unrestricted** multiplicity `g`, with
`s >= 0`, `n > 0`, and `g(n) > 0`, if a prime `q | n` has `n <= q^K`,
`K >= 1`, then

```
n^(s/K) <= (K+1) * (tau(n)+1)^(K+1).
```

Name: `normalized_record_prime_power_bound`.

The proof uses the existing prime-stripping inequality and bounds all
`g(d)` for `d | ordCompl[q](n)` by the normalized record value. The common
factor `g(n)` cancels, giving a bound independent of its size.

### Smoothness of every sufficiently large record

`eventually_normalized_record_output_smooth` proves that for every fixed
`s > 0` and `K >= 1`, all sufficiently large `s`-normalized records with
`g(n) > 0` satisfy

```
forall q in n.primeFactors, q^K < n.
```

This follows because the divisor-count RHS above is subpower. It is a
statement about all such records beyond a threshold depending on `s,K`.
It does NOT give a threshold uniform over all `K` simultaneously.

### Preservation of an attained exponent

`exists_smooth_normalized_record_of_infinite_g_gt` proves: if
`g(n)>n^delta` infinitely often and `0<s<delta`, then for every fixed `K>=1`
there are arbitrarily large `s`-normalized records that retain
`g(n)>n^delta` and satisfy the root-smoothness conclusion.

`infinite_smooth_outputs_of_infinite_g_gt` states the corresponding
infinitude of outputs. `exists_fixed_positive_power_smooth_record_outputs`
combines this with the existing unconditional positive-power theorem.

**The exponent is preserved, not increased.** These are output-smoothness
results, not the smooth-shifted-prime density needed to settle Erdős 821.
From `p-1 | n` one can infer `q^K<n` for prime factors `q` of `p-1`, but not
`q^K<p-1`: the predecessor can be much smaller than the record output.
The existing selected-family constructions already demonstrate why one
cannot simply assume an input prime has a fixed-power size relative to `n`.
No missing scale-comparison estimate or exponent improvement was proved.

`Spec.lean` remains unchanged with the original `sorry`. There is still no
complete proof or disproof to submit.

## Input-scale record audit (informal calculation; no new Lean theorem)

Examined whether the new record-output smoothness result could be upgraded
relative to the primes occurring in a fiber. For a nonempty odd squarefree
fiber at an `s`-normalized record, `0<s<1`, suppose all input primes are at
most `P`. For each prime `q | n`, every input has a prime factor `p` with
`q | p-1`, since its totient is the product of those predecessors. The
verified single-prime record frequency bound therefore gives formally the
finite covering estimate underlying the following informal calculation:

```
1 <= sum_{p <= P, p prime, q | p-1} (p-1)^(-s)
  <= q^(-s) * sum_{1 <= a <= floor(P/q)} a^(-s)
  <= P^(1-s) / ((1-s)*q).
```

Hence `q <= P^(1-s)/(1-s)`. The last partial-sum estimate is the usual
integral comparison for `0<s<1`; this calculation was not added as a Lean
theorem. It exposes the remaining fixed smoothness exponent `1-s`.
Taking `s` just below an attained multiplicity exponent only reaches the
corresponding fixed smoothness scale. No supply of arbitrarily large records
with `s` approaching one, no shifted-prime density at arbitrary root scales,
and no exponent-improving implication was obtained.

This is an audit of this particular route, not an impossibility result for
the conjecture. `Spec.lean` is still unchanged with its original `sorry`.

## Verified weighted input-scale record estimates (`RecordInputScale.lean`)

The subsequent continuation formalized the weighted covering argument and a
power-weight upper bound, rather than the earlier integral comparison.
`RecordInputScale.lean` imports `RecordFibers`, compiles cleanly, and has a
fresh olean. All five principal axiom lists contain only `propext`,
`Classical.choice`, and `Quot.sound`. `RecordInputScaleCheck.lean` audits
exact types and axioms.

- `bounded_multiples_rpow_sum`: for a finite set D of positive multiples of
  q bounded by P, with s <= u and u > 1,
  ```
  sum_{d in D} d^(-s) <= P^(u-s) * q^(-u) * C_u,
  C_u = sum_{a : Nat} a^(-u).
  ```
  Division by q is injective on D. The p-series defining C_u converges.

- `one_le_record_prime_cover_sum`: at a positive, nonempty s-normalized
  record for the FULL ODD SQUAREFREE multiplicity, if all input primes are
  at most P, then for every prime q dividing n,
  ```
  1 <= sum_{p <= P, p prime, q | p-1} (p-1)^(-s).
  ```
  Every input contains a prime whose predecessor contains q; the verified
  record-frequency bound applies to this covering.

- `normalized_record_output_prime_le_input_scale` combines the two bounds:
  ```
  q^u <= C_u * P^(u-s).
  ```

- `eventually_record_output_roots_below_input_cutoff`: if
  `K*(u-s)<u`, then for sufficiently large P, uniformly over all positive
  nonempty normalized record outputs n with input-prime cutoff P,
  every output prime q satisfies `q^K<P`.

- `exists_record_weight_margin_iff`: for real k>=1 and s<=1,
  ```
  (exists u>1, s<=u and k*(u-s)<u) <-> 1-1/k < s.
  ```
  This verifies the precise parameter threshold, not a global limitation
  theorem for other possible arguments.

CAUTION: these are records of `gOddSquarefree`, not unrestricted `g`.
The earlier `RecordOutputs` theorem concerns records of `g`; they cannot
be assumed to hold at the same record output without a separate argument.

No arithmetic density estimate or exponent-improving implication was
obtained. A fixed positive record exponent still does not reach arbitrary
root parameters. `Spec.lean` is unchanged and retains its original `sorry`;
there is no complete proof or disproof to submit.

## Reference-access proxy hypothesis checked

Checked whether earlier connection failures were caused by proxy settings.
No proxy environment variables are configured. A DNS-independent request
using `curl --noproxy '*' --resolve arxiv.org:443:151.101.3.42` also timed out
at the connection stage after five seconds. No paper, updated status, or new
arithmetic result was obtained. The additional ForMathlib number-theory
files contain no missing totient-fiber or smooth-shifted-prime theorem.
Do not repeat this access check absent a genuine environmental change.

No settlement or further exponent improvement resulted. `Spec.lean` remains
unchanged with its original `sorry`.

## Uniform upper-bound constants in `UniformRankin.lean`

New verified auxiliary file: `Submission/UniformRankin.lean` (imports
`Submission.Rankin`). Its exact types and axioms were checked in
`Submission/UniformRankinCheck.lean`; the main theorems depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Both files compile, and
`UniformRankin.olean` has been rebuilt.

- `pseries_one_add_inv_le`: for every positive integer k,
  `sum' a, a^(-(1+1/k)) <= 2*k`. This uses dyadic condensation and the
  finite geometric identity, so its bound is uniform as k grows.
- `smoothRankinConstant_one_add_inv_le`: the Rankin constant at
  `s=1-1/k`, `u=1+1/k` is at most `2*uniformRankinBase*k` for k>=2.
- `exists_uniform_quadratic_rankin_threshold`: there is one absolute
  positive integer C such that, for every k>=2 and every n,
  ```
  2^(C*k^2) <= n  ==>  g(n) <= K*n/2^k,
  K = 4*totientRatioAverageConstant + 4.
  ```
- `exists_sqrt_log_upper_bound`: there is one absolute positive integer C
  such that, for every n>=2^(4*C),
  ```
  g(n) <= K*n / 2^(Nat.sqrt (Nat.log 2 n / C)).
  ```
  This is a saving of square-root-logarithm size in the exponential, stronger
  than every fixed logarithmic saving in the earlier file.

This is NOT a disproof. A saving `exp(-c*sqrt(log n))` is still subpower:
its exponent loss divided by `log n` tends to zero. No uniform positive
fixed power saving, nor a near-linear lower bound, has been established.
`Submission/Spec.lean` remains unchanged and retains its original `sorry`.
Do not submit this auxiliary upper bound as a settlement.

## Direct-support upper bound in `SupportRankin.lean`

New verified auxiliary file: `Submission/SupportRankin.lean`, importing
`Submission.UniformRankin`. `SupportRankinCheck.lean` audits exact types with
`@` and axiom lists. Both files compile cleanly; the olean was rebuilt.
The principal results use only `propext`, `Classical.choice`, and `Quot.sound`.

- `sum_prime_inv_iterated_dyadic_le`: the sum of 1/p over primes
  p<=2^(2^J) is at most 1+8J. This follows by grouping logarithmic dyadic
  blocks and applying the existing Chebyshev-weighted prime sum.
- `sum_primeFactors_weight_le_at_iterated_scale`: for J>=1 and
  0<n<=2^(2^(2^J)), the sum over prime divisors p of n of
  p^(-(1-1/2^J)) is at most 4+16J.
- `g_le_direct_support_rankin`: in that same range,
  ```
  g(n) <= exp(exp(uniformRankinBase*(4+16J))) * n^(1-1/2^J).
  ```
- `eventually_g_le_power_on_iterated_windows`: for all sufficiently
  large J, uniformly over
  `2^(2^(2^J)) <= n <= 2^(2^(2^(J+1)))`,
  ```
  g(n) <= n^(1-1/2^(J+2)).
  ```
- `eventually_g_le_power_loglog_loss`: the windows cover every sufficiently
  large n, giving the exact bound
  ```
  g(n) <= n^(1 - 1/2^(Nat.log 2 (Nat.log 2 (Nat.log 2 n)) + 2)).
  ```
  The exponent loss is of order 1/log(log n), stronger than the earlier
  square-root-logarithm saving in the exponential.
- `tendsto_support_rankin_exponent_loss` proves that this precise loss
  tends to zero. Thus there is still no fixed positive exponent loss.

These are unconditional upper bounds, NOT a disproof of Erdős 821.
They do not supply the arbitrary-root smooth shifted-prime density needed
for the lower-bound route. `Spec.lean` is unchanged and still contains its
original `sorry`; there is no complete settlement to submit.

Lean note: in a sum whose prime finset is not already bound to a typed local,
write `((p : Nat) : Real)` to prevent elaboration as a sum over a mapped
real-valued finset. This affected the initial reciprocal-prime-sum statement
and has been fixed and audited in the final auxiliary file.

## Optimized direct-support bound (`OptimizedSupport.lean`)

The completed auxiliary file imports `SupportRankin`. It compiles cleanly,
its olean has been rebuilt, and `OptimizedSupportCheck.lean` checks exact
principal types and axioms. All principal axiom lists contain only
`propext`, `Classical.choice`, and `Quot.sound`.

- `sum_primeFactors_weight_le_flexible_scale`: uniformly for 0<=e<1 and
  0<n<=2^(2^(2^J)), the sum of p^(-(1-e)) over prime divisors of n is at
  most 2^((2^J)*e)*(2+8J).
- `g_le_flexible_support_rankin`: for 0<=e<=1/2 in this range,
  g(n)<=exp(exp(uniformRankinBase*2^((2^J)*e)*(2+8J)))*n^(1-e).
- `eventually_exp_weighted_geometric_budget` absorbs the prefactor after
  choosing e proportional to (J+1)/2^(J+1).
- `eventually_g_le_optimized_power_on_windows`: for all sufficiently large
  J, uniformly over 2^(2^(2^J))<=n<=2^(2^(2^(J+1))),
  g(n)<=n^(1-(J+1)/2^(J+4)).
- `eventually_g_le_optimized_power_loglog_loss`: covers all sufficiently
  large n by these windows, with J=Nat.log 2 (Nat.log 2 (Nat.log 2 n)).
- `tendsto_optimized_support_rankin_exponent_loss`: the precise loss
  (J+1)/2^(J+4), with this J(n), tends to zero.

The loss is of order log(log(log n))/log(log n). This improves the earlier
upper bounds but remains a vanishing exponent loss, NOT a disproof.
No unconditional lower bound approaching exponent one has been obtained.
`Spec.lean` is unchanged and retains the original `sorry`.

The sparse-scale Dirichlet route was reconsidered after this audit. Allowing
arbitrarily sparse scales does not by itself supply an upper bound on the
prime factors of (p-1)/d for primes p=1 mod d with smooth d. No new uniform
cofactor estimate was found. This observation is not a theorem excluding
other approaches, and it does not resolve the conjecture.

## Reciprocal divergence at one weak smoothness scale (`ReciprocalDensity.lean`)

This new auxiliary file imports `LowerExponent`. It compiles cleanly and its
olean has been rebuilt. `ReciprocalDensityCheck.lean` checks exact types and
axiom dependencies. All seven principal results use only the permitted
`propext`, `Classical.choice`, and `Quot.sound`.

- `summable_dyadic_count_of_summable_reciprocal`: for a positive-integer set
  S, summability of its reciprocal indicator implies summability of
  `#{n in S : n<=2^k}/2^k`. The proof uses a nonnegative double sum and the
  geometric tail starting at `Nat.clog 2 n`.
- `not_summable_reciprocal_of_eventual_dyadic_count`: a lower count
  `2^(tL)<=C*L*#{n in S : n<=2^(tL)}` for every sufficiently large L,
  with t>0, forces reciprocal divergence. This is a uniform count, not
  merely an arbitrarily-large-scale count.
- `rationalSmoothShiftedPrimes a b` is
  `{p | p.Prime and forall q in (p-1).primeFactors, q^a<=(p-1)^b}`.
- `relative_smooth_prime_count_of_sieve`: after discarding p<=2^((t-1)L),
  the existing full-count sieve supplies
  `2^(tL)<=4*t*L*#(rationalSmoothShiftedPrimes (t-1) (t-5) up to 2^(tL))`.
  This converts absolute smoothness at the cutoff into relative smoothness
  at each remaining prime.
- `exists_fixed_smooth_reciprocal_divergence`: there are a,b with 0<b<a
  for which the reciprocal sum over `rationalSmoothShiftedPrimes a b`
  diverges. The witnesses are a=t-1, b=t-5 for one fixed large sieve t.
- `predecessor_mem_smooth_of_rational`: if b>0 and k*b<=a, membership in
  this rational-scale set implies p-1 belongs to `smoothShiftedPredecessors k`.
- `summable_rational_reciprocal_of_summable_predecessors`: summability of
  the predecessor series at any s<=1 implies reciprocal summability in
  any rational-scale set satisfying k*b<=a.
- `erdos_821_of_arbitrarily_smooth_reciprocal_divergence`: the conjecture
  follows if for EVERY k>=1 there are a,b with b>0 and k*b<=a and divergent
  reciprocal sum in that rational-scale set.

The last hypothesis is NOT established. The unconditional result provides
only one fixed ratio b/a<1, close to one; it does not provide ratios tending
to zero. Retaining reciprocal mass does not itself give an iteration that
improves the relative smoothness exponent. No exponent-improving step or
settlement was found. This is a stronger use of the already verified sieve
count, not a new prime-distribution estimate.

`Submission/Spec.lean` is unchanged and still contains the original `sorry`.
Do not submit these auxiliary results as a proof or disproof of Erdős 821.

## Pointwise prime-chain iteration fails (`PrimeChainAudit.lean`)

The new file imports `ReciprocalDensity`, compiles cleanly, and has a fresh
olean. `PrimeChainAuditCheck.lean` checks its types and permitted axiom list.
It proves an exact finite counterexample to this proposed implication:

```
p in rationalSmoothShiftedPrimes a b,
every q | p-1 prime in rationalSmoothShiftedPrimes a b
  ==> p in rationalSmoothShiftedPrimes (a*a) (b*b).
```

Take a=4, b=3, p=11. The predecessor 10 has prime factors 2 and 5;
5^4<=10^3, and 5's predecessor 4 satisfies 2^4<=4^3. The predecessor
of 2 is 1, so its condition is vacuous. Nevertheless 5^16>10^9.
`rational_smoothness_not_transitive` formally negates the universal
implication, not the original conjecture.

Factoring q-1 at a deeper level does not replace the prime factor q in
the original predecessor p-1. Thus a pointwise depth iteration cannot
simply multiply smoothness exponents. This does not rule out a different
aggregate argument or a construction of new primes. No such argument
with the needed prime counts and cofactor control was obtained.

This is NOT a disproof of Erdős 821. `Submission/Spec.lean` remains
unchanged with its original `sorry`; no valid complete submission exists.

## Additive large sieve (`AdditiveLargeSieve.lean`)

New analytic development, importing only `FormalConjecturesUtil`. It
compiles cleanly, has a rebuilt olean, and is audited in
`AdditiveLargeSieveCheck.lean`. All principal results depend only on
`propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`s in
this auxiliary file.

The namespace is `Erdos821.AnalyticSieve`. Definitions:

```
wave n x = exp(n * (2*pi*I) * x),  n : Int, x : Real;
trigSum A a x = sum_{n in A} a(n) * wave n x.
```

- `point_sampling_bound`: for continuous f,f' with derivative f',
  `delta*f(a) <= integral_[a,a+delta] f
      + delta*integral_[a,a+delta] |f'|`, for delta>=0.
- `sum_interval_integrals_le`: a finite sum over disjoint sampling
  intervals is bounded by the integral over their enclosing interval,
  for a continuous nonnegative integrand.
- `finite_sampling_bound`: sums the pointwise estimate at separated
  sample points.
- `integral_trigSum_norm_sq`: the exact energy identity on [0,2],
  `integral |S(x)|^2 = 2*sum |a(n)|^2`.
- `integral_trigSum_deriv_norm_sq_le`: if |n|<=N on A, the derivative
  energy is at most `(2*pi*N)^2 * 2*sum |a(n)|^2`.
- `additive_large_sieve`: for any finite delta-separated family of
  sample points x_i in [0,1], with 0<delta<=1 and |n|<=N on A,
  ```
  sum_i |S(x_i)|^2 <= (2/delta + 4*(2*pi*N+1))*sum_n |a(n)|^2.
  ```
  The proof uses disjoint forward intervals in [0,2], the energy
  identity, and a scaled quadratic bound on the derivative of |S|^2.
- `rational_separation`: distinct reduced rationals with denominators
  at most Q have real distance at least 1/Q^2.
- `rational_large_sieve`: for a finite set of rationals r in [0,1]
  with denominator <=Q, Q>0,
  ```
  sum_r |S(r)|^2 <= (2*Q^2 + 4*(2*pi*N+1))*sum_n |a(n)|^2.
  ```

This is a standard, non-sharp analytic large-sieve estimate. It does not
establish prime-count lower bounds, Bombieri--Vinogradov, or the arbitrary
smoothness scales needed for Erdős 821. No new lower multiplicity exponent
has yet been deduced from it. `Submission/Spec.lean` remains unchanged with
its original `sorry`, and no complete proof or disproof is available.

Possible next analytic step: pass to primitive Dirichlet characters using
Gauss sums and orthogonality. Mathlib has
`DirichletCharacter.gaussSum_mulShift_of_isPrimitive` in
`NumberTheory/DirichletCharacter/GaussSum.lean`; the multiplicative large
sieve and its application to prime distributions have NOT been proved.
Do not confuse this next-step plan with an established arithmetic input.

## Multiplicative large sieve (`MultiplicativeLargeSieve.lean`)

The new file imports `AdditiveLargeSieve`. It compiles cleanly and has a
rebuilt olean. `MultiplicativeLargeSieveCheck.lean` checks exact principal
types and axioms, all limited to `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry` occurs in this auxiliary file.

All names are in `Erdos821.AnalyticSieve`.

- `conductor_inv_eq` and `primitive_inv`: inversion preserves conductor
  and primitivity. This follows from the definition of factoring through
  a modulus and the change-level homomorphism.
- `primitive_gaussSum_norm_sq`: for every primitive character modulo
  positive q, including q=1, `norm(gaussSum chi stdAddChar)^2=q`.
  The proof uses discrete Fourier inversion at -1 and conjugation,
  not a finite-field-only Gauss-sum theorem.
- `unit_character_parseval`: exact character orthogonality on the unit
  group gives
  `sum_chi |sum_u b(u)*chi(u)|^2 = phi(q)*sum_u |b(u)|^2`.
- `primitive_characterSum_gauss` and `primitive_characterSum_norm_sq`
  express primitive character sums as additive sums at reduced fractions.
- `primitive_characterSum_family_bound`: at one positive modulus q, for
  any finite family C of primitive characters,
  ```
  (q/phi(q))*sum_{chi in C}|sum_{n in A} a(n)*chi(n)|^2
    <= sum_{u in (ZMod q)^units}|S(val(u)/q)|^2.
  ```
- `ReducedResidue` is the sigma type of a positive modulus q and a unit
  modulo q; `reducedFraction` sends it to the rational val(u)/q.
  Its numerator and denominator are proved exact, and the map is injective.
- `reducedResidue_additive_bound` applies the rational additive large sieve
  to these distinct fractions.
- `multiplicative_large_sieve`: for a finite family M of positive moduli
  bounded by Q and any primitive-character families C(q),
  ```
  sum_{q in M} (q/phi(q))*sum_{chi in C(q)}|sum_{n in A} a(n)*chi(n)|^2
    <= (2*Q^2 + 4*(2*pi*N+1))*sum_{n in A}|a(n)|^2,
  ```
  where |n|<=N on A and N>=0.
- `weighted_sum_mul_sq_le` is the finite weighted Cauchy--Schwarz bound.
- `bilinear_characterSum_large_sieve` applies it to two coefficient
  ranges A,B. The square of the weighted sum of products of character-sum
  norms is at most
  `K(Q,X)*K(Q,Y)*sum_A|a|^2*sum_B|b|^2`, where
  `K(Q,T)=2*Q^2+4*(2*pi*T+1)`.
- `characterSum_mul_eq_rectangle` factors the corresponding rectangular
  bilinear character sum. There is NO hyperbolic cutoff m*n<=X in this
  result; that requires another argument.

These are analytic upper bounds, not a new smooth-shifted-prime lower bound.
Neither Bombieri--Vinogradov nor a prime distribution theorem at arbitrary
smoothness scales has been established. No stronger unconditional
multiplicity exponent has yet been extracted from this analytic development.
`Submission/Spec.lean` is unchanged with its original `sorry`; the original
conjecture remains unproved and undisproved.

Possible next steps: Pólya--Vinogradov for primitive characters (using the
Gauss identity and geometric sums), a cutoff/maximal bilinear version, and
an exact Vaughan identity. Further prime-distribution analysis is still
required; these plans are not established hypotheses for a final proof.

## Pólya–Vinogradov (`PolyaVinogradov.lean`)

This file imports `MultiplicativeLargeSieve`. It compiles cleanly, has a
rebuilt olean, and is audited in `PolyaVinogradovCheck.lean`. Every audited
result depends only on the permitted axioms. There are no sorries.
All names are in `Erdos821.AnalyticSieve`.

- `norm_wave`, `wave_nat_eq_pow`, `norm_wave_one_sub_one` establish the
  elementary wave identities used in geometric sums.
- `norm_geometric_mul_le`: a unit-norm complex geometric sum times
  `norm(z-1)` is at most 2.
- `norm_intervalWaveSum_rational_le`: for `0<a<q`, every integer shift M
  and natural length L satisfy
  ```
  |sum_{n<L} wave(M+n,a/q)| <= q/2 * (1/a + 1/(q-a)).
  ```
  This uses `Real.mul_le_sin` on either side of the midpoint.
- `reciprocal_reflect_sum` and `reciprocal_pair_sum` sum these reciprocals.
- `intervalCharacterSum chi M L` is `sum_{n<L} chi(M+n)`.
- `primitive_intervalCharacterSum_gauss` is the shifted interval Gauss
  identity, proved directly from the primitive character Fourier formula.
- `primitive_gaussSum_norm`: the Gauss norm is `sqrt(q)`.
- `polya_vinogradov_harmonic`: for primitive chi modulo `q>=2`,
  ```
  |intervalCharacterSum chi M L| <= sqrt(q)*harmonic(q-1).
  ```
- `polya_vinogradov`: the right side is at most `sqrt(q)*(1+log q)`.
  This is uniform in M and L. Modulus one is explicitly excluded.

## Fourier completion (`FourierCutoff.lean`)

Imports `PolyaVinogradov`, compiles cleanly, built and audited in
`FourierCutoffCheck.lean`. No sorries or unpermitted axioms.

- `weighted_norm_linear_combination_le` is a weighted finite triangle
  inequality for a fixed family of coefficients.
- `normalizedFourier H r = W^(-1)*ZMod.dft H r` for positive W.
- `normalizedFourier_inversion` is exact finite Fourier inversion.
- `intervalIndicator T x` is 1 if `x.val<T`, and 0 otherwise.
- `dft_intervalIndicator` identifies its DFT with an incomplete wave sum.
- `intervalIndicator_fourier_l1`: for `W>=2`, `T<=W`,
  ```
  sum_r |normalizedFourier(intervalIndicator T,r)| <= 2+log W.
  ```
- `fourierTwist r alpha a n = a(n)*stdAddChar(r*alpha(n))`.
  Its coefficient norms equal the original coefficient norms.
- `bilinear_fourier_completion` expresses the bilinear sum with a factor
  `H(alpha(m)+beta(n))` as a sum of twisted rectangular character products.
- `bilinear_fourier_large_sieve` bounds the weighted character family sum
  of this cutoff expression by
  ```
  FourierL1(H) * sqrt(K(Q,X)*K(Q,Y)*EA*EB),
  K(Q,Z)=2Q^2+4*(2*pi*Z+1), EA=sum_A |a|^2, EB=sum_B |b|^2.
  ```
- `bilinear_interval_cutoff_large_sieve` uses `2+log W` for an interval H.

## Hyperbolic cutoff (`HyperbolicLargeSieve.lean`)

Imports `FourierCutoff`, compiles cleanly, built and audited in
`HyperbolicLargeSieveCheck.lean`. No sorries or unpermitted axioms.

The encoding is exact, not an asymptotic replacement of an indicator:
```
logCode N n = ceil(4*(N+1)*log n),       n : Z
logCutoff N R = floor(4*(N+1)*log(R+1)), N R : Nat
hyperbolicModulus N = 16*(N+1)^2.
```
- `scaled_log_gap` and its uniform version separate the integer product
  ranges `m*n<=R` and `m*n>=R+1` by more than the rounding error.
- `logCode_condition`: for positive integers m,n and `R<=N`,
  ```
  logCode N m + logCode N n < logCutoff N R iff m*n<=R.
  ```
  The endpoint R=0 is included.
- `logCode_add_lt_modulus`: for positive m,n bounded by N, there is no
  wraparound in the auxiliary cyclic group.
- `logResidue_condition` is the exact same condition after reduction.
- `logCutoff_le_modulus` verifies the interval length hypothesis.
- `log_hyperbolicModulus_le`: `log W<=4+2*log(N+1)`.
- `hyperbolic_bilinear_large_sieve`: for A,B finite sets of positive
  integers bounded by N, `R<=N`, and the same primitive-character family
  hypotheses as the multiplicative sieve,
  ```
  sum_{q in M} (q/phi(q)) sum_{chi in C(q)}
    |sum_{m in A,n in B,m*n<=R} a(m)b(n)chi(m*n)|
  <= (6+2*log(N+1)) * sqrt(K(Q,X)*K(Q,Y)*EA*EB).
  ```
  Here `abs(m)<=X` on A, `abs(n)<=Y` on B, X,Y>=0.

## Adaptive / maximal cutoff (`MaximalLargeSieve.lean`)

Imports `HyperbolicLargeSieve`, compiles cleanly, built and audited in
`MaximalLargeSieveCheck.lean`. No sorries or unpermitted axioms.

- `fourierEnvelope` is 1 at zero and
  `(1/2)*(1/a+1/(W-a))` at a nonzero natural residue representative a.
- `norm_interval_fourier_le_envelope`: the normalized Fourier coefficient
  of ANY interval of length T<=W is bounded by the envelope at `-r`.
- `sum_fourierEnvelope = 1+harmonic(W-1)`.
- `weighted_norm_variable_combination_le` permits the expansion
  coefficients to vary with the outer family index, with a fixed envelope.
- `adaptive_interval_cutoff_large_sieve`: every primitive character may
  choose its own interval length T(q,chi)<=W; the same `2+log W` loss holds.
- `adaptive_hyperbolic_large_sieve`: every primitive character may choose
  its own cutoff R(q,chi)<=N; the same `6+2*log(N+1)` loss holds.
  Thus the cutoff is not required to be shared across the characters.
  This is the usual maximal-strength form, stated via arbitrary choices
  of cutoffs rather than `Finset.sup` notation.

## Vaughan's identity (`VaughanIdentity.lean`)

Imports only `FormalConjecturesUtil`, compiles cleanly, built and audited
in `VaughanIdentityCheck.lean`. No sorries or unpermitted axioms.

- `shortPart f U` is f supported at n<=U; `longPart f U` at U<n.
- `vaughan_algebra` is the general commutative-ring algebra identity.
- `vaughan_identity` is an exact identity of REAL arithmetic functions,
  where multiplication is Dirichlet convolution:
  ```
  Lambda = Lambda_short(U) + mu_short(V)*log
    - mu_short(V)*zeta*Lambda_short(U)
    + mu_long(V)*zeta*Lambda_long(U).
  ```
- `vaughanTypeI U V = mu_short(V)*Lambda_short(U)`.
  It vanishes for n>U*V and its absolute value is at most log n.
- `vaughanTypeII V = mu_long(V)*zeta`.
  It vanishes for n<=V and its absolute value is at most card(n.divisors).
- `vaughan_identity_typeI_typeII` regroups the middle product to use these
  two coefficients.

### Remaining analytic and original-conjecture gaps

The old TODO for Pólya–Vinogradov, a cutoff/maximal bilinear estimate, and
an exact Vaughan identity has now been completed. Further work could:
1. Relate finite twisted sums of Dirichlet convolutions to the hyperbolic
   rectangular sums in `adaptive_hyperbolic_large_sieve`.
2. Add weighted partial summation for logarithmic Type I terms, using PV.
3. Prove an average second-moment bound for the Type II coefficient
   (a divisor-square moment bound suffices), and perform dyadic Type II
   decomposition with explicit parameter ranges.
4. Obtain a large-conductor von Mangoldt mean-value estimate.

These are plans, not established theorems. NO Bombieri--Vinogradov,
Siegel--Walfisz, or new prime-distribution lower bound has been proved.
Even ordinary Bombieri--Vinogradov alone would not establish the full
arbitrary-smoothness shifted-prime criterion from `Density.lean`.

The central unconditional gap is unchanged: one needs full subcritical
counting/series density of primes p for which ALL factors q of p-1 satisfy
`q^k<=p-1`, for EVERY fixed k. Only one weak fixed smoothness scale is
currently established. No improved unconditional multiplicity exponent
has yet been extracted from the new analytic upper bounds.

`Submission/Spec.lean` is unchanged and still contains its original sorry.
The original conjecture remains unproved and undisproved. None of these
auxiliary results is being submitted as a settlement.

## Finite convolution bridge (`FiniteConvolution.lean`)

Imports `VaughanIdentity`, compiles cleanly, has a rebuilt olean, and is
audited in `FiniteConvolutionCheck.lean`. All audited results use only the
permitted axioms, and there are no sorries. All names below remain in
`Erdos821.AnalyticSieve`.

- `sum_divisorsAntidiagonal_Icc`: for any additive-commutative-monoid-valued
  function F and R<=N,
  ```
  sum_{k=1..R} sum_{d in divisorsAntidiagonal(k)} F(d)
    = sum_{m=1..N,n=1..N,m*n<=R} F(m,n).
  ```
  Proved by a finite sigma-set bijection, including all zero endpoints.
- `sum_convolution_weighted` permits an arbitrary weight w(m*n).
- `sum_convolution_Icc`: for arithmetic functions over any semiring,
  ```
  sum_{k<=N} (f*g)(k) = sum_{m<=N} f(m)*sum_{n<=N/m} g(n).
  ```
  This helper lives here, not in `DivisorMoments`.
- `twistedArithmeticSum chi f N = sum_{n=1..N} (f(n):C)*chi(n)`.
- `characterTwist` bundles the twist as a complex arithmetic function;
  `characterTwist_mul` shows it preserves Dirichlet convolution.
- `twistedArithmeticSum_convolution` gives a hyperbolic rectangle.
- `twistedArithmeticSum_convolution_quotient` gives the quotient-sum form.
- `twisted_vaughan_identity` is the exact finite twisted Vaughan identity.

## Divisor moments (`DivisorMoments.lean`)

Imports `FiniteConvolution`, compiles cleanly, built and audited in
`DivisorMomentsCheck.lean`. No sorries or unpermitted axioms.

- `harmonic_real_nonneg`, `harmonic_real_mono`.
- `multiplicative_le_of_prime_powers`: comparison of nonnegative real
  multiplicative arithmetic functions reduces to prime powers.
- `sigma_zero_sq_le_convolution`: tau(n)^2 <= (tau*tau)(n).
  On p^k every term (j+1)*(k-j+1) is at least k+1; comparison then extends
  through prime factorization. No unproved divisor-moment assertion is used.
- `divisor_card_sq_le_zeta_four`: tau(n)^2 <= (zeta^4)(n).
- `sum_zeta_pow_le_harmonic`: for every k,N,
  ```
  sum_{n=1..N} (zeta^(k+1))(n) <= N*H_N^k.
  ```
  Induction uses the quotient convolution formula, cast(N/m)<=N/m, and
  harmonic monotonicity.
- `sum_divisor_card_sq_le` and `sum_divisor_card_sq_le_log`:
  ```
  sum_{n<=N} tau(n)^2 <= N*H_N^3 <= N*(1+log N)^3.
  ```
- `sum_vaughanTypeII_sq_le` supplies that same energy bound for beta_V.

## Type I estimates (`TypeIEstimates.lean`)

Imports `PolyaVinogradov` and `FiniteConvolution`, compiles cleanly, built
and audited in `TypeIEstimatesCheck.lean`. No sorries or unpermitted axioms.

- `norm_monotone_weighted_sum_le`: bounded prefix sums by B and monotone
  nonnegative real weights f give norm(sum f(i)*g(i)) <= 2*B*f(N-1).
  This is proved with finite summation by parts and telescoping.
- `sum_Icc_one_eq_sum_range` handles positive-index sums.
- `log_nat_mono` includes m=0 using Mathlib's log(0)=0 convention.
- `norm_twisted_convolution_le`: if f is supported at n<=D, |f(n)|<=C on
  n<=N, and all partial twisted g-sums through N have norm <=B, then
  ```
  |S_chi(f*g,N)| <= D*C*B.
  ```
- For primitive chi modulo q>=2, let Bq=sqrt(q)*(1+log q):
  - `norm_twisted_zeta_le_pv`: |S_chi(zeta,N)|<=Bq.
  - `norm_twisted_log_le_pv`: |S_chi(log,N)|<=2*Bq*log N.
  - `norm_vaughan_mu_log_le`: |S_chi(mu_short(V)*log,N)|<=2*V*Bq*log N.
  - `norm_vaughan_typeI_le`: |S_chi(alpha_UV*zeta,N)|<=U*V*Bq*log N.
- The principal modulus-one character is excluded from these PV corollaries.

## Type II block bounds (`TypeIIBounds.lean`)

Imports `MaximalLargeSieve`, `TypeIEstimates`, and `DivisorMoments`.
Compiles cleanly, built and audited in `TypeIIBoundsCheck.lean`.
No sorries or unpermitted axioms.

- `adaptive_hyperbolic_large_sieve_nat`: the earlier integer-index bound
  is transferred to finite natural index sets using the embedding N -> Z.
- `sum_longPart_vonMangoldt_sq_le`:
  sum_{n<=Y} Lambda_long(U,n)^2 <= Y*(log Y)^2.
- `sum_subset_typeII_energy_le` and `sum_subset_vonMangoldt_energy_le`
  apply the two energy estimates to arbitrary subsets of positive intervals.
- `vaughan_typeII_block_bound`: for A subset [1,X], B subset [1,Y], also
  bounded by N, and any independent R(q,chi)<=N, the weighted primitive
  character mean of the corresponding Type II block is at most
  ```
  (6+2*log(N+1)) * sqrt(K(Q,X)*K(Q,Y)
      * X*(1+log X)^3 * Y*(log Y)^2),
  K(Q,Z)=2Q^2+4*(2*pi*Z+1).
  ```

## Dyadic Type II assembly (`DyadicTypeII.lean`)

Imports `TypeIIBounds`, compiles cleanly, built and audited in
`DyadicTypeIICheck.lean`. No sorries or unpermitted axioms.

Definitions:
```
typeIILeftBlock N V j = {m in [1,N] | V<m and log_2(m-1)=j}
typeIIRightBlock N U j = [U+1, N/2^j]
typeIILevels N U V = {j<log_2(N)+1 | V<2^(j+1) and (U+1)*2^j<=N}.
```
For V>=1, every left-block index satisfies 2^j<m<=2^(j+1).

- `twisted_typeII_dyadic`: an EXACT decomposition of the Type II convolution
  sum into these blocks and active levels. Entries outside the left support,
  right support, hyperbola, and active levels are all separately proved zero.
- `typeIIBlockMajorant Q X Y` is the square-root expression in the preceding
  section, without the common factor 6+2*log(N+1).
- `weighted_norm_sum_le_sum`: the weighted finite triangle inequality.
- `vaughan_typeII_dyadic_bound`: the character-dependent endpoint Type II
  mean is bounded by
  ```
  (6+2*log(N+1)) * sum_{j in typeIILevels N U V}
    typeIIBlockMajorant Q (2^(j+1)) (N/2^j).
  ```
  Both U and V survive in the active-scale restriction.

## Primitive von Mangoldt mean (`VaughanMean.lean`)

Imports `DyadicTypeII`, compiles cleanly, built and audited in
`VaughanMeanCheck.lean`. No sorries or unpermitted axioms.

- `character_family_mass_le`: for distinct positive moduli q<=Q and ANY
  character families C(q),
  ```
  sum_q (q/phi(q))*card(C(q)) <= Q^2.
  ```
- `norm_twisted_short_vonMangoldt_le`: the short Lambda term is <=U*log U.
- `pvMajorant Q = sqrt(Q)*(1+log Q)`, nonnegative and monotone.
- `vaughanShortMajorant U V N Q` is
  ```
  U*log U + (U*V+2*V)*pvMajorant(Q)*log N.
  ```
- `primitive_vonMangoldt_mean_bound`: for moduli 2<=q<=Q, primitive character
  families C(q), V>=1, and separate R(q,chi)<=N,
  ```
  sum_q (q/phi(q))*sum_chi |sum_{n<=R(q,chi)} Lambda(n)*chi(n)|
   <= Q^2*vaughanShortMajorant U V N Q
      +(6+2*log(N+1))*sum_{j in typeIILevels N U V}
        typeIIBlockMajorant Q (2^(j+1)) (N/2^j).
  ```
  This is a proved mean estimate, not merely an identity or a conditional plan.
  It does NOT assert a lower bound for primes in progressions.

## Balanced mean (`BalancedVaughanMean.lean`)

Imports `VaughanMean`, compiles cleanly, built and audited in
`BalancedVaughanMeanCheck.lean`. No sorries or unpermitted axioms.

- `large_sieve_kernel_le`: if X<=Q^2 and Q>0, K(Q,X)<=64Q^2.
- `typeIIBlockMajorant_balanced_le`: if X,Y<=Q^2, XY<=T^2, T>=0,
  1<=H, 1+log X<=H and log Y<=H, then the block majorant is <=64Q^2*T*H^3.
- `dyadic_majorant_balanced_le` evaluates the dyadic sum whenever
  ```
  V>=1, Q>0, 2N<=(U+1)Q^2, and 2N<=VQ^2.
  ```
  For each active level these conditions imply both side lengths <=Q^2.
- `balancedTypeIIMajorant N Q` is
  ```
  (6+2*log(N+1)) * (Nat.log 2 N + 1)
    * (128*Q^2*sqrt(N)*(1+log(2N+1))^3).
  ```
- `primitive_vonMangoldt_balanced_mean_bound` replaces the unevaluated
  dyadic term in the preceding mean theorem by this explicit expression.

### Next arithmetic application and unchanged conjecture gap

The previously listed TODOs (finite convolution bridge, logarithmic Type I
partial summation, Type II divisor-square energy, dyadic decomposition,
primitive-character von Mangoldt mean) have now been completed.

A promising NEXT STEP, not yet proved, is to average the residue-1 von
Mangoldt progression counts over PRIME moduli near Q=N^(1/2-delta).
Nonprincipal characters at a prime modulus are primitive, so these moduli
avoid the small-conductor/Siegel--Walfisz issue. One can aim to:
1. Prove the finite character-orthogonality progression identity and bound
   its error via `primitive_vonMangoldt_balanced_mean_bound` divided by the
   lower endpoint of the modulus interval.
2. Use elementary Chebyshev lower bounds for psi(N) and for prime moduli
   in [Q/c,Q], with fixed sufficiently large c. No PNT is needed for this
   particular fixed-exponent application.
3. Bound the principal-character omission of multiples of q crudely by
   (N/q)*log N. After division by phi(q) and summation it is negligible.
4. Choose U=V=N^(1/16), with Q sufficiently close below sqrt(N). In the
   balanced regime, the mean divided by Q is bounded by
   Q*ShortMajorant + O(Q*sqrt(N)*polylog N), which has a power saving
   over N for fixed delta>0. An integer-power parameterization is
   N=2^(64s), U=V=2^(4s), Q=2^(32s-L), 1<=L<=s, followed by s=rL for
   each fixed positive integer r.
5. Remove prime powers, count the prime pairs q|(p-1), and infer that
   p-1 is N^(1/2+delta)-smooth since q is near Q and (p-1)/q<=N/q.
   Restricting p to be not too small is needed to express smoothness
   relative to p rather than merely the upper endpoint N.

This route could give an unconditional multiplicity exponent approaching
1/2, improving the single weak scale already formalized. IT WOULD NOT
settle Erdős 821: the full conjecture needs exponents approaching 1,
corresponding to arbitrary smoothness scales. None of the new prime-modulus
counting or improved multiplicity claims in this paragraph is established
in Lean yet.

NO Bombieri--Vinogradov, Siegel--Walfisz, or new prime-count lower bound has
been proved. `Submission/Spec.lean` is unchanged with its original sorry.
The original conjecture remains unproved and undisproved. These supporting
mean estimates are not being submitted as a settlement.


## Prime progression estimates (`PrimeProgressions.lean`)

Imports `BalancedVaughanMean`. Theorems relate prime-modulus arithmetic
progressions to primitive character sums via exact orthogonality.

- `prime_progression_discrepancy`: the discrepancy of the residue-one Mangoldt
  sum from `mangoldtSum N / φ(q)` is bounded by the nonprincipal-character
  contribution and the omitted multiples of q.
- `prime_progression_average_error`: the sum of discrepancies over a prime-modulus
  family `D ≤ q ≤ Q` is bounded by
  ```text
  primeProgressionError U V N Q D =
    (Q² * vaughanShortMajorant U V N Q + balancedTypeIIMajorant N Q) / D
      + 2*Q*N/D² * log N.
  ```
- `prime_progression_total_lower`: subtracting that error from the summed main
  terms gives a lower bound for the total residue-one Mangoldt weight.

These use `2N ≤ (U+1)Q²`, `2N ≤ VQ²`, and positivity conditions. They are not
an assertion of distribution beyond the square-root level.

## Concrete progression scales (`ProgressionScales.lean`)

Define
```text
N_s = 2^(64s),  U_s = 2^(6s),
Q_sL = 2^(32s-2L),  D_sL = 2^(32s-3L).
```
For `1 ≤ L ≤ s`, these satisfy the balanced-mean hypotheses. The principal
explicit estimate is
```text
primeProgressionError U_s U_s N_s Q_sL D_sL
  ≤ 10^12 (s+1)^5 2^(64s-L).
```
The auxiliary `eventually_nat_poly_le_two_pow r C k` proves that
`C*(r*L+1)^k ≤ 2^L` eventually for any fixed natural parameters. Hence the
relative error decays exponentially along each fixed ray `s=rL`.

## Prime modulus supply (`PrimeModulusSupply.lean`)

`primeModuliBetween D Q` is the finite family of positive prime moduli in `[D,Q]`.
An elementary dyadic prime-count estimate gives enough moduli when
`128s ≤ 2^L`; the deliberately wide interval avoids a prime-count upper bound.
The Mangoldt main term is bounded from below without invoking PNT.

`progression_scale_weight_lower` proves, when `1 ≤ L ≤ s` and
`32768000000000000*(s+1)^7 ≤ 2^L`, that
```text
N_s/(32768*s²) ≤ sum_{D_sL ≤ q ≤ Q_sL, q prime} residueOneMangoldt q N_s.
```
The polynomial side condition holds eventually for `s=rL`, for every fixed
`r ≥ 1`.

## Counting shifted primes (`ShiftedPrimeCounting.lean`)

`shiftedWitnessPrimes M B N` is the set of primes `B < p ≤ N` having
`p ≡ 1 (mod q)` for at least one q in M. The counting proof removes prime
powers using the Chebyshev ψ−θ bound and controls overcounting using
`N < D³`: any `2 ≤ n ≤ N` has at most two distinct prime divisors of `n−1`
that are at least D.

Set `B_sL=2^(64s-L)`. Under the same side conditions as above,
`progression_scale_prime_count` proves
```text
N_s ≤ 8388608*s³ * card(shiftedWitnessPrimes M_sL B_sL N_s).
```
`shiftedWitnessPrimes_factor_bound` shows that every prime factor of p−1 is
at most `N/D` when `Q ≤ N/D`. The divisor q and the complementary factor
`(p−1)/q` are both bounded this way. In the chosen scales,
```text
N_s / D_sL = 2^(32s+3L).
```
This is the precise smoothness bottleneck: its exponent relative to N_s is
strictly greater than one half.

## Multiplicity exponents below one half (`HalfLowerExponent.lean`)

Combines `ShiftedPrimeCounting` with the earlier finite combinatorial transfer
`infinite_g_gt_of_general_dyadic_density` from `LowerExponent`.

For every fixed `r ≥ 1`, eventually in L there is a prime family P with
```text
p ≤ 2^(64rL),  p−1 is 2^((32r+4)L)-smooth,
card P ≥ 2^((64r−1)L).
```
The transfer is applied with `t=64r`, `a=64r−1`, `b=32r+4`. It yields
```lean
infinite_g_gt_half_approximant (r : ℕ) (hr : 1 ≤ r) :
  {n : ℕ | (g n : ℝ) >
    (n : ℝ) ^ ((32 * (r : ℝ) - 7) / (64 * (r : ℝ)))}.Infinite
```
Those exponents tend to 1/2 from below. Choosing r sufficiently large proves
`infinite_g_gt_rpow_of_lt_half`, with no lower-bound assumption on γ. The
proof removes n=0 before comparing real powers by monotonicity in the exponent.

**No exponent at least 1/2 is claimed. No amplification to exponents approaching
one has been established. This is verified partial progress, not a settlement.**


## A linear Mangoldt main term (`StrongMangoldt.lean`)

The previous `dyadic_mangoldt_lower` assigned all primes the weight log 2,
losing a logarithm. The new proof discards primes below sqrt(N) and assigns the
remaining primes a weight at least (log N)/2. The elementary dyadic prime-count
bound supplies enough remaining primes.

- `progression_scale_mangoldt_lower`, for `1 ≤ s`:
  ```text
  N_s / 8 ≤ mangoldtSum N_s.
  ```
- `progression_scale_weight_lower_reciprocal`, under the familiar polynomial
  side condition and `1 ≤ L ≤ s`:
  ```text
  (N_s / 16) * S_sL ≤ sum_{q in M_sL} residueOneMangoldt q N_s,
  S_sL = sum_{q in M_sL} 1/φ(q).
  ```

Retaining S_sL rather than replacing it immediately by a coarse lower bound
is essential for comparing the main term with the second-sieve rejection cost.

## Rough predecessors in progressions (`RoughProgressions.lean`)

For a prime modulus q<Y, every prime p≡1 mod q whose predecessor is not
Y-smooth has a prime factor ell≥Y distinct from q. Therefore
```text
p = q*k*ell + 1,
```
with a short cofactor k when q*Y is close to p's size. The finite cardinality
argument reduces rejection counts to the existing prime-pair Selberg sieve.

The totient ratio is submultiplicative, and q/φ(q)≤2 for prime q. Consequently,
averaging over k uses the earlier harmonic totient-ratio estimate without
losing a factor depending on q.

Principal theorem `rough_witness_prime_count_le`: for prime moduli M with
`D ≤ q ≤ Q < Y`, `N ≤ D*K*Y`, `Q*K ≤ N`, and `J>0`,
```text
card {p in shiftedWitnessPrimes M B N : p−1 not Y-smooth}
 ≤ [64*C*N*H_K/(J log 2)²] * sum_{q in M} 1/φ(q)
    + card(M)*K*[2^(64J)+2^(16J)+1],
C = Sieve.totientRatioAverageConstant.
```
This is an unconditional finite estimate, not an assumed prime-pair asymptotic.

## Second sieve at the scales (`SievedProgressionScales.lean`)

Use `K=2^(5L)`, `Y=2Q_sL`, and `4J=s`. The exact identity
```text
D_sL*K*Q_sL = N_s
```
validates the short-cofactor range. The Selberg remainder satisfies
```text
card(M_sL)*K*[2^(64J)+2^(16J)+1] ≤ 3*B_sL.
```
The main rejection contribution is at most `N_s*S_sL/64` provided
```text
201326592 * C * L ≤ s.
```
The small-prime cutoff, prime powers, and Selberg remainder together cost at
most another `N_s*S_sL/64`. Subtracting from the linear Mangoldt lower bound
leaves a positive supply of smooth predecessors.

`sievedProgressionPrimes s L` filters `shiftedWitnessPrimes` by Y-smoothness.
The unconditional finite theorem `sieved_progression_prime_count` proves
```text
N_s ≤ 262144*s² * card(sievedProgressionPrimes s L)
```
under `1≤L≤s`, `4J=s`, the displayed constant restriction, and
`32768000000000000*(s+1)^7 ≤ 2^L`.

## Above-half extraction (`AboveHalfLowerExponent.lean`)

For every fixed r≥1 with `150994944*C ≤ r`, take the scale parameters
`s=4rL` and the second parameter `3L`. Eventually in L there is a prime family P
satisfying
```text
p ≤ 2^(256rL),  p−1 is 2^((128r−5)L)-smooth,
card P ≥ 2^((256r−1)L).
```
The general combinatorial transfer then gives the exact theorem
```lean
infinite_g_gt_above_half_parameter (r : ℕ) (hr : 1 ≤ r)
    (hC : 150994944 * Sieve.totientRatioAverageConstant ≤ (r : ℝ)) :
  {n : ℕ | (g n : ℝ) >
    (n : ℝ) ^ ((128 * (r : ℝ) + 2) / (256 * (r : ℝ)))}.Infinite
```
Its exponent is `1/2 + 1/(128r)`. An Archimedean choice of r proves
`exists_multiplicity_exponent_above_half`; monotonicity of real powers after
removing n=0 gives `exists_epsilon_cutoff_below_half`.

**Critical limitation:** increasing r decreases the improvement. Neither this
parameter change nor increasing L produces exponents approaching one. The
prime-pair upper bound only permits a fixed small logarithmic interval width;
no arithmetic amplification beyond that restriction has been established.


## Removing a logarithmic modulus loss (`PrimeModulusReciprocals.lean`)

The new lower bound retains fixed positive reciprocal mass across the logarithmic
modulus interval. No prime number theorem or new assumption is used.

1. `mangoldtSum_eq_psi` identifies the natural-index sum with Chebyshev ψ.
2. `progression_scale_theta_lower`: `N_s/16 ≤ θ(N_s)` for s≥1, by subtracting
   the ψ−θ prime-power error from the linear Mangoldt lower bound.
3. `dyadicPrimeModuli j` consists of prime moduli in `(N_(j−1), N_j]`.
   Since `N_j/N_(j−1)=2^64`, the Chebyshev upper bound at the lower endpoint
   and the new lower bound at the upper endpoint give logarithmic prime weight
   at least `N_j/32` in each block.
4. `dyadic_prime_moduli_reciprocal_lower`:
   ```text
   1/(2048j) ≤ sum_{q in dyadicPrimeModuli j} 1/φ(q),  j≥1.
   ```
5. The blocks are disjoint. Summing yields
   ```text
   (B−A)/(2048B) ≤ sum_{N_A ≤ q ≤ N_B, q prime} 1/φ(q),  A<B.
   ```
6. Set `s=256rm`, `L=192m`, `A=(128r−9)m`, `B=(128r−6)m`. Then
   `D_sL=N_A`, `Q_sL=N_B`, and for r,m≥1,
   ```text
   1/(131072r) ≤ sum_{q in M_sL} 1/φ(q).
   ```
   This is `sieved_scale_moduli_reciprocal_lower`.

## Stronger exported sieve count (`SievedProgressionScales.lean` refactor)

The proof formerly used a crude reciprocal lower bound immediately. Its
stronger intermediate conclusion is now exported without that loss:

```lean
sieved_progression_prime_reciprocal_count {s L J : ℕ}
    (hL : 1 ≤ L) (hLs : L ≤ s) (hJ : 4 * J = s)
    (hsmall : 32768000000000000 * (s + 1) ^ 7 ≤ 2 ^ L)
    (hC : 201326592 * Sieve.totientRatioAverageConstant * (L : ℝ) ≤ (s : ℝ)) :
  (progressionScaleN s : ℝ) *
    (∑ q ∈ primeModuliBetween (progressionScaleD s L) (progressionScaleQ s L),
      (((q : ℕ).totient : ℝ))⁻¹) ≤
    4096 * (s : ℝ) * ((sievedProgressionPrimes s L).card : ℝ)
```

The previous `sieved_progression_prime_count` is now a short corollary with
exactly the same statement as before. The stronger theorem is audited in
`SquareRootReciprocalCheck.lean`.

## Root-2 reciprocal divergence (`SquareRootReciprocal.lean`)

For every sufficiently large fixed r, eventually in m, with
`N=2^(16384rm)`, the number of primes p≤N whose predecessors satisfy
`q²≤p−1` for every prime divisor q is at least
```text
N / (137438953472 * r² * m).
```

The proof combines the reciprocal-weighted count with the fixed positive
modulus reciprocal mass. It retains the earlier small-prime cutoff: every
surviving p satisfies `B_sL < p`, and `(2Q_sL)² ≤ B_sL`. Hence the **relative**
square-root condition holds; this is not just an absolute smoothness bound
in terms of N.

The existing theorem `not_summable_reciprocal_of_eventual_dyadic_count` then
proves divergence of the prime reciprocal series on this set. The shift from
p to d=p−1 gives nonsummability at all exponents s≤1 for
`smoothShiftedPredecessors 2`.

Additional consequences:
- `square_root_predecessor_reciprocal_divergence`.
- `square_root_predecessor_full_dyadic_density`: for every t≥2 and M, some L≥M
  has at least `2^((t−1)L)` root-2 smooth predecessors below `2^(tL)`.
- `square_root_predecessors_infinite`.

## Exact remaining gap (`HigherRootReduction.lean`)

Monotonicity of the root-smooth predecessor sets extends the root-2 series
result to k≤2. Combining with `Density.erdos_821_iff_smooth_shifted_all_exponents`
removes those root cases from the equivalent formulation. The remaining
condition is the same series divergence for **every k≥3** and every s<1.

This is a precise reduction, not a proof of its remaining side. No pointwise
prime-chain iteration, multiplicity amplification, or analytic estimate at
arbitrarily small smoothness powers has been supplied.

A renewed external-reference request failed with DNS resolution unavailable;
no new outside result or claimed settlement was accessed.


## Smooth composite modulus supply (`SmoothCompositeModuli.lean`)

`geometricBlockPrimes m` consists of primes in `(2^(64m), 2^(64(m+1))]`.
The already proved geometric Chebyshev estimate gives
```text
2^(64m) ≤ 2048*(m+1)*card(geometricBlockPrimes m).
```
`primeProductModuli r m` is the image of the r-element subsets of this prime
block under multiplication. Unique prime factorization makes this map injective.
Every resulting modulus is squarefree, has exactly r prime factors, and lies
between `2^(64rm)` and `2^(64r(m+1))`.

Define the positive natural constant
```text
primeProductMassConstant r = 2^(64r) * 4096^r * r!.
```
If `4096*r*(m+1) ≤ 2^(64m)`, then
```text
1/[primeProductMassConstant r * (m+1)^r]
  ≤ sum_{d in primeProductModuli r m} 1/φ(d).
```
The counting argument uses `n^r ≤ 2^r*r!*choose(n,r)` when `2r≤n`; it does
not lose a fixed power of the scale.

For t≥3 and m≥max(2,t−2), take r=t−2. Every modulus d in that family satisfies
```text
d is 2^(128m)-smooth,
2^(64tm) ≤ d*2^(128m),
d ≤ 2^(64(t−1)m).
```
Thus a prime p≤N with d|(p−1) automatically has a smooth predecessor. The
unconditional finite overcount bound from `Progressions.lean` applies with
r=t−2 and costs at most `(64tm)^r` per prime.

## Explicit distribution hypothesis (`GeometricDistributionCriterion.lean`)

Definitions:
```text
progressionPrimeCount d N = #{p≤N prime : d|(p−1)}

geometricProgressionError t m =
 sum_{1≤d≤2^(64(t−1)m)}
   |progressionPrimeCount d (2^(64tm)) − π(2^(64tm))/φ(d)|.

GeometricProgressionDistribution =
 ∀t≥3 ∀A∈ℕ, eventually in m,
   geometricProgressionError t m ≤ 2^(64tm)/(m+1)^A.
```

The definition introduces no axiom. No proof of this proposition is present.

The finite theorem `geometric_distribution_smooth_prime_count` keeps all side
conditions visible. If the error satisfies the displayed bound with A=t,
and the elementary polynomial and threshold conditions hold, then
```text
N ≤ geometricSmoothCountConstant t * (m+1)^(2(t−2)+1)
      * #{p≤N prime : p−1 is 2^(128m)-smooth},
N=2^(64tm),
geometricSmoothCountConstant t =
  256*t*primeProductMassConstant(t−2)*(64t)^(t−2).
```

Proof structure:
1. The total progression main term is `π(N)*sum_D 1/φ(d)`.
2. The elementary prime-count lower bound and the composite-modulus reciprocal
   bound make this at least `N/[128t*C*(m+1)^(t−1)]`.
3. For m large enough, the hypothesized error `N/(m+1)^t` is at most half
   that main term.
4. The finite overcount bound converts the retained progression count to the
   smooth shifted-prime count above.
5. Polynomial-versus-exponential comparison gives, eventually, prime families
   of cardinality at least `2^((64t−1)m)` with smoothness bound `2^(128m)`.
6. The existing combinatorial transfer gives multiplicity exponent
   `1−131/(64t)`. Letting t grow proves the full original statement **conditional
   on GeometricProgressionDistribution**.

No unconditional near-full progression-distribution estimate was obtained.
The root-2 series result and the fixed above-half multiplicity exponent remain
the strongest unconditional conclusions of this development.

### Recent Lean implementation notes

- Avoid unrestricted `simp` or `nlinarith` over contexts containing reducible
  terms such as `2^(64*(m+1))`; eager unfolding can produce millions of natural
  recursion reductions. Restrict simplification lemmas and arithmetic hypotheses.
- `Nat.primeFactors_prod` makes the subset-product map injective.
- For squarefreeness use `Finset.squarefree_prod_of_pairwise_isCoprime`, converting
  natural coprimality with `Nat.coprime_iff_isRelPrime`.
- Casts involving local definitions often need `dsimp` of those definitions
  before `exact_mod_cast`.


## One-sided finite transfer (refactor of `GeometricDistributionCriterion.lean`)

The new signed quantity is
```text
geometricSmoothModulusDeficit t m =
  π(N) * sum_{d in primeProductModuli(t−2,m)} 1/φ(d)
    − sum_{d in primeProductModuli(t−2,m)} progressionPrimeCount d N,
N=2^(64tm).
```
It may be negative. No absolute values are present.

`geometric_smooth_deficit_le_error` proves that this deficit is bounded above
by the previous all-modulus absolute discrepancy, once the elementary modulus
size conditions hold.

`geometric_signed_deficit_smooth_prime_count` gives the same finite smooth-prime
count as the previous theorem but assumes only that the signed deficit is at
most `N/(m+1)^t`. All polynomial side conditions remain explicit. The old
`geometric_distribution_smooth_prime_count` is now a short corollary, with its
statement unchanged.

## Cofinal criterion (`OneSidedDistributionCriterion.lean`)

```lean
def CofinalSmoothModulusCondition : Prop :=
  ∀ T : ℕ, ∃ t : ℕ, max 3 T ≤ t ∧ ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧
    geometricSmoothModulusDeficit t m ≤
      (2 : ℝ) ^ (64 * t * m) / ((m : ℝ) + 1) ^ t
```

This proposition is a definition, not an axiom or an established fact.

- `eventually_signed_deficit_supplies_family`: all auxiliary polynomial side
  conditions eventually hold, so at those scales a signed-deficit bound supplies
  the needed prime family.
- `smooth_prime_family_of_frequent_signed_deficit`: unbounded good scales suffice;
  eventual validity of the arithmetic deficit bound is unnecessary.
- `infinite_g_gt_of_frequent_signed_deficit`: at a fixed t, the same hypothesis
  gives multiplicity exponent `1−131/(64t)`.
- `cofinal_smooth_modulus_condition_of_geometric_distribution`: the earlier
  all-modulus distribution hypothesis implies the cofinal one-sided condition.
- `erdos_821_of_cofinal_smooth_modulus_condition`: choose a sufficiently large
  available t for each epsilon to obtain the entire original statement,
  conditional on the new proposition.

The analytic gap is now a one-sided prime-weighted average over large smooth
composite moduli. The available prime-modulus large-sieve estimates do not
establish it at cofinal near-full modulus levels. No cancellation estimate for
this signed aggregate has been proved, and no iteration from the root-2 result
to arbitrary roots has been found.

## Strict square-root reciprocal refinement (`StrictSquareRootReciprocal.lean`)

The latest record-fiber review found no new multiplicity amplification.
`RecordPairs` supplies upper overlap-frequency bounds, not the lower bound
needed by `LcmFibers`. No such missing lower bound was proved.

A new unconditional analytic refinement is complete:
`StrictSquareRootReciprocal.lean` imports `SquareRootReciprocal`, compiles
cleanly, and has a fresh olean. `StrictSquareRootReciprocalCheck.lean` verifies
its exact theorem types and all five principal axiom lists; the only axioms
are `propext`, `Classical.choice`, and `Quot.sound`.

- `sieved_prime_mem_rational_smooth`: if `Y(s,L)^a <= B(s,L)^b`, every member
  of the sieved prime family belongs to `rationalSmoothShiftedPrimes a b`.
- `strict_square_root_sieve_scale`: at `s=256*r*m`, `L=192*m`, for `r,m>=1`,
  the preceding inequality holds with `a=128*r-2` and `b=64*r-3`.
  Writing these as `a,b`, the exponent of Q is `128*b*m` and that of B is
  `(128*a+64)*m`; the required comparison reduces to `a <= 64*b*m`.
- `eventually_strict_square_root_prime_count`: for each fixed `r>=1` with
  `150994944*totientRatioAverageConstant <= r`, eventually in m,
  ```text
  2^(16384*r*m) <= 137438953472*r^2*m *
    #{p <= 2^(16384*r*m) : p in rationalSmoothShiftedPrimes(128*r-2,64*r-3)}.
  ```
- `strict_square_root_prime_reciprocal_divergence`: the reciprocal series
  over this set diverges for every such fixed r.
- `exists_strict_square_root_reciprocal_divergence`: there exist positive
  natural a,b with `2*b<a` for which the corresponding reciprocal series
  diverges.

Thus the relative smoothness exponent can be fixed strictly below one half:
```text
b/a = (64*r-3)/(128*r-2) = 1/2 - 1/(64*r-1).
```
This keeps a strict gain that the previous root-2 endpoint theorem discarded.
It is not an iteration or a new estimate at arbitrary root parameters. In
fact `a<3*b` for all `r>=1`, and increasing r reduces the smoothness gain.
The new result does not imply the root-3 or unbounded-root criterion.

**The original conjecture remains unsolved.** `Spec.lean` is unchanged and
still contains its original `sorry`. No complete proof or disproof has been
produced or submitted.

Build:
```sh
lake env lean -o .lake/build/lib/lean/Submission/StrictSquareRootReciprocal.olean Submission/StrictSquareRootReciprocal.lean
lake env lean Submission/StrictSquareRootReciprocalCheck.lean
```

## Sharp limiting multiplicity transfers (latest continuation)

Two new auxiliary files compile cleanly, with fresh oleans and axiom audits.
All eight principal axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. Neither file imports or changes `Spec.lean`.

### `RationalSmoothMultiplicity.lean`

Imports `StrictSquareRootReciprocal`.

- `rational_smooth_prime_mem_dyadic_smooth`: relative rational smoothness and
  `p < 2^(a*k*L)` give absolute `2^(b*k*L)`-smoothness of p-1.
- `rational_reciprocal_supplies_dyadic_family`: reciprocal nonsummability
  yields arbitrarily large dyadic families at the rescaled parameters
  `t=a*k`, counting exponent `t-1`, and smoothness exponent `b*k`.
- `infinite_g_gt_of_rational_smooth_reciprocal`: for `0<b<a`, reciprocal
  divergence over `rationalSmoothShiftedPrimes a b` implies
  ```text
  forall gamma < 1 - b/a, {n : g(n) > n^gamma}.Infinite.
  ```
  The finite transfer produces `1-b/a-3/(a*k)`; choosing k large enough
  absorbs the loss for any requested gamma strictly below `1-b/a`.
- `infinite_g_gt_strict_square_root_limit`: unconditionally, for every
  `r>=1` with `150994944*totientRatioAverageConstant <= r`,
  ```text
  forall gamma < 1/2 + 1/(64*r-1),
    {n : g(n) > n^gamma}.Infinite.
  ```

Audit: `RationalSmoothMultiplicityCheck.lean`.

### `PolynomialDensityTransfer.lean`

Imports `RationalSmoothMultiplicity`.

- `dyadic_family_of_eventual_polynomial_count`: suppose eventually in m
  there are prime families P with
  ```text
  p <= 2^(t*m),
  p-1 is (K*2^(b*m))-smooth,
  2^(t*m) <= C*(m+1)^d*|P|.
  ```
  At m=k*L, the polynomial loss is eventually at most `2^L`, and
  `K <= 2^L`. This supplies dyadic parameters
  `(t*k, t*k-1, b*k+1)`.
- `infinite_g_gt_of_eventual_polynomial_count`: with `b<t`, the preceding
  eventual hypothesis implies every multiplicity exponent below `1-b/t`.
  The finite rounding loss is `4/(t*k)`, removable by rescaling.
- `eventually_sieved_polynomial_count`: the already established analytic
  sieve satisfies this input with
  ```text
  t=16384*r, b=8192*r-384, K=2,
  C=137438953472*r^2, d=1,
  ```
  under the same lower bound on r. This retains the absolute smoothness
  cutoff, avoiding the extra loss in converting it to relative smoothness.
- `infinite_g_gt_sieved_limit`: consequently,
  ```text
  forall r>=1 with 150994944*totientRatioAverageConstant <= r,
  forall gamma < 1/2 + 3/(128*r),
    {n : g(n) > n^gamma}.Infinite.
  ```
  This is the strongest unconditional multiplicity exponent guarantee now
  proved in this development. It improves the earlier selected exponent
  `1/2+1/(128*r)` and the rational-transfer limit `1/2+1/(64*r-1)`.

Audit: `PolynomialDensityTransferCheck.lean`.

### Scope and remaining gap

These arguments remove polynomial and fixed dyadic losses. They do not
provide a new analytic distribution estimate, iterate the smoothness gain,
or produce exponents approaching one. The lower bound on r remains, and
increasing r makes each gain smaller. No proof that these are optimal among
all possible methods is claimed.

The full conjecture in `Spec.lean` is still unresolved. Its original `sorry`
and import are unchanged; no complete proof or disproof has been submitted.
The SHA-256 of the unchanged file is
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.

## Smooth-product modulus spacing audit (`SmoothModulusSpacing.lean`)

This continuation re-examined the unproved signed-deficit condition, rather
than refining the fixed multiplicity exponent. No new lower bound for the
signed prime-weighted aggregate was obtained.

### Analytic issues identified

`prime_progression_average_error` is a prime-modulus theorem: it uses the
fact that every nonprincipal character at a prime modulus is primitive.
It cannot simply be applied to `primeProductModuli`. A composite-modulus
application would need a conductor decomposition and imprimitive-character
error estimates. Even after such a decomposition, the present bound for
full-conductor primitive characters retains the Q-squared large-sieve term.

At fixed r, the actual product-modulus scale is
```text
2^(64*r*m) <= d <= 2^(64*r*(m+1)).
```
Thus in the cofinal criterion r=t-2 and N=2^(64*t*m), the true modulus
exponent is asymptotically `(t-2)/t`, rather than the deliberately enlarged
upper envelope `(t-1)/t`. Using the sharper envelope would still leave
`Q*sqrt(N)/N` growing as a positive power when t>4. This is a limitation of
that majorant, not a bound on the actual signed deficit.

### Verified finite and asymptotic spacing facts

New file `SmoothModulusSpacing.lean` imports `SmoothCompositeModuli`, compiles
cleanly, and has a fresh olean. `SmoothModulusSpacingCheck.lean` checks all
five principal types and axiom dependencies; the only axioms are `propext`,
`Classical.choice`, and `Quot.sound`.

- `exists_reduced_fractions_exact_gap`: for coprime d,e>1 there are integers
  `0<a<d`, `0<b<e`, with `gcd(a,d)=gcd(b,e)=1`, such that
  ```text
  abs(a/d-b/e) = 1/(d*e).
  ```
  The construction takes a multiplicative inverse of e modulo d and
  `b=(e*a)/d`, so `e*a=d*b+1`.
- `exists_coprime_prime_product_moduli`: if
  `4096*r*(m+1) <= progressionScaleN m` and r>=1, two disjoint r-element
  subsets of the prime block produce coprime d,e>1 in the product family.
- `exists_close_fractions_at_prime_product_moduli`: the resulting distinct
  reduced fractions have positive distance at most `2^(-128*r*m)`.
- `prime_product_uniform_separation_le`: every uniform separation bound for
  all reduced fractions at these moduli is at most `2^(-128*r*m)`.
- `eventually_prime_product_uniform_separation_le`: the last assertion holds
  at every sufficiently large m, for each fixed r>=1; the finite size
  condition follows from the existing polynomial-versus-exponential lemma.

These results rule out the specific shortcut of assuming better minimum
spacing solely because the modulus support consists of smooth products.
They do NOT rule out improved estimates using average spacing, cancellation,
dispersion, or other structure, and do NOT disprove Erdős 821. No optimality
claim for all large-sieve bounds is made.

The temporary `SpacingProbe.lean` was removed. `Spec.lean` remains unchanged
with its original `sorry`. There is still no complete proof or disproof to
submit, and the strongest unconditional multiplicity result remains
`Erdos821.infinite_g_gt_sieved_limit` in `PolynomialDensityTransfer.lean`.

## Intrinsic large-sieve cardinality audit (latest continuation)

Two new files extend the preceding minimum-spacing audit. Both compile
cleanly, have fresh oleans, and their principal axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. No prime-weighted cancellation
estimate or new multiplicity exponent was obtained.

### `SmoothModulusSieveMass.lean`

Imports `SmoothModulusSpacing`.

- `primeProductModuli_totient_lower`: each d in the product family satisfies
  `2^(64*r*m) <= phi(d)`, because each factor p has `p-1 >= 2^(64*m)`.
- `prime_product_totient_mass_lower`: under the existing finite supply
  condition `4096*r*(m+1) <= progressionScaleN m`,
  ```text
  2^(128*r*m) <= 4096^r*r!*(m+1)^r * sum_{d in D} phi(d),
  D=primeProductModuli(r,m).
  ```
- `reducedResidueEnergy D A a` sums squared trigonometric samples over all
  reduced residues at moduli in D.
- `uniform_reduced_residue_constant_lower`: if `0 in A` and the energy is
  at most `B*sum_A |a(n)|^2` for EVERY coefficient sequence a, then
  `sum_D phi(d) <= B`. Use the single coefficient a(0)=1.
- `prime_product_uniform_additive_constant_lower` combines these bounds.
- `eventually_prime_product_totient_mass_power_lower`: for fixed r,k>=1 and
  any natural constant C, eventually in m,
  ```text
  C*2^(64*r*(2*k-1)*m) <= (sum_{d in D} phi(d))^k.
  ```
  This is an integer-power formulation of quadratic size up to a subpower
  factor in the lower modulus scale `Q0=2^(64*r*m)`.

Audit: `SmoothModulusSieveMassCheck.lean` (five principal theorem reports).

This cardinality test is independent of minimum spacing. It blocks a fixed
power saving in a generic additive large-sieve constant just from restricting
to these smooth product moduli, even if average-spacing information is used.
It does not address coefficient-specific bounds.

### `PrimitiveProductCharacters.lean`

Imports `SmoothModulusSieveMass`.

Definitions:
```text
primitiveCharacters(d) = all characters of level d with conductor d,
imprimitiveCharacters(d) = their complement.
```

- `card_characters_factorsThrough_le`: for c|d, d!=0, at most phi(c)
  characters of level d factor through c. This is a finite image count
  using `changeLevel`, not a bound on twisted arithmetic sums.
- `imprimitiveCharacters_card_le_proper_divisor_totients`: cover all
  imprimitive characters by their proper conductors to get
  `#imprimitive(d) <= sum_{c proper divisor d} phi(c)`.
- `prime_product_prime_factor_mem`: each prime factor of a product modulus
  belongs to the original prime block.
- `prime_product_proper_divisor_totient`: for each proper divisor c of a
  product modulus d,
  `progressionScaleN m * phi(c) <= phi(d)`.
  Squarefreeness gives multiplicativity between c and d/c; a prime factor
  of d/c supplies the missing large totient factor.
- `card_divisors_squarefree`: `tau(d)=2^(#primeFactors(d))` for squarefree d.
- `prime_product_imprimitive_card_bound`:
  ```text
  2^(64*m)*#imprimitive(d) <= 2^r*phi(d).
  ```
- `prime_product_totient_le_twice_primitive_card`: when
  `2^(r+1) <= 2^(64*m)`, each d in D satisfies
  `phi(d) <= 2*#primitive(d)`.
- `eventually_prime_product_primitive_mass_power_lower`: for r,k>=1 and
  any natural C, eventually
  ```text
  C*2^(64*r*(2*k-1)*m) <= (sum_{d in D} #primitive(d))^k.
  ```
- `primitiveCharacterEnergy` is the weighted squared-character-sum energy
  with weight d/phi(d), restricted to primitive characters.
- `uniform_primitive_character_constant_lower`: if `1 in A` and a constant
  B bounds this energy for EVERY coefficient sequence on A, then
  `sum_D #primitive(d) <= B`. Use the single coefficient a(1)=1.
- `prime_product_uniform_primitive_constant_lower`: under the finite
  supply and half-primitive conditions,
  ```text
  2^(128*r*m) <= 2*4096^r*r!*(m+1)^r*B.
  ```

Audit: `PrimitiveProductCharactersCheck.lean` (eight principal reports).
The temporary `PrimitiveCountProbe.lean` was removed.

### Scope

The full-conductor characters are not sparse enough to remove the generic
quadratic large-sieve cardinality cost. These theorems concern estimates
uniform over arbitrary coefficients (with the displayed frequency-set
hypotheses). They do NOT rule out cancellation for Vaughan coefficients,
von Mangoldt sums, or the one-sided prime-weighted deficit. In particular,
they do NOT disprove the conjecture or the sufficient cofinal condition.
No signed-deficit estimate was established.

`Spec.lean` remains unchanged with its original `sorry`, and no complete
proof or disproof has been submitted. The strongest unconditional
multiplicity theorem is still `Erdos821.infinite_g_gt_sieved_limit`.

## Exact block-prime moments and constant overcount (`SmoothModulusMoments.lean`)

This continuation worked with the signed aggregate itself rather than an
operator-norm large-sieve bound. `SmoothModulusMoments.lean` imports
`GeometricDistributionCriterion`, compiles cleanly, and has a fresh olean.
`SmoothModulusMomentsCheck.lean` verifies seven principal theorem types and
axiom lists; only `propext`, `Classical.choice`, and `Quot.sound` occur.

### Exact identities

```lean
blockPrimeDivisors m n :=
  (geometricBlockPrimes m).filter (fun q => q | n)
```

- `prime_product_divisor_count_eq_choose` proves, for all natural r,m,n,
  ```text
  #{d in primeProductModuli(r,m) : d|n}
    = choose(card(blockPrimeDivisors(m,n)),r).
  ```
  This is an exact bijection between divisors and r-element subsets, not
  just the earlier upper bound by all prime factors of n.
- `prime_product_progression_sum_eq_binomial_moment` gives
  ```text
  sum_{d in primeProductModuli(r,m)} pi(N;d,1)
    = sum_{p<=N prime} choose(omega_m(p-1),r),
  omega_m(n)=card(blockPrimeDivisors(m,n)).
  ```
- `geometric_smooth_deficit_eq_binomial_moment` substitutes this equality
  into the signed deficit at r=t-2 and N=2^(64*t*m).

### Constant overcount

- `block_prime_divisor_card_lt`: if m>=1 and 0<n<2^(64*t*m), then
  `omega_m(n)<t`. All block primes exceed `2^(64*m)`, and their product
  divides n.
- `prime_product_divisor_count_le_at_scale`: at r=t-2, t>=2, the count of
  product moduli dividing n is at most `choose(t-1,t-2)=t-1`.
- `prime_product_progression_sum_le_smooth_count`: under the existing size
  conditions t>=3 and m>=max(2,t-2),
  ```text
  sum_{d in D} pi(N;d,1)
    <= (t-1) * #{p<=N prime : p-1 is 2^(128*m)-smooth}.
  ```
  A prime counted by any d in D has a sufficiently large smooth divisor;
  the remaining cofactor is small enough to ensure the displayed smoothness.

### Sharper finite transfer, still conditional

`geometric_signed_deficit_sharp_smooth_prime_count` has the same explicit
signed-deficit input and elementary side conditions as the previous finite
transfer. Its improved conclusion is
```text
N <= [256*t*primeProductMassConstant(t-2)*(t-1)] * (m+1)^(t-1)
       * #{p<=N prime : p-1 is 2^(128*m)-smooth}.
```
The power of m is now t-1, instead of 2t-3, because the overcount is constant
in m. No earlier theorem's statement was changed.

### Remaining arithmetic issue

The exact aggregate is a binomial moment of order t-2, not the first moment
counted by individual prime moduli. The existing prime-modulus estimates do
not supply its lower bound for cofinal t. Merely rewriting the aggregate or
using nonnegativity does not establish that bound. No usable lower bound
for these high moments, no signed cancellation estimate, and no new
unconditional multiplicity exponent were obtained.

This is a combinatorial improvement of the transfer, not a proof of the
signed-deficit hypothesis or a settlement of Erdős 821. `Spec.lean` remains
unchanged with its original `sorry`, and no complete proof or disproof has
been submitted.

## Composite-character reduction (`CompositeCharacterErrors.lean`)

The full file now compiles, including the previously pending second half.
`CompositeCharacterErrorsCheck.lean` checks the principal theorem types and
reports only `propext`, `Classical.choice`, and `Quot.sound` as dependencies.

Definitions in `Erdos821.AnalyticSieve`:

- `nonunitMangoldt d N`: Mangoldt mass of integers up to N not coprime to d.
- `characterLiftError d N = (Nat.log 2 N : Real) * Real.log d`.
- `primitiveConductorMangoldtMajorant d N`: sum of absolute primitive
  Mangoldt-character sums over all nontrivial conductors dividing d.
- `compositeProgressionError d N`: this primitive-conductor majorant plus
  `(d+1)*characterLiftError d N`, divided by `totient d`.

Verified results:

- `noncoprime_prime_power_dvd_log_power` and
  `nonunitMangoldt_le_liftError` bound the nonunit contribution by using
  the identity for the Mangoldt sum over divisors of `d^(Nat.log 2 N)`.
- `principal_character_nat`, `twisted_principal_mangoldt_composite`, and
  `changeLevel_apply_nat` give the exact principal and lifted character formulas.
- `norm_twisted_changeLevel_sub_le_nonunit` and
  `norm_twisted_changeLevel_le` give the explicit lift error.
- `character_eq_lift_primitive` extracts the primitive-conductor lift identity.
- `nonprincipal_conductor_mem` and
  `nonprincipal_mangoldt_sum_le_conductors` bound all nonprincipal character
  sums by the primitive-conductor majorant plus `d*characterLiftError d N`.
  This uses a finite sigma-type cover, not an unproved claim that lifts preserve
  conductor. Duplicate lifts only enlarge the upper bound.
- `composite_progression_discrepancy_all_characters` and
  `composite_progression_discrepancy` prove the finite discrepancy estimate for
  every positive modulus, not merely prime moduli.
- `composite_progression_total_lower` sums it over arbitrary finite families of
  positive moduli to obtain a main term minus an explicit remainder.

Implementation notes: rewriting the dependent sum required explicit
`rw [Finset.sum_sigma]` and explicitly instantiated `Finset.sum_attach` lemmas;
`simp only` did not perform those dependent rewrites. One norm inequality needed
`_root_.add_le_add` to avoid ambiguity with the open Nat namespace. The final
summation proof uses an explicitly typed local inequality before transitivity.
The temporary failing API probe `CompositeProgressionProbe.lean` was removed.

### Remaining gap (unchanged)

This is a finite reduction, not a new distribution estimate. In particular,
there is no proved bound of the needed strength for

    sum_{d in product moduli} (1/phi(d)) *
      sum_{c|d,c>1} sum_{primitive chi mod c} |S_chi(N)|.

Nor is there a proof of the cofinal signed-deficit condition or of the higher-root
series divergence for all k>=3. The original conjecture has not been proved or
disproved. `Submission/Spec.lean` is unchanged and retains its original `sorry`.
No completed proof has been submitted.


## Grouped conductor completion and Vaughan cutoff audit (latest continuation)

The three new files below compile, have built oleans, and have corresponding
`...Check.lean` files. Their main theorem types were checked and all printed
axiom dependencies are exactly the permitted three. No assertion of the
original conjecture or a new asymptotic prime-density bound was obtained.

### `ConductorCompletionWeights.lean`

Imports `Submission.CompositeCharacterErrors`.

Structural lemmas:

- `mem_primeProductModuli_iff`: squarefreeness, block-prime support, and support
  cardinality characterize membership in the product family.
- `primeProductModuli_mul`, `primeProductModuli_divisor`,
  `primeProductModuli_complement`, `primeProductModuli_pairwiseDisjoint`.

For D_r = primeProductModuli(r,m), define

    W_r = primeProductReciprocalMass r m = sum_{d in D_r} 1/phi(d).

`prime_product_conductor_completion_eq` proves exactly, for c in D_s and s<=r,

    sum_{d in D_r, c|d} 1/phi(d)
      = (1/phi(c)) * sum_{e in D_(r-s), gcd(c,e)=1} 1/phi(e).

`prime_product_conductor_completion_le` drops the coprimality condition to
bound the last sum by W_(r-s).

`prime_product_divisor_sum_grouped` and
`prime_product_weighted_divisor_sum_grouped` give exact finite regrouping by
the number of conductor factors. For any nonnegative F,
`prime_product_weighted_divisor_sum_le` gives

    sum_{d in D_r} [sum_{c|d,c>1} F(c)]/phi(d)
      <= sum_{s=1}^r W_(r-s) * sum_{c in D_s} F(c)/phi(c).

Applying this to the sum of absolute primitive Mangoldt-character sums gives
`prime_product_conductor_majorant_le`. Its conductor-group sum is named
`primitiveProductMangoldtMean s m N` (nonnegativity also proved).

`geometric_block_prime_count_upper`,
`primeProductReciprocalMass_le_binomial`, and
`factorial_mul_primeProductReciprocalMass_le` imply the explicit estimate

    primeProductReciprocalMass_upper:
    W_r <= [2^64/(m+1)]^r / r!, for m>=1.

This uses Chebyshev's theta upper bound and the prime-product totient lower
bound. The constant is deliberately coarse but the inverse-logarithmic
and factorial factors are retained.

### `ProductConductorMean.lean`

Imports `Submission.ConductorCompletionWeights`.

The positive-modulus family `primeProductPositiveModuli` and its exact sum
transfer bridge to the already proved PNat-indexed general Vaughan theorem.

For L_s = [2^(64m)]^s and Q_s = [2^(64(m+1))]^s, define

    B_s = productVaughanMajorant U V N s m
        = [Q_s^2 * vaughanShortMajorant(U,V,N,Q_s)
            + (6+2log(N+1)) * sum_{j in typeIILevels(N,U,V)}
                typeIIBlockMajorant(Q_s, 2^(j+1), floor(N/2^j))] / L_s.

`primitiveProductMangoldtMean_le_vaughan` proves the primitive conductor
mean is <= B_s for every s>=1 and V>=1. It retains the general unbalanced
Type II sum; no balanced-range assumptions are imposed.

`primeProductModuli_le_two_pow_mul_totient` gives d<=2^r*phi(d).
`primeProductModuli_add_one_le` and `prime_product_lift_remainder_le` give

    sum_{d in D_r} (d+1)*characterLiftError(d,N)/phi(d)
      <= 2^(r+1) * |D_r| * (Nat.log 2 N) * log(Q_r).

`productConductorVaughanRemainder r m N U V` is the explicit real expression

    E = sum_{s=1}^r [2^64/(m+1)]^(r-s)/(r-s)! * B_s(U(s),V(s))
          + 2^(r+1)*|D_r|*(Nat.log 2 N)*log(Q_r).

`prime_product_composite_error_le` and its named-remainder version
`prime_product_composite_error_le_remainder` bound the sum of the earlier
composite progression errors by E, for m>=1 and V(s)>=1 for 1<=s<=r.

`prime_product_mangoldt_total_lower_vaughan` then proves the unconditional
finite lower bound

    psi(N)*W_r - E <= sum_{d in D_r} psi(N;d,1).

This formula need not have a positive left side. No claim is made that E
is small at the scales required for the original conjecture.

### `ProductVaughanBarrier.lean`

Imports `Submission.ProductConductorMean`.

This file audits the explicit formula above for **all** cutoff choices,
not only the balanced choices from earlier parameter work.

- `log_dyadic_ge_one`, `typeIIBlockMajorant_lower`, and `pvMajorant_ge_one`
  supply elementary lower bounds on the nonnegative majorant terms.
- `vaughan_majorant_ge_central_scale`: for a>=2, Q>=1, and ANY U,V, the raw
  Vaughan majorant at N=2^(2a) is at least Q^2*2^a. Proof: if U>=2^a the
  short U*log(U) term is enough; if V>=2^(a+1) the other short term is enough;
  otherwise the central Type II level j=a is active and provides the bound.
- `productVaughanMajorant_ge_dyadic_square`: if 2^a<=L_s and a>=2, then
  B_s(U,V,2^(2a))>=2^(2a), for every U,V.
- `productVaughanMajorant_le_remainder`: the full-conductor term s=r occurs
  in E with coefficient exactly one, and all remaining terms are nonnegative.
- `product_conductor_vaughan_remainder_ge_scale`: for t>=4, m>=1,
  r=t-2, N=2^(64tm), and ANY cutoff functions U,V, E>=N.
- `product_conductor_vaughan_remainder_not_small`: at those scales it is
  impossible that E<=N/(m+1)^t.

These theorems concern the chosen upper-bound formula E, NOT the actual
character means or the actual signed prime-progression deficit. In particular,
they are not a disproof of the cofinal signed-deficit condition, still less a
disproof of Erdős 821. They show that completion-weight regrouping and arbitrary
Vaughan cutoff optimization cannot by themselves make this formula prove the
needed cofinal estimate. New arithmetic cancellation, a sharper estimate, or a
different approach is required.

### Implementation and final state

- The temporary `ConductorGroupingProbe.lean` API probe was removed.
- For finite-sum bijections involving PNat, annotate the source binder explicitly.
- Generic `positivity` sometimes unfolded large prime-block expressions and timed
  out; explicit `Nat.cast_nonneg`, `pow_nonneg`, and `div_nonneg` avoided this.
- The Type II single-summand lower bound required explicitly specifying the
  summand function to `Finset.single_le_sum`.
- No edits were made to `Submission/Spec.lean`. It retains the original `sorry`.
- No completed proof or disproof has been submitted.

## Signed local-character check (`SignedCharacterKernels.lean`)

The latest continuation examined signed character aggregates rather than
optimizing the absolute-value Vaughan bound. The new file imports
`Submission.CompositeCharacterErrors`, compiles, and has a built olean.
`SignedCharacterKernelsCheck.lean` checks the main types and reports only
`propext`, `Classical.choice`, and `Quot.sound`.

In `Erdos821.AnalyticSieve`, define

    localNonprincipalKernel q n
      = phi(q) * 1_{n=1 mod q} - 1_{gcd(n,q)=1}.

`localNonprincipalKernel_eq_mod` gives a computationally convenient natural
remainder formula. `nonprincipal_character_sum_eq_kernel` proves that this
real kernel (cast to complex) equals the sum of chi(n) over all nonprincipal
characters modulo any positive q. The principal-character term must be kept
at nonunits; replacing it by the constant one would be incorrect there.

`product_nonprincipal_sums_eq_kernel` gives the corresponding exact identity
for products of local sums over a finite set of positive moduli. It does not
assert an unproved bijection with primitive characters of the product modulus.

The signed weighted sum is

    signedLocalKernelSum P N
      = sum_{1<=n<=N} Lambda(n) * product_{q in P} localNonprincipalKernel(q,n).

The exact, non-numerical evaluation

    signed_local_kernel_sum_three_five:
    signedLocalKernelSum {3,5} 7 = -log(7)

and its strict negativity corollary are proved. The contributions at 2 and 4
cancel, those at nonunits 3,5,6 vanish, and the contribution at 7 is negative.
Thus even-order products of signed local kernels do not have automatically
nonnegative Mangoldt-weighted averages. This example refutes only that general
positivity shortcut: {3,5} is not claimed to be the entire geometric modulus
family, and the example says nothing against the conjecture's cofinal signed
estimate.

No new lower bound for the necessary high-order signed correlations was found.
The full conjecture remains unproved and undisproved. `Spec.lean` remains
unchanged, with its original `sorry`; no completed proof has been submitted.


## Unbalanced mean and below-square-root composite distribution (latest continuation)

Two new files compile without warnings and have built oleans:

- `Submission/UnbalancedVaughanMajorant.lean`
- `Submission/CompositeBelowHalfScales.lean`

Their corresponding `...Check.lean` files check the principal theorem types
and print only `propext`, `Classical.choice`, and `Quot.sound` as dependencies.
The temporary `UnbalancedProbe.lean` was removed.

### `UnbalancedVaughanMajorant.lean`

Imports `Submission.ProductConductorMean`.

`large_sieve_kernel_sqrt_le` bounds each square-root large-sieve kernel by
`2Q + 6sqrt(X)` when X>=1. `typeIIBlockMajorant_unbalanced_le` proves

    block(Q,X,Y) <= 36*T*H^3*(Q^2 + Q*R + T),

under X,Y>=1, T,R>=0, H>=1, XY<=T^2,
`sqrt(X)+sqrt(Y)<=R`, `1+log(X)<=H`, and `log(Y)<=H`.

Define `unbalancedTypeIIMajorant N Q B` to be

    (6+2log(N+1)) * (Nat.log 2 N + 1)
      * 288*(1+log(2N+1))^3 * (Q^2*sqrt(N) + Q*N/B + N).

`dyadic_majorant_unbalanced_le` bounds the entire Type II contribution by
this formula whenever `B>=1`, `B^2<=U+1`, and `B^2<=V`. In particular, there
is no balanced-range requirement comparing individual side lengths to Q^2.
The proof bounds active side lengths times B^2 by 2N.

`primitive_vonMangoldt_unbalanced_mean_bound` combines this with the general
Vaughan mean theorem. It allows separate endpoints R(q,chi)<=N and retains
all the usual family and primitiveness hypotheses explicitly.

In namespace `Erdos821`, `productUnbalancedMajorant U V N B s m` is

    [Q_s^2 * vaughanShortMajorant(U,V,N,Q_s)
       + unbalancedTypeIIMajorant(N,Q_s,B)] / L_s,

where Q_s=[2^(64(m+1))]^s and L_s=[2^(64m)]^s.

- `productUnbalancedMajorant_nonneg`
- `productVaughanMajorant_le_unbalanced`
- `primitiveProductMangoldtMean_le_unbalanced`

provide nonnegativity and the bridges to the earlier conductor mean.

### `CompositeBelowHalfScales.lean`

Imports `Submission.UnbalancedVaughanMajorant`.

The actual chosen cutoffs are

    N = progressionScaleN(t*m) = 2^(64*t*m),
    U = V = progressionScaleU(t*m) = 2^(6*t*m),
    B = 2^(3*t*m).

(An earlier informal idea used cutoffs independent of t; that is NOT the
choice used in this completed file.)

Assume 1<=s<=r, `2*r+1<=t`, and m>=2r. Then Q_s<=sqrt(N), but the smaller
conductor groups need not satisfy the old balanced block-length hypotheses.

Structural and parameter lemmas:

- `vaughanShortMajorant_mono_modulus`
- `product_modulus_below_sqrt`
- `unbalanced_majorant_scale_log_bound`: replaces logarithmic factors by
  `10^12*(l+1)^5` at N=progressionScaleN(l).
- `product_conductor_scale_ratios`: with
  `F=2^(128r)*2^((64t-1)m)`, all three quantities

      Q_s^2*sqrt(N)/L_s,  Q_s*N/B/L_s,  N/L_s

  are <=F, whenever 1<=s<=r and 2r+1<=t.

Define natural constants

    belowHalfMeanConstant(r,t)
      = 4,000,000,000,000 * 2^(128r) * (t+1)^5,

    belowHalfLiftConstant(r,t)
      = 2^(r+1) * 2^(64r) * 4096*r*t,

    belowHalfCompositeConstant(r,t)
      = r*2^(64r)*belowHalfMeanConstant(r,t)
          + belowHalfLiftConstant(r,t).

`product_unbalanced_below_half_bound` and
`primitive_product_below_half_bound` bound the chosen majorant and the actual
primitive conductor mean by

    belowHalfMeanConstant(r,t) * (m+1)^5 * 2^((64t-1)m).

The first holds for m>=2r, and the second inherits exactly the same conditions.

`primeProductReciprocalMass_le_two_pow` gives W_k<=2^(64k) for m>=1.
`primeProductModuli_card_le_upper` gives |D_r|<=Q_r.
`product_lift_below_half_bound` bounds the full lifting contribution by

    belowHalfLiftConstant(r,t) * (m+1)^5 * 2^((64t-1)m).

`composite_below_half_error_bound` then proves, whenever `2r+1<=t` and
`max 1 (2r)<=m`,

    sum_{d in D_r} compositeProgressionError(d,N)
      <= belowHalfCompositeConstant(r,t) * (m+1)^5 * 2^((64t-1)m).

Since 2^((64t-1)m)=N/2^m, this is a genuine power saving, not an unresolved
character-sum remainder.

`eventually_composite_below_half_error` proves that, for every fixed A,
this error is eventually <=N/(m+1)^A. It uses the already proved exponential
domination of any fixed natural polynomial.

The two exported arithmetic statements are

    eventually_product_mangoldt_discrepancy:
    for 2r+1<=t and any A, eventually in m,
      sum_{d in D_r} |psi(N;d,1)-psi(N)/phi(d)| <= N/(m+1)^A,

    eventually_product_mangoldt_total_lower:
    for 2r+1<=t and any A, eventually in m,
      psi(N)*W_r - N/(m+1)^A <= sum_{d in D_r} psi(N;d,1).

These statements have no unproved analytic input. The parameter restriction
is crucial: r/t<1/2. For the old cofinal criterion r=t-2, this range does not
cover t>=4, and no contradiction with `ProductVaughanBarrier` is asserted.

### Scope, possible next work, and unchanged conjecture

This completes the previously missing below-square-root composite-modulus
application of the character mean estimates. It does NOT prove the near-full
cofinal signed-deficit condition. No new multiplicity exponent or arbitrary
higher-root smooth-prime density was established.

A next positive application could convert the aggregate Mangoldt lower bound
into a count of primes whose predecessors have r distinct block-prime factors,
using the existing prime-power bounds and the binomial-moment overcount. This
would give a structured smooth-part density result in the same below-half
range; it must not be described as a settlement or as reaching the needed
cofinal near-full modulus levels.

The original `Submission/Spec.lean` is unchanged and retains its original
`sorry`. No complete proof or disproof has been submitted.


## Structured prime-predecessor family (`StructuredPrimeFactors.lean`)

The latest continuation completed the positive arithmetic application suggested
in the preceding section. `StructuredPrimeFactors.lean` imports
`Submission.CompositeBelowHalfScales` and `Submission.SmoothModulusMoments`.
It compiles without warnings, has a built olean, and has a corresponding audit
file `StructuredPrimeFactorsCheck.lean`. The audited main results depend only
on `propext`, `Classical.choice`, and `Quot.sound`.

Define

    structuredWitnessPrimes r m N
      = {p<=N prime : r <= card(blockPrimeDivisors m (p-1))}.

The support block is `(2^(64m), 2^(64(m+1))]`, as previously defined.

### Finite incidence and prime-power estimates

`prime_product_divisor_count_le_choose` generalizes the old special-case
`t-2` overcount: for 0<n<2^(64tm) and m>=1,

    #{d in primeProductModuli(r,m) : d|n} <= choose(t-1,r).

`sum_product_progressions_eq_incidence` gives the exact weighted incidence
identity for all natural product-modulus families.

`product_progression_weight_le_structured_count` proves, with N=2^(64tm)
and B=choose(t-1,r),

    sum_{d in D_r} psi(N;d,1)
      <= B*log(N)*(card(structuredWitnessPrimes r m N) + 2*sqrt(N)).

The same incidence bound is applied to proper prime powers, so their total
contribution is bounded by `2*B*sqrt(N)*log(N)`, independent of |D_r|.
The n=1 term vanishes because Lambda(1)=0.

### Main term and prime-count lower bound

`eventually_product_mangoldt_weight_lower` combines the below-half distribution
bound, the linear Mangoldt lower bound, and the reciprocal product-modulus
supply. For every fixed r,t with `2r+1<=t`, eventually

    N/[16*primeProductMassConstant(r)*(m+1)^r]
      <= sum_{d in D_r} psi(N;d,1).

Define

    structuredPrimeCountConstant(r,t)
      = 2048 * primeProductMassConstant(r) * t * choose(t-1,r).

`structured_prime_count_of_weight` is the finite transfer. Its explicit
prime-power budget is

    4096*choose(t-1,r)*primeProductMassConstant(r)*t*(m+1)^(r+1)
      <= 2^(32tm).

`eventually_structured_prime_count` removes this polynomial side condition
using exponential domination and proves, for `2r+1<=t`, eventually

    N <= structuredPrimeCountConstant(r,t)*(m+1)^(r+1)
           * card(structuredWitnessPrimes r m N).

### Witness extraction and smoothness

`structuredWitnessPrimes_has_divisor` extracts a modulus d in D_r dividing p-1
from the binomial count. It also records primality and p<=N.

`structuredWitnessPrimes_smooth` proves that, for `r+2<=t`, m>=2, and p in the
structured family at N=2^(64tm),

    p-1 is 2^(64*(t-r)*m)-smooth.

Indeed, d>=2^(64rm), its individual prime factors are smaller than the stated
smoothness bound, and p-1<N<=d*2^(64*(t-r)*m).

`eventually_structured_smooth_prime_family` exports a finite prime family with
all four properties: primality, the N upper cutoff, the smoothness cutoff,
and at least r distinct block-prime factors, together with the full polynomial
prime-count lower bound. It requires r>=1 and `2r+1<=t`.

### Scope and current state

This is an unconditional structured-density theorem, not merely a conditional
reduction. Nevertheless `(t-r)/t>1/2` in its proved range. It does not supply
arbitrarily small smoothness exponents, and it does not improve the strongest
existing multiplicity bound above one half. Its additional information is the
prescribed r-factor structure of the large smooth divisor of p-1.

A possible next analytic investigation is a second sieve on the remaining
cofactor while preserving the composite-modulus main term. No such sieve for
this new family has yet been proved, and no claim is made that it could reach
all root parameters using the current estimates.

The temporary `StructuredPrimeProbe.lean` was removed. `Submission/Spec.lean`
is unchanged with SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
It retains its original `sorry`. No completed proof or disproof has been submitted.

## Composite cofactor sieve and its cube-root cutoff limitation

The latest continuation completed the second-sieve investigation suggested
above. Three new source files compile without warnings and have built oleans
and corresponding `...Check.lean` audit files. The audited results use only
`propext`, `Classical.choice`, and `Quot.sound`.

### `CompositeRoughProgressions.lean`

Imports `Submission.RoughProgressions` and
`Submission.PrimitiveProductCharacters`.

In namespace `Erdos821.AnalyticSieve`:

* `composite_cofactor_totient_ratio_sq` generalizes the ratio bound to any
  positive modulus d; it retains `(d/phi(d))^2` rather than inserting 4.
* `sum_prime_pair_composite_cofactor_bound` proves, with
  `E_J = 2^(64J)+2^(16J)+1`, for dK<=X and J>0,

      sum_{1<=k<=K} primePairCofactorCount(X,dk)
        <= 16*Cavg*X*harmonic(K)/(J log2)^2 * d/phi(d)^2 + K*E_J.

* `rough_composite_progression_card_le_pairs` covers the rough primes by
  these prime pairs for any positive Y-smooth d, assuming X<=dKY. A prime
  ell>=Y cannot divide d, hence coprimality permits cancellation of ell.
* `rough_composite_progression_prime_count_le` combines these bounds.
* `rough_composite_progression_reciprocal_count_le` uses d<=2phi(d), giving

      |roughProgressionPrimes(d,Y,X)|
        <= 32*Cavg*X*harmonic(K)/(J log2)^2 / phi(d) + K*E_J.

* `rough_composite_family_reciprocal_count_le` sums over an arbitrary finite
  smooth modulus family, retaining its reciprocal-totient mass.

In namespace `Erdos821`:

* `prime_product_modulus_totient_ratio` proves, for d in D_r(m), L=2^(64m),

      L*d <= (L+2^r)*phi(d).

  It bounds every proper-divisor totient by phi(d)/L and uses
  sum_{c|d}phi(c)=d and tau(d)=2^r.
* `prime_product_modulus_le_twice_totient` gives d<=2phi(d) if 2^r<=L.

### `StructuredSecondSieve.lean`

Imports `Submission.CompositeRoughProgressions` and
`Submission.StructuredPrimeFactors`.

Define `smoothStructuredPrimes r m N Y` by filtering the structured family
for Y-smooth predecessors. Let N=2^(64tm), B=choose(t-1,r), W=W_r(m).

* `sum_rough_product_counts_eq_incidence` is the exact rough incidence
  counting identity, with each prime weighted by the number of product
  moduli dividing its predecessor.
* `product_progression_weight_le_smooth_structured_count` proves

      sum_D psi(N;d,1)
        <= log(N)*(B*|G| + sum_D |roughProgressionPrimes(d,Y,N)|
                         + 2B sqrt(N)).

  Importantly, the rough incidence sum is NOT multiplied by B.
* `eventually_product_mangoldt_weight_lower_reciprocal` proves, for
  2r+1<=t, eventually in m,

      N/16 * W <= sum_D psi(N;d,1).

  The prior numerical main-term lower bound is not substituted here.
* `smooth_structured_weight_retained` is a finite sufficient criterion:
  if the preceding main term holds, rough incidences are <= A*W+E,
  log(N)*A<=N/64, and log(N)*(E+2B sqrt(N))<=N*W/64, then

      N*W/32 <= B*log(N)*|G|.

  These last budgets are explicit hypotheses, not assertions that they hold
  at arbitrary smoothness levels.

### `CompositeSecondSieveBarrier.lean`

Imports `Submission.StructuredSecondSieve`.

This audits a particular upper-bound formula, NOT the true rough prime
count and NOT the conjecture. Put

    c=t-r-b, N=2^(64tm), Y=2^(64bm), K=2^(64cm), L=2^(64rm),
    A=32*Cavg*N*harmonic(K)/(J log2)^2,
    E_J=2^(64J)+2^(16J)+1.

Define

    compositeSecondSieveCost = log(N)*(A + L*K*E_J),
    compositeSecondSieveMajorant = log(N)*(A*W + |D_r|*K*E_J).

* `totientRatioAverageConstant_ge_one`, `log_progression_scale_ge`, and
  `harmonic_progression_scale_ge` provide elementary lower bounds.
* `cube_root_cofactor_exponent_bound`: if 2r<=t and 3b<=t, then
  b^2<=2t(t-r-b).
* `composite_second_sieve_main_ge_scale`: under those two restrictions,
  J>0 and J<=bm imply log(N)*A>=N.
* `composite_second_sieve_cost_ge_scale`: for t,m,J>=1, 2r<=t, 3b<=t,
  the cost is >=N for EVERY J. For J<=bm use the preceding result; for
  J>bm, L*K*2^(64J)>=N, and log(N)>=1.
* `prime_product_mass_mul_lower_le_card` proves L*W<=|D_r| from
  phi(d)>=L for each product modulus.
* `composite_second_sieve_cost_mul_mass_le` and
  `composite_second_sieve_majorant_ge_scale_mass` therefore show that
  the actual explicit majorant is >=N*W in the same cube-root range.
* `composite_second_sieve_rejected_weight_le` verifies that this IS the
  bound given by the composite second sieve, under the scale conditions
  r+b<=t, b,m>=2, r<=bm, 2^r<=2^(64m), J>0.
* `composite_second_sieve_majorant_not_small`: if additionally W>0,
  this formula cannot be <=N*W/16, for ANY J.

### Scope and remaining gap

The suggested composite-modulus second sieve is now formalized, including
the correct pre-overcount subtraction. It can potentially give structured
families with a fixed improvement below square-root smoothness, but no new
multiplicity exponent was instantiated in this continuation.

More importantly, the exact cutoff audit shows that this PARTICULAR bound
cannot reach cube-root smoothness by parameter tuning, even after removing
the unnecessary binomial loss. It cannot establish the arbitrary-root
series criterion needed to settle the original conjecture. This is not an
assertion that the true rejected count is large. A genuinely stronger
estimate or a different argument would be necessary.

The temporary `CompositeRoughProbe.lean` was removed. All three new sources
compile; no pending proof is left in them. The original `Submission/Spec.lean`
is unchanged, with SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
It still contains its original `sorry`. No proof or disproof of the conjecture
has been submitted.

## Positive composite-sieve application: improved fixed multiplicity gain

The latest continuation went beyond the cutoff limitation and completed an
unconditional structured prime count at a fixed smoothness exponent strictly
below one half. It also transferred that count to a stronger fixed
multiplicity exponent. The original conjecture remains UNSOLVED.

Two new sources, `StructuredStrictHalfScales.lean` and
`CompositeMultiplicityGain.lean`, compile without warnings and have built
oleans and `...Check.lean` audits. The audited main results use only
`propext`, `Classical.choice`, and `Quot.sound`.

### Concrete parameters and definitions

`StructuredStrictHalfScales.lean` imports
`Submission.CompositeSecondSieveBarrier` (which transitively supplies the
positive composite-sieve and structured-family theorems).

For a fixed natural a, set

    r = 2a, t = 4a+1,
    strictStructuredN(a,m) = N = 2^(64(4a+1)m),
    strictStructuredY(a,m) = Y = 2^(128am),
    strictStructuredJ(a,m) = J = (2a-1)m,
    K = 2^(64m),
    B = choose(4a,2a),
    W = primeProductReciprocalMass(2a,m).

`strictStructuredPrimes a m` is the family of primes p<=N with at least
2a predecessor prime factors in the block `(2^(64m),2^(64(m+1))]`, whose
predecessors are also Y-smooth. Define

    strictStructuredSieveMain = A = 32*Cavg*N*harmonic(K)/(J log2)^2,
    strictStructuredSieveError = E = |D_(2a)|*K*(2^(64J)+2^(16J)+1),
    strictStructuredErrorConstant(a)
      = 64(4a+1)*(3*2^(128a)+2*choose(4a,2a)).

### Main-term and error bounds

Assume `10000000*Cavg <= a`. This also implies a>=10.

* `strict_structured_coefficient_bound` proves

      8519680*Cavg*(4a+1) <= (2a-1)^2.

* `strict_structured_harmonic_upper` uses m>=2 to show
  `harmonic(2^(64m)) <= 65*m*log2`.
* `strict_structured_sieve_main_small` then gives `log(N)*A <= N/64`.
  Keeping the exact log2 factors, rather than bounding both sides crudely,
  improves the constant significantly.
* `strict_structured_sieve_error_pow_bound` and
  `strict_structured_sqrt_pow_bound` bound the cofactor-sieve error and
  prime-power contribution using `R = 2^((256a+63)m)`.
* `strict_structured_total_error_pow_bound` gives

      log(N)*(E+2B sqrt(N)) <= ErrorConstant(a)*(m+1)*R.

  Since `2^m*R=N`, exponential domination absorbs every fixed polynomial.
* `strict_structured_rough_count_le` is the actual rough incidence bound
  `sum_D |roughProgressionPrimes(d,Y,N)| <= A*W+E`, valid for a>=1 and
  m>=max(2,a).
* `eventually_product_reciprocal_supply r` exports the existing eventual
  lower bound `W_r >= 1/(MassConstant(r)*(m+1)^r)` in reusable form.
* `eventually_strict_structured_total_error_small` proves

      eventually_m, log(N)*(E+2B sqrt(N)) <= N*W/64.

### Retained family and count

* `eventually_strict_structured_retained_weight` combines the two sieve
  budgets with the unconditional below-half progression main term:

      eventually_m, N*W/32 <= B*log(N)*|strictStructuredPrimes(a,m)|.

* `strict_structured_count_of_weight` and
  `eventually_strict_structured_prime_count` give the natural-number count

      N <= structuredPrimeCountConstant(2a,4a+1)*(m+1)^(2a+1)*|G|.

* `eventually_strict_structured_smooth_family` exports the finite family,
  the count, and all four pointwise properties (prime, <=N, Y-smooth
  predecessor, and >=2a block-prime predecessor factors).

These are unconditional results under the explicit numerical restriction
on the fixed parameter a. The smoothness ratio is `2a/(4a+1)<1/2`.

### Improved multiplicity exponent

`CompositeMultiplicityGain.lean` imports
`Submission.StructuredStrictHalfScales` and
`Submission.PolynomialDensityTransfer`.

* `composite_sieve_complementary_exponent` checks the exact identity

      1 - 128a/[64(4a+1)] = 1/2 + 1/(8a+2).

* `infinite_g_gt_composite_sieved_limit` proves

      10000000*Cavg <= a, gamma < 1/2 + 1/(8a+2)
        ==> {n : (g(n):R) > (n:R)^gamma}.Infinite.

* Choosing `a = ceil(10000000*Cavg)`,
  `infinite_g_gt_composite_uniform` removes the auxiliary parameter:

      gamma < 1/2 + 1/(80000000*Cavg+10)
        ==> {n : (g(n):R) > (n:R)^gamma}.Infinite.

* `erdos_821_composite_range` expresses this as the original conclusion
  restricted to

      epsilon > 1/2 - 1/(80000000*Cavg+10).

* `composite_uniform_gain_gt_eighty_old_gain` verifies that this explicit
  fixed gain exceeds 80 times the corresponding uniform gain obtained by
  choosing r=ceil(150994944*Cavg) in the previous strongest result:

      80 * [3/(19327352832*Cavg+128)] < 1/(80000000*Cavg+10).

This is an improvement within this formal development, not a claim to beat
external literature. The exponents are still near one half. INCREASING a
DECREASES the gain, so this theorem does not approach exponent one. In
particular it does not establish the arbitrary-root series criterion or
settle the conjecture.

### Current state

The best fixed multiplicity exponent in this development is now supplied
by `infinite_g_gt_composite_uniform`, rather than the older
`infinite_g_gt_sieved_limit`. There is no pending uncompiled source. The
temporary `CompositeGainProbe.lean` was removed.

`Submission/Spec.lean` remains unchanged with its original `sorry` and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof or disproof has been submitted.

## Exact large-prime moments and divisor switching

The latest continuation examined a possible higher-order replacement for the
first-moment rejection sieve. It completed two new finite-identity files:
`LargePrimeMoments.lean` and `LargePrimeProducts.lean`. Both compile without
warnings, have built oleans, and have corresponding `...Check.lean` audits.
The audited main results use only `propext`, `Classical.choice`, `Quot.sound`.

No analytic estimate for the new correlations has been proved, and no new
multiplicity exponent was obtained in this continuation. The best current
fixed exponent remains `infinite_g_gt_composite_uniform`.

### `LargePrimeMoments.lean`

Imports `Submission.StructuredSecondSieve`.

Define

    largePrimeDivisors(Y,n) = {q in n.primeFactors : Y<=q},
    ell_Y(n) = card(largePrimeDivisors(Y,n)).

* `largePrimeDivisors_card_zero_iff`: for n>0, ell_Y(n)=0 iff n is Y-smooth.
* `smooth_divisor_large_prime_product_dvd`: if a Y-smooth d divides n,
  then d times the product of all the distinct large prime divisors of n
  divides n. This uses coprimality with the smooth d.
* `smooth_divisor_large_prime_power_le`: for n>0, d*Y^ell_Y(n)<=n.
* `largePrimeDivisors_card_lt_of_smooth_divisor`: if Y>=1 and n<d*Y^s,
  then ell_Y(n)<s.

Define the real alternating binomial partial sum

    binomialSievePartial(n,k) = sum_{j=0}^k (-1)^j choose(n,j).

The zero, positive-n, exact-indicator, odd lower-bound, and even upper-bound
identities are proved from Mathlib's integer alternating-binomial formula.

For a finite family P and real weights w, define

    largePrimeMoment(P,w,Y,j)
      = sum_{p in P} w(p)*choose(ell_Y(p-1),j),
    largePrimeSievePartial(P,w,Y,k)
      = sum_{j=0}^k (-1)^j largePrimeMoment(P,w,Y,j).

* `largePrimeSievePartial_eq_pointwise` exchanges the two finite sums.
* `smooth_prime_weight_eq_large_moments`: for p>=2 in P and ell_Y(p-1)<=k,
  the Y-smooth predecessor weight is exactly this alternating sum.
* `smooth_prime_weight_bonferroni`: for nonnegative w, odd truncations are
  lower bounds and even truncations upper bounds, without a cap on ell.
* `smooth_prime_weight_eq_first_moment`: if each p has a Y-smooth divisor
  d of p-1 with p-1<d*Y^2, the smooth weight is exactly M_0-M_1.

### `LargePrimeProducts.lean`

Imports `Submission.LargePrimeMoments`.

Define

    largePrimeBasis(Y,N) = primes q with Y<=q<=N,
    largePrimeProducts(Y,N,j)
      = products of j distinct primes in this basis.

* `large_prime_product_divisor_count`: for 0<n<=N, the number of these
  products dividing n is choose(ell_Y(n),j).
* `largePrimeProducts_pos`, `largePrimeProducts_lower`, and
  `smooth_coprime_largePrimeProducts` prove positivity, a>=Y^j, and
  coprimality with a Y-smooth d.
* `largePrimeMoment_eq_product_sum`: the moment is the weighted incidence
  sum over all selected large-prime products.
* `largePrimeMoment_progression_eq`: within primes p<=N with d|p-1, for
  Y-smooth d, the j-th moment equals the sum of progression weights at
  moduli d*a, a in largePrimeProducts(Y,N,j).

Define

    shiftedPrimeCofactors(N,q)
      = {1<=k<=(N-1)/q : q*k+1 is prime}.

* `prime_progression_weight_eq_cofactors` proves the exact weighted
  bijection between primes p<=N with q|p-1 and these cofactors (q>0).
  The endpoints and p=2 case are included.
* `largePrimeMoment_progression_eq_cofactors` gives

      M_j(d,Y,N;w)
        = sum_{a in largePrimeProducts(Y,N,j)}
            sum_{k in shiftedPrimeCofactors(N,d*a)} w(d*a*k+1).

* `largePrimeProducts_one` identifies the j=1 product family with the
  large-prime basis.
* `large_prime_selected_cofactor_le`: every selected cofactor satisfies
  k<=(N-1)/(d*Y^j), for d>0 and Y>=1.
* `smooth_progression_weight_eq_switched_moments`: if N<=d*Y^(s+1),
  the Y-smooth progression weight is the alternating sum of these switched
  correlations for 0<=j<=s.
* `smooth_progression_weight_eq_sub_large_pairs`: if N<=d*Y^2, this is
  exactly the total prime progression weight minus the j=1 large-prime
  pair sum; it is NOT merely a union-bound inequality.
* `largePrimeMoment_progression_eq_zero_of_large_order`: if N<=d*Y^j,
  the j-th moment vanishes identically.

### What this does and does not supply

These identities expose a potential higher-order analytic route and preserve
all endpoints and multiplicities. They do NOT bound the new prime
correlations. For odd-order Bonferroni lower bounds one would need suitable
upper estimates for negative terms and lower estimates for positive terms.
Those estimates are not supplied by the existing first-moment upper sieve.

In particular, when d is close to the square-root scale and Y is at the
cube-root scale, N<=d*Y^2: there is at most one large prime factor, so all
higher moments vanish. Merely adding higher-order inclusion-exclusion terms
to that family cannot repair the previously audited first-moment bound.
One would need either stronger prime-pair estimates there, or a different
parameter regime together with genuinely new higher-correlation estimates.
No such claim is made in the new files.

The temporary `LargePrimeMomentsProbe.lean` was removed. There is no pending
uncompiled source. `Submission/Spec.lean` remains unchanged with its original
`sorry` and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The conjecture remains unsolved; no proof or disproof has been submitted.

## A finite-model test of the proposed low-to-high moment bootstrap

After further analytic searches and unsuccessful attempts to close the main
gap, the latest continuation tested a possible purely moment-theoretic
bootstrap. It found and formalized an exact obstruction to that inference.
This is a limitation of the information in a finite initial moment segment,
NOT a disproof of Erdős 821 or a model claimed to describe the actual primes.

New source files `TruncatedMomentModels.lean` and `ProductMomentModels.lean`
compile without warnings and have built oleans and corresponding
`...Check.lean` audits. The audited theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.

### `TruncatedMomentModels.lean`

Imports `Submission.LargePrimeMoments`.

For a real sequence M and truncation R, define weights recursively from the
top down:

    truncatedMomentWeight(R,M,k) = 0                         if k>R,
    truncatedMomentWeight(R,M,k)
      = M(k) - sum_{j=k+1}^R choose(j,k)*weight(j)             if k<=R.

The recursion terminates on R+1-k; it contains no partial or unsafe code.

* `truncatedMomentWeight_moment_Icc` and `truncatedMomentWeight_moment`
  prove the exact triangular moment equations, for every k<=R:

      sum_{j=0}^R choose(j,k)*weight(j) = M(k).

* `truncatedMomentWeight_nonneg` proves all weights are nonnegative if
  M(k)>=0 for k<=R and

      (k+1)*M(k+1) <= M(k),  k<R.

  Its key elementary inequality is
  choose(j,k)<=(k+1)*choose(j,k+1) for j>k. Using the already established
  next moment equation bounds the tail subtracted in the recursion by
  (k+1)M(k+1)<=M(k).

* `exists_truncated_binomial_moment_model` normalizes this construction
  when M(0)=1: nonnegative weights, support in {0,...,R}, total mass one,
  and all requested initial binomial moments.

* Define `poissonBinomialMoment(mu,k)=mu^k/k!`.
  `poissonBinomialMoment_step` gives its exact consecutive-moment ratio.
  `exists_truncated_poisson_moment_model` specializes the construction for
  0<=mu<=1. Thus even exact initial Poisson moments do not force any tail
  beyond their specified order.

### `ProductMomentModels.lean`

Imports `Submission.TruncatedMomentModels`, whose existing dependency chain
includes the product-modulus completion and binomial-incidence identities.
Write W_r(m)=primeProductReciprocalMass r m.

* `blockPrimeDivisors_eq_primeFactors_of_product` identifies the block
  divisor set of a product modulus with its full prime-factor set.
* `singleton_product_divisor_count` gives r singleton product-modulus
  divisors of an r-factor product.
* `primeProductReciprocalMass_zero` proves W_0=1.
* `primeProductReciprocalMass_succ_ratio` proves

      (r+1)*W_(r+1) <= W_1*W_r.

  This is obtained by counting singleton divisors in the weighted
  completion sum, then dropping the coprimality restriction in the
  complementary-product weight.

* `primeProductReciprocalMass_one_le_one` proves W_1<=1 for m>=2^64 from
  the previously established block reciprocal-mass upper bound.

* `exists_truncated_product_moment_model` therefore proves, for EVERY
  truncation R and every m>=2^64, the existence of nonnegative weights w
  supported on {0,...,R}, with total one, satisfying exactly

      sum_{j=0}^R choose(j,k)*w(j) = W_k(m),  for every k<=R.

* `eventually_product_moment_model_with_zero_next` additionally uses the
  reciprocal supply lower bound to show that, eventually in m,

      W_(R+1)(m)>0,

  while such a model still has

      sum_{j=0}^R choose(j,R+1)*w(j)=0.

### Interpretation and unchanged conjecture

This invalidates an inference based solely on nonnegative normalized counts
and exact agreement of finitely many low-order factor-count moments with
these main terms. Even ideal low-order main terms are compatible, at that
abstract level, with no mass at higher factor counts. Additional arithmetic
or distribution information is necessary.

The model does NOT assert that actual primes have these truncated counts,
that it can be realized by all primes below the required cutoff, or that
the conjecture is false. No new multiplicity exponent was obtained in this
continuation. The best current bound is still
`infinite_g_gt_composite_uniform`.

The temporary `MomentModelProbe.lean` was removed. No pending uncompiled
source remains. A `positivity` timeout in the final reciprocal-mass
positivity step was resolved by supplying a typed denominator-positivity
proof, avoiding unfolding the huge finite prime sets.

`Submission/Spec.lean` remains unchanged with its original `sorry` and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof or disproof has been submitted.

## Total-size-constrained partition moment tests (latest continuation)

This continuation tested whether the exact total logarithmic factor size could
repair the previous finite-moment bootstrap. Two new finite certificates have
been kernel-checked. Neither is a prime model or an asymptotic counterexample.
No improvement in the multiplicity exponent or settlement was obtained.

### `PartitionMomentModel.lean`

The namespace `Erdos821.PartitionMomentModel` gives a distribution on 25
partitions of 12, with positive integer masses summing to 1,136,520. It proves:

* Every part is positive, every outcome has total size exactly 12, and every
  outcome has a part at least 5.
* `mean_one`: the normalized rational mass is one.
* `mean_count`: for every j in {1,...,12}, E[C_j] = 1/j.
* `mean_low_weight_moment`: for all nonnegative a,b,c,d,e with
  a+2b+3c+4d+5e <= 5,

      E[choose(C_1,a) choose(C_2,b) choose(C_3,c)
        choose(C_4,d) choose(C_5,e)]
      = 1/[a! 2^b b! 3^c c! 4^d d! 5^e e!].

* `mean_cube_root_smooth_zero`: the indicator that every part j satisfies
  3j <= total size has expectation zero.

Thus these particular finite joint moments strictly below half the total,
even with exact total size AND all single-part means, do not force a
cube-root-smooth outcome.

### `HalfPartitionMomentModel.lean`

The namespace `Erdos821.HalfPartitionMomentModel` gives a second distribution
on 35 partitions of 12, with positive integer masses summing to 448,779,260,160.
It includes the half-size endpoint in its joint-moment conditions:

* Every outcome has total 12, positive parts, and a part at least 4.
* The normalized mass is one and E[C_j]=1/j for ALL j in {1,...,12}.
* `mean_half_weight_moment` gives the analogous exact binomial moment formula
  for a+2b+3c+4d+5e+6f <= 6, with denominator
  a! 2^b b! 3^c c! 4^d d! 5^e e! 6^f f!.
* `mean_fourth_root_smooth_zero` gives zero mass to outcomes for which
  4j <= total size for every part j.

The second certificate avoids attributing the entire obstruction to omission
of the half-size endpoint. The root threshold differs: it concerns fourth-root,
not cube-root, smoothness.

### Verification and scope

The rational tables were found with Sage, but the Lean proofs do not trust
Sage, floating-point computations, `native_decide`, or any external solver.
The integral identities and finite structural properties are proved with
kernel-checked `decide`; the rational identities follow by exact arithmetic.
Both source files compile cleanly and have fresh oleans. Their corresponding
`...Check.lean` files compile cleanly and audit all principal theorem types
and axioms. Only `propext`, `Classical.choice`, and `Quot.sound` occur.

These are fixed finite partition models. They do not model actual primes,
do not supply models at arbitrarily fine logarithmic resolutions, and do not
rule out an argument using uniform asymptotic or additional arithmetic data.
They are NOT disproofs of Erdos 821. The strongest unconditional multiplicity
bound is unchanged: `infinite_g_gt_composite_uniform`.

`Submission/Spec.lean` remains unchanged, still with the original `sorry`.
Its SHA-256 is still
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
There is no complete proof or disproof to submit.

## Complementary-divisor continuation audit (no new theorem)

Re-examined the cofinal signed-deficit criterion and the exact divisor-switching
identities. For d in the product-modulus family D_(t-2)(m), the complementary
cofactor k=(p-1)/d is short. However, after switching, the prime progression
modulo k retains the condition (p-1)/k in D_(t-2)(m). Ordinary unweighted
progression estimates at this short modulus do not lower-bound this restricted
subset of its primes. Dropping the restriction would give the wrong direction
for the required lower bound.

No estimate of the resulting weighted prime sum, new multiplicity exponent,
proof, or disproof was obtained. No Lean source was changed in this continuation.
`Spec.lean` is still unchanged and contains its original `sorry`. The previously
completed finite partition models must not be promoted to asymptotic models or
to assertions about actual primes.

## Global prime-chain continuation audit (no new theorem)

Investigated whether power-saving scarcity of root-smooth predecessors could
be contradicted by following large prime factors recursively. The implication
from non-smoothness gives a child q with q^k > p-1. Iteration can impose a lower
bound on the depth before reaching small primes, but it supplies no contradiction
with the available size decrease. A counting theorem for whole prime-chain
structures avoiding the exceptional smooth family would be a new arithmetic
input; none was proved. The existing pointwise nontransitivity example at 11
remains a separate, narrower result.

No Lean source was changed, no new exponent was obtained, and no complete proof
or disproof is ready. `Spec.lean` retains its original `sorry`.

## Average rough-part multiplicity audit (no new theorem)

Checked whether the multiplicity construction could use only control of the
logarithmic mass of large prime factors, instead of full predecessor smoothness.
A pointwise bound of X^rho on the part supported above X^delta already makes
the predecessor smooth at scale X^max(delta,rho). A suitably small average
logarithmic bound would allow extraction of a large pointwise-bounded subfamily.
No unconditional estimate making both parameters tend to zero while preserving
the required prime-count exponent was obtained. The common-smooth-part and
prime-block lemmas in `Work.lean` do not themselves supply it.

This was an informal audit, not a new formal theorem. No Lean source was changed,
and the original conjecture in `Spec.lean` remains unproved and undisproved.

## Power-sparse sets propagated through large-child prime chains

A new concrete global consequence of the hypothetical negation has now been
formalized. This does not prove the conjecture or its negation, and does not
improve the strongest unconditional multiplicity exponent.

### `LargeChildPropagation.lean`

This file imports `Submission.Density` and defines:

* `largeDivisorLift k A`: positive integers n with a positive divisor q in A
  satisfying n <= q^k.
* `largeChildParents k A`: primes p with a prime q in A such that q divides
  p-1 and p-1 <= q^k.
* `largeChildLayer k A L`: the set from which A can be reached in at most L
  such steps, including A itself.
* `largeChildAvoidingPath k A L p`: a path of L STRICT large-child edges
  starting at p, avoiding A at every vertex.

The generic weighted-divisor lemma proves `summable_largeDivisorLift`: if the
power series of A converges at exponent b, and s<=u, u>1, and

    k*(u-s)-u <= -b,

then the corresponding lifted series converges at exponent s.
`summable_largeChildParents` transfers this bound across p -> p-1 for s>=0.

For k>=1 and 0<=b<1, the explicit choice

    next exponent = 1-(1-b)/(2*k)

retains a positive gap below one. Iterating gives

    largeChildLayerExponent k b L = 1-(1-b)/(2*k)^L.

`summable_largeChildLayer` proves convergence at that exponent for EVERY FIXED
L. The remaining primes retain reciprocal divergence by
`not_summable_reciprocal_outside_largeChildLayer`, hence in particular are
infinite. The result does not assert a uniform positive exponent gap as L grows.

`outside_largeChildLayer_has_avoiding_path` constructs the corresponding strict
path whenever every prime outside A has a strict large child.

### `SparseSmoothPrimeChains.lean`

This imports the generic propagation result and `HigherRootReduction`.
`rootSmoothPrimeSet k` is the set of primes with kth-root-smooth predecessors.

* `exists_sparse_rootSmoothPrimeSet_of_negation`: assuming the EXACT negation
  of the original conjecture, some k>=3 and b in [0,1) give a convergent
  b-weighted series on this smooth prime set.
* `negation_forces_sparse_large_child_layers`: under that explicit assumption,
  every fixed-depth ancestor layer has the explicit convergent series above,
  while its prime complement has divergent reciprocal sum.
* `negation_forces_reciprocal_many_avoiding_paths`: under the same assumption,
  every fixed path length is realized by a reciprocal-divergent set of prime
  starting vertices, with all vertices outside the smooth set.
* `prime_mem_some_root_smooth_ancestor_layer` and
  `root_smooth_ancestor_layers_cover_primes` show UNCONDITIONALLY that each
  individual prime belongs to some finite layer, and the union of all layers
  is precisely the set of primes. The depth depends on the prime.

There is no contradiction between the fixed-depth summability and the union
covering all primes: the exponent gap tends to zero with L. No uniform chain
counting estimate closing that issue has been proved. In particular, the
explicit `Hneg` arguments must NOT be mistaken for proofs of the negation.

### Verification and current state

Both files compile cleanly, have fresh oleans, and have clean corresponding
`...Check.lean` type/axiom audits. All principal theorems depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The temporary `ChainProbe.lean`
was removed. There is no pending unfinished auxiliary Lean proof.

`Submission/Spec.lean` is unchanged, retains its original `sorry`, and has SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof or disproof is ready for submission.


## Explicit masses and growing-depth prime-chain consequences

This continuation completed the pending code and strengthened its application
from a single avoiding path to all eligible branches.

### `LargeChildPropagation.lean`: finite bound extracted

`sum_largeDivisorLift_le` is now the finite-sum version of the original
summability estimate. Its upper bound is

    (sum' a, a^(-u)) * (sum' q, A.indicator(q^(-b)) q).

`summable_largeDivisorLift` wraps this bound. Its previous public statement is
unchanged. The source, olean, and updated check file all pass.

### `LargeChildMass.lean`: explicit layer masses

`setPowerMass A s` is the sum of n^(-s) over A. For k,R>=1 and 0 not in A,
assuming summability at 1-1/R, `setPowerMass_largeChildLayer_le` proves

    mass(layer L, 1-1/(R*(2k)^L))
      <= mass(A,1-1/R) * (1+2R)^L * (2k)^(L^2).

The factor uses the existing `pseries_one_add_inv_le` from
`UniformRankin.lean`. `largeChildLayer_card_le` gives the corresponding finite
count bound at arbitrary N>=1. All intermediate finite-sum, union,
monotonicity, and reciprocal-exponent lemmas are audited.

### `GrowingLargeChildDepth.lean`: depth grows with the cutoff

Definitions:

    t_L = largeChildDepthScale k R L = R*(2k)^(2L)
    X_L = largeChildDepthCutoff k R L = 2^t_L.

`eventually_growing_largeChildLayer_count_small` proves, for every fixed J,

    eventually in L: t_L^J * #{n<=X_L : n in layer L} <= X_L.

The proof compensates the layer exponent gap by the factor 2^((2k)^L),
which eventually dominates the explicit mass factor and each fixed power of
t_L. `eventually_growing_prime_complement_large` then uses the elementary
dyadic Chebyshev lower bound and the J=2 saving to prove

    eventually in L: pi(X_L) <= 2*#{p<=X_L : p prime, p not in layer L}.

The pending incorrect parameter name in `Nat.le_of_mul_le_mul_left` was fixed.
The complete current source, not just an older olean, now compiles cleanly.

### `LargeChildAvoidingTrees.lean`: exact full-tree property

`largeChildAvoidingTree k A L p` recursively says that p and every vertex
reachable in at most L weak large-child steps are prime and outside A.
Weak edges have q prime, q dividing p-1, and p-1<=q^k, exactly as in the
ancestor-layer definition.

`largeChildAvoidingTree_iff` proves the exact equivalence

    largeChildAvoidingTree k A L p
      <-> p.Prime and p not in largeChildLayer k A L.

`largeChildAvoidingTree_has_path` recovers a strict avoiding path under the
usual splitting hypothesis. Thus the new tree result retains the information
about *all* eligible children that is lost by selecting only one path.

### `GrowingSmoothPrimeChains.lean`: application to the exact negation

The negation of the original conjecture remains an explicit `Hneg` hypothesis.
`exists_reciprocal_exponent_above` chooses R with b<=1-1/R, allowing the
previous sparse smooth-prime series to use the explicit mass bounds.

* `negation_forces_growing_sparse_layers`: some k>=3,R>=1 have all fixed
  binary-logarithm savings at the above growing depths and cutoffs.
* `negation_forces_growing_many_avoiding_paths`: eventually at least half the
  primes <=X_L start strict avoiding paths of length L.
* `negation_forces_growing_many_avoiding_trees`: the stronger conclusion that
  at least half those primes have the full depth-L avoiding-tree property.

These do not prove `Hneg`, nor do they derive False from it. Since
log(log(X_L)) = 2L*log(2k)+O(1), the resulting depth is only a fixed multiple
of log log X_L. The available chain-size and chain-count arguments do not
contradict this behavior. No new unconditional multiplicity exponent or
arbitrary-higher-root smooth-prime bound was obtained.

### Verification

All four new files have clean corresponding `...Check.lean` audits and fresh
oleans. The propagation and sparse smooth-chain checks were rerun after the
refactor. All audited results depend only on `propext`, `Classical.choice`,
and `Quot.sound`. `ChainMassProbe.lean` was removed. No `sorry`, `admit`, or
new axiom occurs in the six chain/mass source files checked in this continuation.

`Submission/Spec.lean` remains unchanged, with SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
It still contains the original `sorry`. No complete proof or disproof is ready
for submission, and no submission tool was called.


## Canonical largest-factor parent mass: a locally admissible test pattern

The continuation first checked whether the hypothetical negation had lost
quantitative information when reduced to one power-sparse smooth-prime set.
It had not: `erdos_821_iff_smooth_shifted_all_exponents` is an exact equivalence.
Sparsity uniform in all larger root parameters follows already by antitonicity,
so that observation supplies no new contradiction.

A new candidate was to assign each rough prime to the unique largest prime
factor of its predecessor, removing the overcount in the all-large-divisor
ancestor bounds. One tempting sufficient input would be an eventual pointwise
reciprocal parent-mass bound c/q with c<1. This input was tested before trying
to build a proof around it.

### `CanonicalParentMassTest.lean`

`canonicalRoughParentFinset k q` consists of primes p with

    q divides p-1,
    p-1 < q^k,
    every prime factor of p-1 is <=q.

It is represented as a finite subset of range(q^k+1).
`canonicalParentReciprocalMass k q` sums 1/p over this finset.
`canonicalRoughParent_unique` verifies uniqueness of q when q is prime.

The concrete coefficient set is

    A = {2,6,8,12,20,30,42,56,72}
      = {n*(n+1) : 1<=n<=8} union {8}.

* `canonicalTestCoefficients_reciprocal_sum` proves the exact rational
  identity sum(a in A,1/a)=73/72.
* `canonicalTestCoefficients_admissible` proves that for every prime ell there
  is an r such that neither r nor any a*r+1 (a in A) is divisible by ell.
  For ell<=10, r=191 works for ell=2,3,5,7. For ell>10, at most ten residue
  classes are forbidden, counting the q form as well. The generic finite-field
  counting lemma is `exists_residue_avoiding_linear_forms`.
* `canonicalTestNormalizedSum_gt_one` proves

      x>=73  ==>  sum(a in A, x/(a*x+1))>1.

  This uses exact rational arithmetic at x=73 and termwise monotonicity.
* `canonicalTestForm_mem_parent` proves that when k>=2, q>=73 is prime, and
  a*q+1 is prime, the form belongs to the canonical parent finset. Since a<=72<q,
  all predecessor factors are <=q and a*q<q^2<=q^k.
* `canonicalParentReciprocalMass_gt_of_test_pattern` proves

      k>=2, q>=73, q prime, all a*q+1 prime
        ==> 1 < q*canonicalParentReciprocalMass k q.

* `eventual_canonical_contraction_forces_finite_test_patterns` proves that an
  eventual bound M_k(q)<=c/q on prime q, with k>=2 and c<1, forces the set of
  realizations of this ten-form prime pattern to be finite.

### Precise scope

The local admissibility theorem does NOT prove infinitude of the prime pattern.
No prime-tuple conjecture is used as an axiom or hypothesis of the audit.
Consequently the pointwise contraction itself has NOT been unconditionally
refuted. Its implied finiteness of an admissible pattern explains why it is
not a harmless counting improvement: the usual prime-pattern prediction would
oppose it. An averaged estimate could allow these exceptional q, but no needed
averaged estimate was established here.

This is a test of a proposed auxiliary estimate, NOT a disproof of the original
conjecture and NOT a new unconditional multiplicity exponent.

### Verification and state

The complete source and fresh olean compile cleanly. The corresponding
`CanonicalParentMassTestCheck.lean` checks all theorem types and axiom lists;
only `propext`, `Classical.choice`, and `Quot.sound` occur. There is no `sorry`,
`admit`, or new axiom in the file. The temporary `CanonicalMassProbe.lean` was
removed. No unfinished auxiliary proof remains from this continuation.

A Lean elaboration pitfall encountered here: always type the image binder
explicitly in `S.image (fun a : Nat => -(a : ZMod ell)^(-1))` (with inverse
notation in the actual source). An untyped binder caused Lean to coerce the
whole finset into ZMod before imaging, leading to a type mismatch and very slow
reduction on the concrete finset. The final proof uses the explicit Nat binder.

`Submission/Spec.lean` is unchanged with SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
It still contains the original `sorry`; no complete proof or disproof is ready,
and no submission tool was called.


## Fixed-cofactor prime pairs: unconditional Brun-type convergence

This continuation returned to the averaged arithmetic question after the
pointwise contraction test. The existing progression bounds do not provide
relative error control on an arbitrary power-sparse subset of prime moduli;
no such control was inferred from the absolute below-half estimates. Instead,
the existing two-prime sieve was used to remove a concrete bounded-cofactor
portion of the parent mass.

### `PrimePairReciprocals.lean`

Imports `Submission.CanonicalParentMassTest` and `Submission.Sieve`.

* `summable_reciprocal_of_summable_geometric_count` is a general converse
  geometric-counting criterion. If

      sum_L #{n<2^(t*L): n in S}/2^(t*L)

  converges, with t>=1, then the reciprocal series on S converges. No
  monotonicity of the indicator is required. The proof bounds reciprocal
  mass on successive geometric blocks and then all finite partial sums.

* `pair_sieve_normalized_error` proves that the explicit sieve error, divided
  by 2^(128*m), is at most 3*(1/2)^m.

* `prime_pair_normalized_count` applies
  `Sieve.prime_pair_explicit_bound` at N=2^(128*m), sieve parameter m>0:

      #{q<N : q prime, a*q+1 prime}/N
        <= C(a)/m^2 + 3*(1/2)^m,

  where

      C(a) = 2 / ((totient(2*a)/(2*a) * log 2)^2).

* `summable_prime_pair_reciprocal` proves, unconditionally for every fixed a>0,

      Summable ({q : q prime and a*q+1 prime}.indicator (1/q)).

* `summable_canonical_test_pattern_reciprocal` specializes this to the
  ten-form admissible pattern of `CanonicalParentMassTest.lean`, using only
  its q and 2*q+1 forms. Its reciprocal series converges. This assertion is
  compatible with either finiteness or infinitude of the pattern.

* `primePairParentSet a` is the image of the prime-pair set under q |-> a*q+1.
  `summable_prime_pair_parent_reciprocal` transfers convergence to these
  larger primes, using injectivity and 1/(a*q+1)<=1/q for prime q.

* `boundedCofactorParentSet A` is the union of those parent sets for 1<=a<=A.
  `summable_bounded_cofactor_parent_reciprocal` proves convergence for every
  fixed finite A. The proof uses finite summation, not a claim about arbitrary
  countable unions.

* `bounded_canonical_parent_mem` places a canonical parent p of a prime q
  with p<=A*q+1 in that bounded-cofactor set, by the exact quotient
  a=(p-1)/q.

* `summable_bounded_canonical_parent_reciprocal` proves convergence on all
  such canonical parents for every k and every fixed A.

### What remains

The fixed-cofactor contribution is now rigorously negligible for reciprocal
mass, so the previous admissible-pattern test does not by itself block a
suitable averaged contraction. However, no required estimate for the rest
of the canonical parent mass was proved. In particular, the constants and
summable tails here are not uniform enough to replace the fixed bound A by
the full range of cofactors up to q^(k-1). The union as A tends to infinity
need not have a convergent reciprocal series.

No growing-cofactor cutoff theorem, arbitrary-root smooth-prime estimate,
new unconditional multiplicity exponent, or contradiction to the hypothetical
negation was obtained in this continuation.

### Verification and state

The source and its current olean compile cleanly. `PrimePairReciprocalsCheck.lean`
checks all principal theorem types and axioms. All depend only on `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, or new axiom occurs
in the file. The temporary `BrunProbe.lean` was removed; no unfinished auxiliary
proof remains from this continuation.

Two elaboration details: when comparing a finset cardinality from the sieve
file to a set-indicator version, an explicit `Finset.ext` equality avoids
mismatched decidable instances inside `linarith`. Also,
`Function.Injective.summable_iff` is easiest to apply after separately naming
the proof that the function vanishes off the map's range, avoiding unexpected
metavariable-goal ordering.

`Submission/Spec.lean` remains unchanged, with SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The original `sorry` remains. No valid final proof or disproof is ready for
submission, and no submission tool was called.


## Uniform growing-cofactor estimate from the averaged two-prime sieve

This continuation replaced the fixed finite cofactor range by an explicit
unbounded cutoff, using the harmonic weight retained in
`Sieve.sum_prime_pair_explicit_bound`.

### `GrowingCofactorReciprocals.lean`

Imports only `Submission.PrimePairReciprocals`.

Definitions:

    rootLogCofactorCutoff R p = 2^(R*Nat.sqrt(Nat.log 2 p))
    rootLogCofactorParentSet R =
      {p : p in boundedCofactorParentSet (rootLogCofactorCutoff R p)}.

Thus membership means p=a*q+1 with q and p prime, a positive, and
 a<=rootLogCofactorCutoff R p.

Principal finite estimates:

* `bounded_cofactor_parent_count_le_pairs` bounds parents p<N with a<=A by
  the summed prime-pair counts with q<=N/a. This is a finite covering bound;
  overlapping representations are allowed on the upper-bound side.
* `cofactor_sieve_normalized_error` controls the error even when A<=2^m:

      A*(2^(64m)+2^(16m)+1)/2^(128m) <= 3*(1/2)^m.

* `bounded_cofactor_parent_normalized_count` gives

      count/2^(128m)
        <= cofactorSieveConstant*harmonic(A)/m^2 + 3*(1/2)^m,

  where `cofactorSieveConstant = 16*Sieve.totientRatioAverageConstant/(log 2)^2`.
* `rootLogCofactorCutoff_mono` and `rootLogCofactorParent_count_le` dominate
  the varying cutoff inside a geometric block by

      A_m = 2^(R*Nat.sqrt(128*m)).

* `rootLog_block_cutoff_le` proves A_m<=2^m once m>=128*R^2.
* `harmonic_rootLog_block_le` proves

      harmonic(A_m) <= (1+16R)*sqrt(m),

  for m>=1, using the logarithmic harmonic bound and the integer-square-root
  inequality. There is no assumed smooth-prime distribution in this estimate.
* `rootLog_cofactor_normalized_count` consequently yields

      count/2^(128m)
        <= cofactorSieveConstant*(1+16R)*m^(-3/2) + 3*(1/2)^m

  at those scales. Both majorant series converge.

Main conclusions:

* `summable_rootLog_cofactor_parent_reciprocal`: for every fixed R, the
  reciprocal series on `rootLogCofactorParentSet R` converges. This follows
  from the previously proved geometric counting criterion and eventual
  comparison with the p-series/geometric majorant.
* `not_summable_reciprocal_outside_rootLog_cofactor_parents`: the complementary
  prime set retains reciprocal divergence.
* `prime_outside_rootLog_cofactor_parent_iff`: for prime p, nonmembership is
  exactly

      for every q in (p-1).primeFactors,
        rootLogCofactorCutoff R p * q < p-1.

* `not_summable_rootLog_prime_factor_bound` states the corresponding reciprocal
  divergence directly with that arithmetic factor condition.

### Scope and unchanged main gap

This is genuinely uniform over a growing range of cofactors, not a countable
union of fixed-cofactor summability statements. Nevertheless, for each FIXED
R its cutoff is only exp(O_R(sqrt(log p))). The resulting largest-factor bound
is near p, not p^(1/k) for arbitrary fixed k. Increasing R does not change this
asymptotic distinction: the relevant thresholds depend on R and the theorem
keeps R fixed before p tends to infinity. No diagonal choice converting it to
arbitrary-root smoothness was justified.

In particular, this does not improve the strongest unconditional inverse-totient
multiplicity exponent. The needed contribution from the remaining, much larger
cofactors is still uncontrolled. No contradiction to the exact negation of the
conjecture and no proof of that negation were obtained.

### Verification and state

The complete source, fresh olean, and `GrowingCofactorReciprocalsCheck.lean`
compile cleanly. All audited theorem dependencies are among `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, or new axiom occurs
in the file. `GrowingCofactorProbe.lean` was removed. No unfinished auxiliary
proof remains from this continuation.

Useful APIs confirmed here: `Nat.sqrt_le' n : (Nat.sqrt n)^2<=n`,
`Nat.sqrt_le_sqrt`, `Nat.pow_le_pow_iff_left`, and
`Summable.of_norm_bounded_eventually_nat`. When extracting an image witness,
`change a*q+1=p at heq` may be needed before `omega` can use its equality.

`Submission/Spec.lean` remains unchanged with SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
It retains the original `sorry`. No valid final proof or disproof is ready
for submission, and no submission tool was called.

## Review of threshold optimization and record-fiber amplification

The latest continuation rechecked two possible ways of combining existing
quantitative results. No additional Lean theorem was obtained.

* `exists_uniform_quadratic_rankin_threshold` requires n>=2^(C*k^2) to give
  a saving 2^k. Thus k can grow only on the order of sqrt(log n) within this
  theorem. Choosing k on the order of epsilon*log n, as a fixed-power upper
  saving would require, violates the threshold for large n. The existing
  `exists_sqrt_log_upper_bound` already records the valid consequence.
* The normalized-record pair estimates in `RecordPairs.lean` give UPPER
  bounds for pairs with large common divisors. LCM-based amplification would
  need a sufficiently large family of such pairs, hence a suitable LOWER
  bound. The supplied upper bounds do not give it. Combining many low-overlap
  inputs without an additional gain in output size does not improve the
  multiplicity exponent.

These are confirmations of previously documented limitations, not new
obstructions or new positive results. The review did not justify an inference
from subpower savings to fixed-power savings, a reversal of an overlap bound,
or a diagonal choice in the growing-cofactor theorem.

No Lean source was changed in this review. `Submission/Spec.lean` remains
unchanged with its original `sorry`; no complete proof or disproof is ready.

## Review of a many-predecessor-factors route

The next continuation checked whether a large number of prime factors of p-1
could force enough of its logarithmic mass into small factors to bypass the
higher-root smoothness gap. No new analytic estimate or Lean theorem was
obtained.

The existing `StructuredPrimeFactors.lean` theorem supplies r distinct factors
in its prime block at scale X=2^(64*t*m), under 2*r+1<=t. Its guaranteed divisor
mass has exponent r/t<1/2. The resulting smoothness estimate remains
(t-r)/t>1/2, before the already established fixed second-sieve improvement.
Increasing r within this permitted parameter range does not make the controlled
divisor consume a fraction tending to one of log X.

A factor count without a matching lower bound for the product of suitably
small factors does not exclude a large residual prime factor. No normal-order
or extreme-factor-count assertion was treated as supplying the missing prime
density bound. This review confirms the previously recorded parameter gap; it
is not new progress toward the final conjecture and is not a disproof.

No Lean source was changed. `Submission/Spec.lean` retains its original `sorry`,
and no complete proof or disproof is ready for submission.

## Direct signed-aggregate review (no new theorem)

The latest continuation inspected `geometricSmoothModulusDeficit` directly,
without replacing it by the absolute progression error. Its actual-count term
is a progression sum over `primeProductModuli (t-2) m`. Exchanging the prime
and modulus sums, and using `prime_product_divisor_count_eq_choose`, makes
this the order-(t-2) binomial moment of the number of block-prime divisors
of p-1.

The existing unconditional distribution theorem has the parameter constraint
2*r+1 <= t. Substituting r=t-2 satisfies this only when t<=3; it does not give
the cofinal t required by `CofinalSmoothModulusCondition`. The existing
`ProductMomentModels.lean` results also preclude deducing a positive next
moment solely from the known initial moments and their nonnegativity.
These abstract models are not counterexamples to the arithmetic conjecture.

No new signed-average lower bound was established. In particular, neither
local signed-kernel positivity nor unrestricted divisor switching was assumed.
This review confirms a previously identified gap, rather than proving that
no possible direct signed-average argument can work.

No Lean source was changed. `Submission/Spec.lean` still contains its original
`sorry`; its SHA-256 remains
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
There is no complete proof or disproof ready for submission.

## Cross-scale factor-moment review (no new theorem)

The next continuation examined whether simultaneous factor-size information
across finer logarithmic blocks could close the gap left by a fixed-block
factorial moment. The existing half-level partition certificate already
incorporates exact total size and the tested joint moments across all its
finite blocks. It is not an asymptotic model and does not rule out every
possible all-scale inference.

No stronger prime constraint was obtained from refinement. The available
arithmetic distribution input still restricts the product of selected factors
to the below-half modulus range. Merely using more or finer blocks does not
extend that product range to X^(1-delta) for arbitrarily small delta. Neither
an asymptotic uniqueness theorem for the factor-size distribution nor a new
high-product-mass lower bound was proved.

No new Lean theorem or improvement of the multiplicity exponent resulted.
`Submission/Spec.lean` is unchanged and still contains its original `sorry`.
The full conjecture remains unproved and undisproved in this workspace.

## Inverse-totient Dirichlet moments and the off-diagonal collision criterion

A subsequent continuation developed a different exact analytic formulation in
`Submission/InverseTotientMoments.lean`, importing only `Submission.Work`.
The new file and its `InverseTotientMomentsCheck.lean` audit compile cleanly;
the source has a fresh olean. Every audited theorem uses only `propext`,
`Classical.choice`, and `Quot.sound`. No original conjecture theorem is used.

### Unconditional first-moment results

* `summable_totient_neg_rpow`: for u>1, sum_m totient(m)^(-u) converges.
  This uses the existing uniform elementary input bound
  m^k <= ((2^(k+1))!)^k * totient(m)^(k+1), choosing k so that k*u/(k+1)>1.
* `totient_fiber_tsum` and `summable_totient_weight_iff` rigorously regroup
  any nonnegative weighted sum by its finite totient fibers.
* `summable_totient_neg_rpow_iff` and
  `summable_inverse_totient_first_moment_iff` give the exact threshold:

      Summable (fun n => (g n : R) * n^(-u))  <->  1<u.

### Exact second-moment reformulations

* `summable_inverse_totient_second_moment_of_power_bound`: if eventually
  g(n)<=n^beta and 1+beta<2*s, then sum_n g(n)^2*n^(-2*s) converges. This
  follows by domination by the first moment at exponent 2*s-beta>1.
* `not_summable_second_moment_of_infinite_power_exceedance`: infinitely
  many g(n)>n^s prevent the second-moment summands from tending to zero.
* `erdos_821_iff_second_moment_divergence` is an exact equivalence:

      original conjecture
        <-> forall s<1, not Summable (fun n => g(n)^2*n^(-2*s)).

  For the converse, a hypothetical eventual bound g(n)<=n^(1-epsilon)
  makes the second moment converge at s=1-epsilon/4<1.

### Collision interpretation and remaining gap

* `totient_collision_card` identifies g(n)^2 with the full ordered pair count.
* `totient_distinct_collision_card` identifies g(n)*(g(n)-1) with the
  cardinality of `offDiag` of the full finite totient fiber. Thus this is a
  genuine nonnegative collision count, not a signed analytic surrogate.
* `half_lt_of_summable_inverse_totient_second_moment` proves the diagonal
  contribution forces divergence for s<=1/2.
* `summable_second_moment_iff_off_diagonal` shows that for s>1/2 the diagonal
  contribution is summable, so convergence is equivalent to convergence of
  sum_n g(n)*(g(n)-1)*n^(-2*s).
* `erdos_821_iff_off_diagonal_divergence` therefore gives:

      original conjecture
        <-> forall 1/2<s<1,
              not Summable (fun n => g(n)*(g(n)-1)*n^(-2*s)).

The off-diagonal divergence is NOT proved. These equivalences and the exact
first-moment threshold do not improve the strongest existing multiplicity
exponent and do not settle Erdős 821. No collision lower bound sufficient for
all s<1 was obtained. Diagonal counting, or finitely many fixed collision
identities, must not be treated as supplying that missing bound.

The temporary `MomentProbe.lean` was removed; no auxiliary proof is pending.
`Submission/Spec.lean` remains unchanged with its original `sorry` and SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
There is still no complete proof or disproof ready for submission.

## Endpoint convergence of all logarithmically weighted collision moments

New file: `Submission/InverseTotientMomentEndpoint.lean`, importing
`Submission.InverseTotientMoments` and `Submission.Rankin`. It compiles cleanly
and has a fresh olean. `InverseTotientMomentEndpointCheck.lean` audits the
principal types and confirms only the three permitted axioms.

### Unconditional estimates proved

* `sum_reciprocal_totient_le_harmonic`:

      sum_{1<=m<=A} 1/totient(m)
        <= Sieve.totientRatioAverageConstant * harmonic(A).

  This follows directly from the existing harmonic average of
  (m/totient(m))^2, since m/totient(m)>=1 for positive m.

* `totient_ge_two_pow_of_input_ge`: for j>=3, m>=2^(4*j) implies
  totient(m)>=2^j. The elementary input bound at k=1 gives
  m<=24*totient(m)^2.

* `harmonic_fourfold_block_upper`:
  harmonic(2^(4*(j+1))) <= 10*j for j>=1.

* `summable_of_summable_geometric_blocks`: grouping a nonnegative series
  into [2^(t*j),2^(t*(j+1))) is valid without monotonicity of its terms.

* `eventually_weighted_g_le_div_log_cube`: for each natural R, eventually

      g(n)*(Nat.log 2 n)^R
        <= (4*C+4)*n/(Nat.log 2 n)^3,

  where C is the totient-ratio average constant. This uses the already
  established pointwise Rankin estimate with logarithmic exponent R+3.

* `summable_weighted_g_at_totient`: regrouped input weights

      g(totient(m))*(Nat.log 2 (totient(m)))^R/totient(m)^2

  are summable. On the input block [2^(4*j),2^(4*(j+1))), for all sufficiently
  large j, the block sum is bounded by 10*(4*C+4)*C/j^2.

* `summable_inverse_totient_endpoint_log_moment`: regrouping by the finite
  totient fibers gives, for EVERY natural R,

      Summable (fun n => g(n)^2*(Nat.log 2 n)^R/n^2).

* `summable_inverse_totient_second_moment_endpoint` gives the unweighted
  endpoint s=1 in the exact rpow notation of the prior collision criterion.

### Scope

These are unconditional endpoint upper bounds, not a settlement or a new
multiplicity lower exponent. They remain compatible with divergence at EVERY
s<1. Finiteness of all fixed logarithmically weighted endpoint moments must
not be extrapolated to a fixed power-weight improvement or to analytic
continuation of the collision Dirichlet series past its convergence boundary.
No sufficient lower bound for the subcritical off-diagonal series was proved.

No temporary probe or unfinished proof remains. `Spec.lean` is unchanged and
still contains its original `sorry`; its SHA-256 remains
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof or disproof is ready for submission.

## First-moment Euler-product investigation (informal; no new theorem)

The latest continuation examined the multiplicative input series behind the
first-moment identity. For real u>1, its expected standard Euler-product form is

  sum_n g(n)*n^(-u)
    = product_p (1 + (p-1)^(-u)/(1-p^(-u)))
    = zeta(u) * product_p (1 + (p-1)^(-u) - p^(-u)).

This formula was used only as an informal analytic direction; it was NOT
added as an axiom or claimed as a newly formalized theorem. Squaring the
coefficients does not square this Euler product: the second moment instead
imposes equality between products of distinct predecessor factors. No
estimate controlling those off-diagonal relations for every s<1 was obtained.
Neither first-moment analytic continuation nor the verified endpoint
logarithmic moment bounds were assumed to imply convergence or divergence
at a fixed subcritical exponent.

No Lean source was changed in this review. The conjecture in Spec.lean
remains unchanged and contains its original sorry. No complete submission
is available.

## Uniform fixed-power obstruction for the full Rankin majorant

New file: `Submission/RankinEnvelopeBarrier.lean`, importing only
`Submission.Rankin`. The file and `RankinEnvelopeBarrierCheck.lean` compile
cleanly; the main source has a fresh olean. All audited declarations depend
only on `propext`, `Classical.choice`, and `Quot.sound`.

This strengthens the earlier review of the quadratic-threshold specialization:
it treats ALL parameter choices in the underlying upper-bound expression,
including arbitrary dependence of those parameters on n.

Namespace: `Erdos821.RankinEnvelope`.

* `smooth_constant_ge_one`: for s>0 and u>1,
  smoothRankinConstant(s,u)>=1, using the term a=1 in its convergent p-series.

* `envelope_ge_power`: for real n,A,y,C,D>=1, s>0, u>1, delta>0, and
  log(n)<=n^(2*delta^2),

    n^(1-delta) <= (C/A+3*A/y)*n + (A*n)^s*exp(D*y^(u-s)).

  If the first two positive terms were both below the target, they would
  force A>n^delta and y>n^(2*delta). If s>=1-delta the power factor already
  exceeds the target. Otherwise u-s>delta, forcing the exponential factor
  to be at least exp(n^(2*delta^2))>=n. This proves the lower bound on the
  envelope, NOT on g.

* `majorant` is exactly the right-hand side of
  `Erdos821.g_le_linear_coeff_rankin`.

* `eventually_majorant_ge_power`: for every delta>0, eventually in n,
  the majorant is >=n^(1-delta) for ALL positive natural A,y and real s>0,u>1.
  The threshold is independent of A,y,s,u. The bound even omits the s<=u
  restriction imposed in the original upper-bound theorem.

* `eventually_majorant_gt_power`: applying the preceding result at delta/2
  gives a STRICT >n^(1-delta) bound, uniformly in all those parameters.

### Scope

This rigorously rules out obtaining a fixed-power upper saving solely by
optimizing this particular Rankin majorant. It is NOT a fixed-power lower
bound on g, a proof of the conjecture, a disproof, or a barrier to every
possible sharper Rankin-style estimate. An upper estimate on g being too
large cannot be reversed to a lower estimate on g.

No improvement of the multiplicity exponent or subcritical collision lower
bound was obtained. `RankinBarrierProbe.lean` was removed. No auxiliary proof
is unfinished. `Submission/Spec.lean` remains unchanged with its original
sorry and SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
The original conjecture remains unproved and undisproved.

## Primitive squarefree collisions: removing every common input factor

New files:

* `Submission/PrimitiveTotientCollisions.lean` (289 lines)
* `Submission/PrimitiveCollisionLowerBound.lean` (54 lines)

Both compile cleanly and have fresh oleans. The corresponding `...Check.lean`
files audit all main declarations; every audited theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound`. No original conjecture theorem
is imported or used. The temporary `PrimitiveCollisionProbe.lean` was removed.

Namespace: `Erdos821.PrimitiveCollisions`.

### Exact removal of common divisors

`Collision` is the type of ordered squarefree pairs (a,b) with phi(a)=phi(b).
`Primitive` is its subtype with gcd(a,b)=1. `Distinct` additionally requires
a!=b.

* `primitivePart` divides both inputs by their gcd. Squarefreeness makes the
  gcd coprime to each quotient, so totient multiplicativity and cancellation
  prove that the quotients still have equal totient.
* `split_injective`: the gcd together with the primitive pair reconstructs
  the original pair uniquely.
* `weight_split`: the weight phi(a)^(-2s) factors as
  phi(gcd(a,b))^(-2s) times the weight of the primitive pair.
* `summable_collision_iff_primitive`: for s>1/2, the complete squarefree
  collision series converges iff its primitive subseries converges. The
  unrestricted sum over possible common divisors is bounded by the known
  convergent input series sum_d phi(d)^(-2s).
* `collision_tsum_le` and `primitive_tsum_le` give the quantitative bounds

      primitive_sum <= collision_sum
          <= (sum_d phi(d)^(-2s)) * primitive_sum,

  with the required summability hypotheses. The upper comparison is not
  asserted as an equality: arbitrary common divisors may fail the needed
  coprimality or squarefreeness conditions.
* `fiberEquiv`, `fiber_card`, and `fiber_tsum` regroup squarefree collision
  pairs by their common output, giving the exact second moment gSquarefree^2.
* The only diagonal primitive pair is (1,1), so removing it does not affect
  convergence (`summable_primitive_iff_distinct`).

The main exact criterion is

  `erdos_821_iff_distinct_primitive_divergence`:

      original_conjecture <->
        forall s, 1/2<s -> s<1 ->
          not Summable (fun p : Distinct => phi(p.first)^(-2s)).

The required divergence for every such s is NOT proved.

### Unconditional arithmetic range transferred

`not_summable_distinct_of_infinite_g_gt` transfers any attained exponent
s+delta, with delta>0 and s>1/2, to nonsummability of the distinct primitive
series at s, using the previously verified squarefree reduction.

`not_summable_distinct_composite_range` applies this to the existing fixed
threshold:

    1/2 < s < 1/2 + 1/(80000000*Sieve.totientRatioAverageConstant+10).

`infinite_distinct_primitive_collisions` follows: there are infinitely many
ordered pairs of distinct, coprime, squarefree numbers with equal totient.

### Scope and current state

This identifies exactly which collision pairs must supply the missing
subcritical divergence. Multiplying known pairs by common squarefree factors
cannot by itself create new divergence above one half; their contribution
is bounded by a convergent factor. The unconditional transfer preserves the
previous fixed exponent and does NOT improve it toward one. No proof of the
full primitive divergence criterion, and no disproof of the conjecture, was
obtained.

No auxiliary proof is unfinished. `Submission/Spec.lean` is unchanged and
still contains its original `sorry`. SHA-256:
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No valid complete submission exists; the original conjecture remains
unproved and undisproved.

## Finite prime excision and primitive relations on fresh input supports

New files:

* `Submission/PrimeExcision.lean` (186 lines)
* `Submission/PrimeExcisionApplications.lean` (87 lines)

Both compile cleanly and have fresh oleans. Their `...Check.lean` files audit
all main results; only `propext`, `Classical.choice`, and `Quot.sound` occur.
The temporary `PrimeExcisionProbe.lean` was removed.

### Quantitative finite excision

`gAvoiding K n` counts squarefree preimages of n that are coprime to K.
For K>0, split a squarefree fiber by d=gcd(m,K), then divide its inputs by d.
Squarefreeness makes m/d coprime to K, and its totient is n/phi(d).

* `card_gcd_class_le_gAvoiding` injects a single gcd class into that smaller
  restricted fiber.
* `gSquarefree_le_sum_gAvoiding` proves the unconditional finite inequality

      gSquarefree(n) <= sum_{d|K} gAvoiding(K,n/phi(d)).

* `exists_reduced_gAvoiding` gives m<=n with

      gSquarefree(n) <= tau(K)*gAvoiding(K,m).

* `exists_gAvoiding_gt_of_divisor_count` is uniform at the finite input scale:
  if K,n>0, tau(K)<=n^beta and gSquarefree(n)>n^(alpha+beta), it supplies m<=n
  with gAvoiding(K,m)>n^alpha. Here K MAY depend on the input scale; the
  divisor-count hypothesis is explicit.
* `infinite_gAvoiding_of_infinite_gSquarefree` and
  `infinite_gAvoiding_of_infinite_g` preserve an attained positive exponent
  after excluding any FIXED K, with an arbitrarily small positive exponent
  loss. The output remains squarefree. No uniform threshold in K is asserted
  by these infinitude theorems.
* `erdos_821_iff_avoiding_inputs`: for each fixed K>0, the full conjecture is
  equivalent to its squarefree, K-coprime input version. Neither side is
  established unconditionally.

### Unconditional applications

`infinite_gAvoiding_composite_range` transfers the existing fixed threshold

    0 < gamma < 1/2 + 1/(80000000*Sieve.totientRatioAverageConstant+10)

to every fixed K>0.

`exists_primitive_avoiding_of_one_lt` takes two distinct members of a
restricted fiber and removes their gcd. The resulting inputs remain distinct
and coprime to K, are squarefree, are coprime to one another, and have equal
totient.

`exists_distinct_primitive_avoiding`: such a pair exists outside every fixed
finite input-prime support.

`exists_primitive_with_large_prime_factors`: for every B, there is a
`PrimitiveCollisions.Distinct` pair such that EVERY prime factor of EITHER
input exceeds B. This applies the previous result with K=B!.

### Amplification investigation and scope

Finite prime exclusion therefore does NOT prevent constructing collision
relations on fresh supports. However, these existence theorems provide no
upper bound on the new output scale relative to the excluded support.
Tensoring disjoint high-multiplicity blocks supplies the bound

    product_i n_i^alpha = (product_i n_i)^alpha,

which preserves alpha rather than increasing it. A binary choice from each
primitive pair supplies only one bit per pair; infinitude of fresh pairs is
not a quantitative near-linear multiplicity estimate. No justified additional
cross-output collision gain was found. This discussion is not claimed as a
barrier to all possible uses of prime-excluded families.

The attained exponent is unchanged. Neither arbitrary-root shifted-prime
counting, the cofinal smooth-modulus deficit estimate, nor primitive collision
divergence for every s<1 was proved.

No auxiliary proof is unfinished. `Submission/Spec.lean` remains unchanged
with its original `sorry`, SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
There is no complete proof or disproof ready for submission.

## Prime-producing families review (no new theorem)

Investigated a route through linear prime-producing families and balanced
products, rather than further collision tensoring.

For forms p=Q(t+a_i)+1, with Q smooth and t+a_i of size T, put X approximately
Q*T. To force all predecessor factors below X^(1/k) by the cofactor size
alone requires T <= X^(1/k), hence Q >= X^(1-1/k), or equivalently a prime
output at scale at most Q^(k/(k-1)). The exponent k/(k-1) tends to one.

Fixed-modulus Dirichlet infinitude, or a fixed-tuple prime-existence theorem
without uniform control of its threshold as Q grows, does not supply this
range. No such uniform estimate was obtained here. No bounded-gaps theorem
was added as an axiom or assumed to imply the needed growing-modulus result.

Counting also matters. One prime for each of sufficiently many such moduli
would not by itself give the strongest near-full counting exponent at a
fixed root k. It COULD nevertheless be sufficient cofinally in k if the
number of moduli has exponent 1-1/k and prime-output overlaps are controlled:
the generic multiplicity transfer would then approach exponent 1 as k grows.
Thus this review is NOT a claim that many primes per modulus are necessary
for every possible cofinal construction. The missing uniform prime supply
and overlap control were not proved.

The alternative p=product_i t_i+1 with all factors in balanced short ranges
would directly produce smooth predecessors. Enough prime values in those
boxes is itself an unproved arithmetic input in this development; ordinary
prime infinitude or primality of some divisor of a polynomial value does not
establish it. No sufficient new lower estimate was derived.

No Lean source was changed and no auxiliary proof is unfinished.
`Submission/Spec.lean` still contains its original sorry and remains at hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
The original conjecture is still unproved and undisproved; no complete
submission is ready.

## Finite prime-factor energy expansion review (no new theorem)

Investigated whether adding input primes one at a time supplies an
exponent-improving lower bound for the collision moment.

Informally let c_P(n) count squarefree inputs supported on a finite prime set
P with totient n, and let

    E_P(s) = sum_{n>=1} c_P(n)^2*n^(-2s).

For a new prime p and a=p-1, expansion of the finite coefficient sequence
c_{P union {p}} = c_P + the multiplicative shift of c_P by a gives

    E_{P union {p}}(s)
      = (1+a^(-2s))*E_P(s)
        + 2*a^(-2s)*sum_{m>=1} c_P(a*m)*c_P(m)*m^(-2s).

This finite identity was examined informally; no new Lean theorem for it was
added. It is NOT a coefficientwise square of the first-moment Euler product.
Discarding the nonnegative correlation term yields only the diagonal product
product_p (1+(p-1)^(-2s)), whose convergence above s=1/2 supplies no needed
subcritical divergence. No sufficient lower estimate for the scaled
correlations was obtained. Their positivity alone does not imply that their
sum diverges.

Additional analytic-continuation/phase-alignment ideas did not produce a
justified inference from first-moment behavior to the required second moment.
No exponent improvement, proof, or disproof was obtained in this review.

No Lean source changed and no auxiliary proof is pending. Spec remains
unchanged with its original sorry and SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete submission is ready.

## Shared-cofactor prime-tuple extension review (no new theorem)

Tested a different use of prime-producing forms: for d|A, if p=d*t+1 is
prime and phi(m)=A/d with p not dividing m, then

    phi(p*m) = (p-1)*phi(m) = A*t.

This could add preimages from many different cofactor fibers into one output
fiber. However, even with every candidate form prime and all distinctness
conditions favorable, the number supplied is at most

    sum_{d|A} g(A/d).

Under a global bound g(u)<=C*u^beta with beta>=0, this is at most
C*A^beta*tau(A). Since tau(A) is subpower, this SINGLE new-prime construction
cannot by itself turn beta into a strictly larger fixed exponent at output
A*t. An eventual power bound can be made global by enlarging C to cover the
finitely many positive small outputs. The argument concerns the supplied
construction, not a new upper bound on the whole totient fiber.

No quantitative multi-prime construction overcoming this loss was obtained.
In particular no claim is made that this rules out every use of prime tuples
or a number of new factors growing with the output. No bounded-gaps or
prime-tuple assertion was imported as an axiom. This review was informal and
added no Lean theorem.

The original conjecture remains unproved and undisproved. No Lean source
changed; no auxiliary proof is pending. Spec still contains its original
sorry and has SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete submission is ready.

## Totient injectivity on powerful inputs and first-power support

New file: `Submission/PowerfulTotient.lean` (172 lines), importing only
`Submission.SquarefreeInput`. It compiles cleanly and has a fresh olean.
`PowerfulTotientCheck.lean` audits the main declarations: only `propext`,
`Classical.choice`, and `Quot.sound` occur. `PowerfulProbe.lean` was removed.

This arose from testing whether prime-power atoms, whose totients are smooth
relative to their input size, bypass the need for ordinary shifted primes.
The stronger structural conclusion is that powerful inputs cannot collide.

### Main arithmetic argument

`PowerfulInput a` means every p in a.primeFactors satisfies p^2 | a. At zero
this definition is vacuous; zero is handled separately using phi(a)=0 iff
a=0, so that convention causes no issue.

* `totient_collision_support_identity` cancels predecessor factors belonging
  to common input primes. Writing P=primeFactors(a), Q=primeFactors(b), a
  collision phi(a)=phi(b) gives

      a * product_{q in P\Q}(q-1) * rad(b)
        = b * product_{q in Q\P}(q-1) * rad(a).

* `not_sq_dvd_of_largest_support_difference`: if p belongs to P\Q and is at
  least every prime in Q\P, then p^2 cannot divide a. Otherwise the displayed
  identity and coprimality with b*product_{q in Q\P}(q-1) force p^2 | rad(a),
  contradicting squarefreeness of the radical.
* `eq_of_totient_eq_of_powerful_differences`: it suffices that the primes in
  each DIFFERING support occur at least twice on their own side. A maximum of
  the symmetric difference rules out unequal supports; the previously proved
  fixed-support injectivity then identifies the inputs.

### Verified consequences

* `totient_injective_on_powerful`: totient is injective on powerful inputs.
* `powerful_totient_fiber_card_le_one`: every totient fiber has at most one
  powerful member.
* `powerfulInput_pow`: every kth power with k>=2 is powerful.
* `totient_pow_injective`: for every k>=2, a |-> phi(a^k) is injective.
* `firstPowerSupport a` consists of input prime factors p with p^2 not dividing
  a, equivalently the primes occurring exactly once when a>0.
* `firstPowerSupport_injOn_totient_fiber`: within every fixed totient fiber,
  this FIRST-POWER support determines the input. This strengthens the earlier
  injectivity of the full radical/prime-support map.

### Scope and unchanged main gap

Thus restricting the construction entirely to kth powers, or even arbitrary
powerful inputs, produces no distinct equal-totient inputs. Varying exponents
on a fixed support is not a substitute for the missing supply of suitable
first-power primes. These structural theorems do NOT give a fixed-power upper
saving for the full g, improve the existing lower exponent, or settle the
original conjecture.

No auxiliary proof is unfinished. Spec remains unchanged with its original
sorry and SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof or disproof is ready for submission.

## Post-powerful-input continuation and bounded reference recheck

A single bounded request to https://www.erdosproblems.com/821 was attempted
after the much earlier network failures. It failed immediately with
`curl: (6) Could not resolve host: www.erdosproblems.com`. No updated status,
paper, or additional theorem was obtained. Do not repeat this request without
a genuine change in network availability.

Further analysis of first-power-support injectivity did not provide a new
counting lower bound. Unique reconstruction from the first-power support
controls the encoding of a fiber, not how many admissible supports occur.
It supplies neither the missing shifted-prime density nor an exponent
amplification. No new Lean source or theorem was added in this continuation.

Spec remains unchanged with its original sorry and hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No auxiliary proof is pending and no complete proof/disproof is ready.

## Bounded first-power arity: completed and audited

`Submission/FirstPowerArity.lean` now compiles cleanly and has a fresh olean.
It imports only `Submission.PowerfulTotient`. The audit in
`FirstPowerArityCheck.lean` confirms only `propext`, `Classical.choice`, and
`Quot.sound` for its main declarations.

Let gFirstPowerAtMost(r,n) count inputs in the totient fiber at n with at most
r input primes occurring exactly once. Injectivity of firstPowerSupport on
that fiber and the bounded-subset-family estimate give, for positive n,

    gFirstPowerAtMost(r,n) <= (r+1)*(tau(n)+1)^r.

Thus for every FIXED r and every delta>0, this count is eventually at most
n^delta. No restrictions are imposed on higher prime-power factors.
The complementary count gFirstPowerAbove(r,n) partitions g(n) exactly.
For every fixed r and alpha>0, sufficiently large n with g(n)>n^alpha satisfy

    g(n) < 2*gFirstPowerAbove(r,n).

So most inputs of such a fiber have more than any prescribed fixed number
of first-power prime factors. The proof does not assert uniform thresholds
as r grows, a multiplicity lower-bound improvement, or shifted-prime density.
In particular it does not settle the original conjecture.

The earlier two proof errors (a base-at-least-one premise for power
monotonicity and a ring-associativity step) are repaired. The deprecated
filter-card lemma was replaced. No auxiliary proof remains pending.

Spec.lean is still unchanged, with its original sorry. Its SHA-256 remains
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof or disproof is ready for submission.

## Exact finite-support collision energy (latest continuation)

New file: `Submission/FiniteTotientEnergy.lean`, importing only
`Submission.PrimitiveTotientCollisions`. It compiles cleanly and has a fresh
olean. `FiniteTotientEnergyCheck.lean` audits the main results; only `propext`,
`Classical.choice`, and `Quot.sound` occur. `EnergyProbe.lean` was removed.

This formalizes the previously informal finite energy expansion, including
its exact connection to the unrestricted squarefree second moment. It does
NOT establish the missing cross-correlation growth.

Namespace: `Erdos821.FiniteEnergy`.

Definitions for a finite set P of input primes:

    output(S) = product_{p in S}(p-1),
    coefficient(P,n) = #{S subset P : output(S)=n},
    energy(P,s) = sum_{S,T subset P, output(S)=output(T)} output(S)^(-2s),
    correlation(P,d,s) =
      sum_{S,T subset P, output(S)=d*output(T)} output(T)^(-2s).

`output_eq_totient` identifies outputs with the totients of the squarefree
products of the selected primes. `energy_eq_coefficient_sum` and
`correlation_eq_coefficient_sum` prove the exact formulas

    E(P,s) = sum_n coefficient(P,n)^2*n^(-2s),
    C(P,d,s) = sum_n coefficient(P,n)*coefficient(P,d*n)*n^(-2s),

where each finite sum is over the image of output on P.powerset.

`energy_insert` proves, for p not in P and p>1, with a=p-1,

    E(P union {p},s) = (1+a^(-2s))*E(P,s) + 2*a^(-2s)*C(P,a,s).

The algebraic identity itself does not need primality; primality is required
for the connection to the actual squarefree totient fibers.

`coefficient_le_gSquarefree` gives the unrestricted fiber bound. Equality
holds when P covers the prime supports of every squarefree input in the
fiber (`coefficient_eq_gSquarefree_of_cover`). Every finite partial sum of
the unrestricted squarefree moment is dominated by some finite prime energy
(`exists_energy_ge_squarefree_partial_sum`). Consequently

    Summable(n |-> gSquarefree(n)^2*n^(-2s))
      iff exists C, forall finite prime sets P, E(P,s)<=C.

`erdos_821_iff_energy_unbounded` gives the exact original-conjecture criterion:

    forall s in (1/2,1), forall real C,
      exists finite prime set P with C<E(P,s).

The right side remains UNPROVED.

Discarding the cross terms gives

    product_{p in P}(1+(p-1)^(-2s)) <= E(P,s).

But for s>1/2, `diagonal_product_le_constant` bounds this product uniformly by

    exp(sum_{m>=0} phi(m)^(-2s)),

which is finite by the previously verified first-moment theorem. Thus the
diagonal lower bound is insufficient. No claim is made that positivity of
the cross terms alone forces energy divergence, nor that this identity
improves the existing multiplicity exponent.

No auxiliary proof remains pending. Spec.lean is unchanged with its original
sorry and SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
There is still no complete proof or disproof ready for submission.

## Disjoint finite-energy blocks: combination and quantitative gains

New file: `Submission/DisjointFiniteEnergy.lean`, importing only
`Submission.FiniteTotientEnergy`. It compiles cleanly with a fresh olean.
`DisjointFiniteEnergyCheck.lean` audits its main declarations; only the three
permitted axioms occur. The temporary `EnergyTensorProbe.lean` was removed.

Within `Erdos821.FiniteEnergy`:

* `sum_powerset_union_disjoint` gives the exact subset decomposition over
  disjoint supports. `kernel_mul_le` shows that two separate collisions
  contribute a collision on their union with the product weight.
* `energy_union_ge_mul` proves E(P,s)*E(Q,s)<=E(P union Q,s) when P and Q
  are disjoint. Extra cross-support relations may make this strict.
* `one_le_energy` and `energy_union_ge_add_sub_one` give E>=1 and the
  additive gain bound.
* `sum_disjoint_block_gains_le` proves, for any pairwise disjoint sequence
  of finite supports B_i and finite index set I,

      sum_{i in I}(E(B_i,s)-1) <= E(union_{i in I}B_i,s)-1.

* `summable_disjoint_block_gains` proves that convergence of the global
  squarefree second moment forces summability of the gains E(B_i,s)-1
  for EVERY pairwise disjoint sequence of finite PRIME supports.
* `not_summable_moment_of_disjoint_block_gains` is its contrapositive.
* `not_summable_moment_of_uniform_disjoint_gain` shows that a fixed positive
  gain delta on every block would suffice at that exponent. Such a sequence
  is not constructed for all s<1.

The actual singleton formula, for p>2, is

    E({p},s)-1 = (p-1)^(-2s) > 0.

`summable_singleton_prime_gains` verifies convergence of these gains over
all primes p>2 when s>1/2. This is an explicit example showing why positive
fresh-block gains alone are insufficient. It is not a statement about the
unknown total contribution of larger blocks with distinct colliding inputs.

No non-summable block-gain estimate beyond the earlier attained exponent
range has been found. The new finite combination inequalities do not by
themselves improve that exponent, prove the conjecture, or disprove it.

No auxiliary proof remains pending. Spec.lean is unchanged with its original
sorry and hash 8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No valid complete submission is ready.

## Prime-incidence rectangles and primitive semiprime collisions

New verified files (with fresh oleans):

- `PrimeRectangles.lean`
- `FixedArityMoments.lean`
- `PrimeRectanglesCheck.lean`
- `FixedArityMomentsCheck.lean`

The finite rectangle-free graph bound is proved over natural cardinalities:

```
E ⊆ A × B, no nondegenerate rectangle
  ⇒ |E|² ≤ |B| (|E| + |A|²).
```

A canonical factorization is chosen for each prime predecessor. This gives
an edge set whose labels `a*b+1` are injective, so a graph rectangle produces
four distinct primes. Its diagonal and off-diagonal products are coprime
squarefree semiprimes with the same totient.

The existing progression counts supply this edge set unconditionally. At
scale L the row and column ranges are `2^(30*L)` and `2^(35*L)`, while the
edge count is at least `2^(63*L)` and at most `2^(64*L)`. All prime edge labels
exceed `2^(63*L)`. The rectangle-free bound is then violated for every
sufficiently large L.

`exists_large_primitive_semiprime_collision K` supplies distinct squarefree
u,v > K with gcd(u,v)=1, equal totients, and exactly two distinct prime factors
on each side. `infinite_primitive_semiprime_outputs` proves infinitely many
common outputs with such pairs. This is stronger arity control than the
earlier qualitative primitive-pair theorem, but not a polynomial-size fiber.

The new limitation theorem is also verified:

```
s > 1/2 ⇒ Summable (fun n =>
  (gFirstPowerAtMost r n : ℝ)^2 * (n : ℝ)^(-(2*s)))
```

for every fixed natural r. It follows by combining the earlier subpower
fixed-arity bound with the unconditional first-moment convergence. Thus
fixed-arity collisions, including the new semiprime rectangles, cannot by
themselves provide the second-moment divergence needed for all s<1.

All audited declarations use only propext, Classical.choice, and Quot.sound.
There is no sorry in either new proof file. Spec.lean is unchanged, with its
original sorry and hash
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof or disproof is ready, and the unchanged file has not been
resubmitted.

## Finer half-scale partition experiment with a density cap (not a Lean theorem)

This continuation tested whether the size-12 moment obstruction disappears on
an appreciably finer grid. An abstract model on partitions of **24** was found
with 768 positive rational weights. An independent Python `Fraction` checker
verifies exactly:

* every outcome has total size 24 and a part at least 7, hence no outcome is
  fourth-root smooth;
* the weights sum to one;
* every joint binomial moment of selected total size at most 12 (including the
  half-size endpoint) equals the permutation reference value
  `1 / product(j^a_j * a_j!)`;
* all single-part means are `1/j`, including parts larger than 12;
* the weight of every partition is at most twice its reference weight
  `1 / product(j^C_j * C_j!)`.

The numerical LP was used only to find a support. Sage rational linear algebra
reconstructed exact weights. The independent checker rechecks all 284 moment
equations and the density cap with exact fractions. This experiment is **not
Lean-certified**, is not an asymptotic family, and is not a model or disproof
about actual primes. It provides no new unconditional multiplicity exponent.
The density cap additionally bounds all nonnegative statistics by twice their
reference means, but this observation is still confined to the finite model.

Development files:

* `Submission/Experiments/finer_partition_moments_cap2.py`
* `Submission/Experiments/finer_partition_cap2_certificate_24_4.json`
* `Submission/Experiments/check_finer_partition_certificate.py`

Run the independent check with:

    python3 Submission/Experiments/check_finer_partition_certificate.py

Correction from the following continuation: the size-36 rational
reconstruction had actually completed before shutdown. Its certificate was
recovered and independently checked; see the later section on finer and
beyond-half partition models. The density cap for that certificate is 100,
not 2. The size-24 cap-2 statement above is unchanged.

The original conjecture remains **unsolved**. `Submission/Spec.lean` is unchanged
with its original `sorry` and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete submission has been made in this continuation.

## Fixed iterates of totient: exact fibers and exponent-transfer limits

This continuation investigated iteration of totient as a possible amplification
route. It completed `Submission/IteratedTotientFibers.lean` (namespace
`Erdos821.IteratedTotient`) and the type/axiom audit
`Submission/IteratedTotientFibersCheck.lean`. Both compile cleanly. The proof file
has a built olean; all twelve audited declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.

Write `multiplicity k n` for the number of inputs whose k-th totient iterate is
n, and `fiber k n` for the corresponding finite set. Verified results include:

* `finite_fiber`, `multiplicity_zero`, `multiplicity_one` establish finiteness,
  g_0(n)=1, and g_1(n)=g(n).
* `multiplicity_succ` gives the **exact** disjoint-fiber recurrence

      g_(k+1)(n) = sum_{phi(m)=n} g_k(m).

* `eventually_input_le_rpow` and `eventually_iterated_input_le_rpow` show that,
  for every fixed k and epsilon>0, all inputs of a sufficiently large output n
  lie between n and n^(1+epsilon).
* `eventually_multiplicity_le_one_add` consequently gives the unconditional
  upper ceiling g_k(n)<=n^(1+epsilon), for each fixed k.
* `eventually_multiplicity_succ_le` transfers one-step upper exponent a and
  k-step upper exponent b to exponent a+b+epsilon for step k+1.
* `eventually_multiplicity_le_mul_exponent` proves that a hypothetical eventual
  bound g(n)<=n^a, a>=0, yields

      g_k(n) <= n^(k*a+epsilon)

  eventually. `finite_large_iterated_fibers_of_power_bound` records the
  corresponding finite-witness conclusion for any exponent b>k*a.
  **No invariance of the maximal multiplicity exponent under iteration has
  been proved.** A near-linear lower bound for g_k would not, through this
  argument alone, give a near-linear lower bound for g.

The file also defines `restrictedSecondMultiplicity P n`, the number of
x with phi(phi(x))=n and P(phi(x)). `restricted_second_eq_sum` identifies it
exactly with the sum of g(m) over phi(m)=n satisfying P.

* `eventually_restricted_second_le`: if g is subpower on P, then the restricted
  two-step count is at most n^epsilon times the number of permitted middle
  values in the one-step fiber.
* `eventually_bounded_valuation_second_le` applies this whenever the middle
  value has any fixed upper bound on its 2-adic valuation.
* `eventually_squarefree_second_le` specializes to

      restrictedSecondMultiplicity Squarefree n <= n^epsilon*gSquarefree(n).

These facts locate a possible iteration gain in middle values with unbounded
2-adic valuation. They do not exclude such a gain, establish a new lower bound
for any iterate, or provide a new multiplicity exponent for g. No assertion
about the statistical distribution of Pratt trees or fixed iterates was used.

Implementation note: the predicate-dependent restricted count and its general
lemmas carry an explicit `[DecidablePred P]`. This avoids mismatched classical
versus concrete decision instances in `Finset.filter` during specialization.

Temporary `/tmp/IterateProbe.lean` was removed. There are no pending Lean repairs
from this continuation. The original conjecture remains **unsolved**;
`Submission/Spec.lean` is unchanged with `sorry` and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof or disproof was submitted in this continuation.


## Finer and beyond-half partition models: exact checks and bounded follow-up

This continuation recovered the completed size-36 certificate and verified it
independently with integer arithmetic. It also verified a new size-18 model
whose moment cutoff is two thirds of total size. Neither is a model of actual
primes, an asymptotic construction, or a disproof of the conjecture.

The general independent checker is
`Submission/Experiments/check_partition_model_exact.py`. Invoke it with a
certificate path and its density cap. It clears a common denominator and
checks positivity, normalization, every requested binomial moment, all
single-part means, absence of smooth outcomes, and the density cap exactly.
The JSON field `halfLevel` is a legacy name: it specifies the moment cutoff
even when that cutoff exceeds half the total size.

Verified certificates:

* `finer_partition_cap100_certificate_36_4.json`: total size 36, selected-moment
  weight at most 18, and every single-part mean 1/j. Every outcome has a part
  at least 10, so fourth-root-smooth outcomes have zero mass. There are 1,623
  positive rational weights and 1,615 moment equations. The density cap is
  **100**, not 2. A common denominator has 356 decimal digits.
* `partition_level_certificate_18_12_6_cap2.json`: total size 18, selected-moment
  weight at most 12, and every single-part mean 1/j. Every outcome has a part
  at least 4, so sixth-root-smooth outcomes have zero mass. There are 303
  positive rational weights and 278 moment equations, with density cap 2.
  A common denominator has 33 decimal digits.

The discovery/reconstruction script was preserved as
`Submission/Experiments/partition_level_model.py` (run using Sage Python).
For cutoffs above half, it uses modular linear algebra to select constraint
rows for the numerical solver. After rational reconstruction it checks every
original equation, including those omitted from that numerical step. Only
this final exact check and the independent checker support the certificates;
numerical feasibility or infeasibility alone does not.

Follow-up runs with (size, cutoff, root, cap)=(24,18,8,2) and (24,16,6,2)
were stopped while still inside HiGHS. Neither produced a candidate or an
exact certificate. They are inconclusive. The (24,18,6,2) run had reported
numerical infeasibility, but no exact dual certificate was reconstructed;
no impossibility theorem is claimed. No background process remains from
these runs.

The input-scale record estimates were rechecked: their sufficient margin is
K*(u-s)<u with u>1, equivalent for s<=1 to s>1-1/K. They therefore preserve
only a fixed smoothness range when the attained exponent is fixed. This
review supplied no new exponent gain or arithmetic estimate.

The original conjecture is still **unsolved**. `Submission/Spec.lean` remains
unchanged with its original `sorry`; SHA-256:
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof or disproof was submitted in this continuation.

## Quantitative power-series spectrum and its feedback limitation

New completed file: `Submission/PowerSmoothSpectrum.lean`, importing
`Submission.RationalSmoothMultiplicity`. It compiles cleanly and has a built
olean. `Submission/PowerSmoothSpectrumCheck.lean` checks all eight exported
declarations; each depends only on `propext`, `Classical.choice`, and
`Quot.sound`. No declaration imports `Spec.lean` or its sorry.

The new transfer allows a general power-series exponent rather than just
reciprocal divergence:

* `rational_power_nonsummability_supplies_dyadic_family` extracts the required
  prime families from nonsummability with arbitrary admissible counting
  exponent.
* `infinite_g_gt_of_rational_smooth_power_nonsummability`: for 0<b<a and
  0<=s<=1, divergence of the p^(-s) series over primes whose predecessors
  have relative smoothness b/a implies infinitely many g(n)>n^gamma for
  every 0<=gamma<s-b/a. Natural-floor rounding and the fixed pigeonhole
  losses are removed by rescaling.
* `summable_rational_smooth_power_of_g_power_bound`: if theta>=0 and
  g(n)<=n^theta eventually, then that shifted-prime series converges for
  every s>theta+b/a. The s>1 case is also included.
* `summable_root_smooth_power_of_g_power_bound` gives the predecessor-indexed
  version: for every k>=2, the root-k predecessor series converges for all
  s>theta+1/k. The change from p to p-1 is justified by a 2^s comparison,
  not silently assumed.
* `eventually_g_le_of_root_smooth_power` eliminates the auxiliary exponent
  u from the existing rough-part upper estimate. Summability at 0<=s<=1
  with s>1-1/k implies g(n)<=n^t eventually for every t>s.
* `negation_forces_quantitative_smooth_series` starts with the exact whole
  negation of Erdős 821 and produces a **single** theta in [0,1) such that
  the eventual g bound and all the rational-smooth series conclusions hold.
  The negation is an explicit hypothesis, not a proved proposition.

The two transfers do not form an exponent-improving loop. With delta=1/k,
using the newly obtained summability in the rough-part estimate requires
both s>theta+delta and s>1-delta. The elementary verified lemma
`quantitative_series_feedback_margin` gives

    theta < (1+theta)/2 < s

when theta<1. Thus this particular feedback weakens the starting upper
exponent. This is not a general barrier theorem for other arithmetic inputs,
and no endpoint assertion is made.

No new unconditional smooth-prime estimate or multiplicity exponent was
obtained. The original conjecture remains **unsolved**. `Submission/Spec.lean`
is unchanged with its original `sorry` and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof or disproof was submitted. The temporary
`/tmp/PowerSmoothProbe.lean` was removed; no Lean repair or background process
is pending from this continuation.

## Fixed iterates on bounded-valuation outputs

New completed file: `Submission/IteratedTotientValuation.lean`, importing
`Submission.IteratedTotientFibers`. It compiles cleanly and has a built olean.
`Submission/IteratedTotientValuationCheck.lean` audits all six declarations;
only `propext`, `Classical.choice`, and `Quot.sound` occur. The new source is
117 lines and contains no sorry or added axiom.

The arithmetic starting point is

    nu_2(m) <= nu_2(phi(m)) + 1.

It follows from phi(2^a)|phi(m) when 2^a|m, including explicit treatment of
zero and exponent zero. The bound iterates to

    nu_2(m) <= nu_2(phi^[k](m)) + k.

`two_valuation_le_of_mem` specializes this to an inverse fiber.

The main unconditional theorem,
`eventually_multiplicity_le_of_bounded_two_valuation`, proves that for every
fixed k,K and epsilon>0, eventually in the output n,

    nu_2(n)<=K  ->  g_k(n)<=n^epsilon.

The induction uses the exact disjoint fiber recurrence, the existing
one-step bounded-valuation bound, and the fact that every large one-step
input lies below n^2. Middle values have valuation at most K+1; an epsilon/4
induction bound for each middle fiber becomes n^(epsilon/2), and the number
of middle values is at most n^(epsilon/2).

`finite_large_multiplicity_bounded_two_valuation` records finiteness of the
exceptional polynomially large fibers in each such output class.
`finite_large_multiplicity_squarefree_outputs` applies this with K=1 to all
squarefree outputs.

This controls **output** valuation for every fixed iterate, extending the
earlier two-step statement about bounded-valuation **middle** values. It
neither gives a lower bound for iterated multiplicity nor proves that maximal
multiplicity exponents are invariant under iteration. Outputs with unbounded
2-adic valuation are not controlled by the new subpower assertion. No
uniform threshold for growing k or K is claimed.

The original conjecture remains **unsolved**. `Submission/Spec.lean` is
unchanged with its original `sorry` and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof or disproof was submitted. No proof repair or background
process is pending from this continuation.

## Fixed iterates retain high prime exponents

Completed `Submission/IteratedPowerfulTotient.lean` and its type/axiom audit
`Submission/IteratedPowerfulTotientCheck.lean`. The proof file compiles cleanly
and has a built olean. All seven audited declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. The formerly pending `Finsupp.filter`
evaluation was resolved using `Finsupp.filter_apply`; no proof error remains.

The central local lemma is `factorization_eq_or_le_of_iterate_eq`: if a,b are
nonzero, their prime exponents agree above p, and phi^[k](a)=phi^[k](b), then

    nu_p(a)=nu_p(b), or both nu_p(a),nu_p(b)<=k.

It follows by iterating the triangular factorization identity

    nu_p(phi(m)) = max(nu_p(m)-1,0) + sum_{q|m, q>p} nu_p(q-1).

Choosing the largest prime where two initial factorizations differ gives
`eq_of_iterate_eq_of_low_exponent_agreement`. Consequently:

* `lowExponentSignature_injOn_fiber`: within each fixed iterated fiber, the
  input is determined by its prime factors of exponents between 1 and k,
  including their labels and exponents.
* `iterate_injective_on_highPower`: phi^[k] is injective on inputs whose
  nonzero prime exponents all exceed k.
* `iterate_pow_injective`: for k<r, a |-> phi^[k](a^r) is injective.
* `highPower_fiber_card_le_one`: at most one such high-power input occurs in
  each iterated fiber. Zero inputs and k=0 are included in the proofs.

This is a structural upper restriction, **not a multiplicity lower bound**.
It does not establish exponent invariance under iteration. In particular,
raising inputs to powers greater than the iterate count makes the iterated
map injective; it cannot preserve an equal-output family of distinct bases.
For k>1, possible low-exponent prime labels need not satisfy p-1|n, so the
one-step fixed-arity subpower estimate does not automatically generalize.

The original conjecture remains **unsolved**. `Submission/Spec.lean` is
unchanged with its original `sorry` and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof or disproof was submitted in this continuation. The
temporary `/tmp/IteratedPowerfulProbe.lean` was removed. No proof repair is
pending in this new auxiliary file.

## A missing-prime radical lift: exact identity and polynomial size loss

Completed `Submission/IteratedRadicalLift.lean` (299 lines), with built olean,
and `Submission/IteratedRadicalLiftCheck.lean`. Both compile cleanly. All eight
audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
No declaration in this file asserts the original conjecture or its negation.

This continuation tested a concrete proposed conversion of a two-step
collision into a one-step collision. For an input m, put

    a = phi(m), n = phi(a), r = rad(a),
    t = product of primes dividing a but not m,
    c = product of primes dividing both a and m,
    L(m) = m*t.

The lift uses only missing primes, not the whole radical, so it avoids
unnecessary repetitions of primes already in m. Nevertheless:

* `lift_identity` proves the exact formula phi(c)*phi(L(m)) = n*r.
* `lift_output_ge_missing` proves phi(L(m)) >= n*t.
* `lift_prime_output` specializes to a prime p:

      phi(L(p)) = phi(p-1)*rad(p-1).

Neither the radical r nor the common-prime correction c is determined by the
final two-step output. The formula does not produce a common one-step output
for a whole iterated fiber, and a uniform subpower size bound for this lift
is actually false.

An elementary counting argument proves `exists_prime_large_radical`: for
every N, some prime p>N satisfies rad(p-1)^2>p-1. For completeness, the
argument is formalized rather than assuming any squarefree-shifted-prime
asymptotic. If rad(n)^2<=n and n>=y^4, write n=b^2*a with a squarefree.
Then a<=rad(n) implies a<=b^2, hence b>=y. The existing large-square-divisor
estimate gives at most 2X/y such exceptional n up to X. Taking
X=(2^t)^8, y=2^t, and 64(t+1)<=2^t, this count together with the small prefix
cannot cover the elementary dyadic lower bound for primes up to X.

`exists_prime_large_radical_above_output` also makes phi(p-1) arbitrarily
large, using the established bound p-1<=24*phi(p-1)^2. Consequently:

* `exists_prime_lift_power_loss`: for every B there is a prime p with
  n=phi(phi(p))>B and n^3<phi(L(p))^2.
* `not_eventually_lift_output_le`: for every real epsilon<1/2, it is false
  that phi(L(m))<=phi(phi(m))^(1+epsilon) eventually for all inputs m.

**Scope:** These are obstructions to this specific uniform radical-lift
construction. They are not a proof against every fiber encoding, nor against
an encoding restricted to suitably chosen large fibers. No polynomial lower
bound for an iterated multiplicity was obtained here. A large radical does
not imply a large *individual* prime factor, so the prime existence theorem
is not a disproof of smooth shifted-prime abundance or of Erdős 821.

The original conjecture remains **unsolved**. `Submission/Spec.lean` is
unchanged with its original `sorry` and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof or disproof was submitted. The temporary
`/tmp/RadicalLiftProbe.lean` was removed. No Lean proof repair is pending in
the new file.

## Repeated cofactor-sieve restriction: the missing relative estimate

A further continuation rechecked whether the completed composite second sieve
could be iterated on its retained smooth-prime family. No new Lean theorem,
unconditional lower exponent, or settlement resulted.

The existing rejection estimate is an absolute upper bound, relative to the
original progression reciprocal mass W. It is not an upper bound proportional
to the mass of the already retained family. After restricting from smoothness
Y0 to a smaller Y1, a further subtraction still spends the same original
lower-bound budget. Subdividing the rejected cofactor range does not refresh
that budget. The already verified cube-root limitation of the explicit
majorant remains applicable; no parameter iteration was found that bypasses it.

For example, a quantitative upper bound on each newly rejected slice relative
to the *current* retained count, with sufficiently uniform constants as the
positive smoothness parameter decreases, could support a genuine iteration.
No such relative estimate follows from the available absolute prime-pair
sieve bound. Proving it would require additional arithmetic information about
the filtered prime family. It was not assumed here.

The original conjecture remains **unsolved**, and `Submission/Spec.lean`
retains its original `sorry`. No proof/disproof was submitted and no new
source file was created in this recheck.

## Higher divisor moments on shifted primes: reference and hypothesis audit

This continuation checked the local reference material and the existing
`DivisorMoments.lean` development for a possible alternative to the explicit
smooth-modulus criterion. No missing published result or applicable Lean
lemma was found locally. `/opt` contains Pantograph documentation, not an
additional number-theory reference corpus. No network retry was made.

The prospective arithmetic input is a sufficiently strong lower bound for

    sum_{p<=X, p prime} tau_k(p-1),

where tau_k is the k-fold divisor function. The thought was to compare high
shifted-prime divisor moments with weighted prime-pair upper bounds for a
large factor of p-1. This is only an investigated route: no complete weighted
comparison or unconditional high-moment lower bound was proved here.

`Submission/DivisorMoments.lean` does NOT supply this input. Its results are
upper bounds over unrestricted integers, such as

    sum_{n<=X} tau(n)^2 <= X*(1+log X)^3,

and their application to Vaughan Type II coefficients. Neither these upper
bounds nor the existing below-half progression estimates may be substituted
for a lower bound of the required size on shifted primes. High prime-weighted
moments with suitable constants remain an additional arithmetic obligation.
No generalized Titchmarsh asymptotic was silently assumed.

No new Lean theorem or multiplicity exponent resulted. The original
conjecture remains **unsolved**; `Submission/Spec.lean` is unchanged with
`sorry`, and no complete proof/disproof was submitted.

## Higher divisor weights, subexponential Euler cost, and a finite rough-moment bound

This continuation completed four auxiliary files. All four compile cleanly,
have built oleans, and have separate type/axiom audits. They do **not** prove
the missing lower moment on shifted primes and do not settle Erdős 821.

### `HigherDivisorWeights.lean`

Definitions in namespace `Erdos821.HigherDivisors`:

    tau(k,n) = (zeta^k)(n)
    harmonicMoment(k,A) = sum_{1<=n<=A} tau(k,n)/n.

The prime-power identity is

    tau(k+1,p^e) = choose(e+k,k).

It yields the useful inequality

    tau(k+1,p*n) <= (k+1)*tau(k+1,n),

**without** a coprimality hypothesis between p and n. Iterating it over a
finite prime set bounds weighted multiples in the harmonic moment. Expanding
prime products over subsets then proves

    sum_{n<=A} tau(k+1,n)*(n/phi(n))^2/n
      <= harmonicMoment(k+1,A)
         * product_{p<=A, p prime}(1+8*(k+1)/p^2).

All fourteen lemmas, including `tau_zero_input`, are covered by the audit
`HigherDivisorWeightsCheck.lean`.

### `SubexponentialEulerCost.lean`

The formerly pending file is now repaired and compiled. It defines

    logEulerCost(k) = sum_{n>=0} log(1+8*k/n^2)
    eulerCost(k) = exp(logEulerCost(k)).

Here n=0 contributes zero under Lean's inverse-zero convention. A finite
Euler product is at most this cost. For every fixed a>=0,

    log(1+a*k)/k -> 0.

Tannery's theorem applies with summable majorant 8/n^2, giving

    logEulerCost(k)/k -> 0.

Consequently, for every epsilon>0, eventually

    eulerCost(k) <= exp(epsilon*k).

The final weighted totient-ratio bound is

    sum_{n<=A} tau(k+1,n)*(n/phi(n))^2/n
      <= eulerCost(k+1)*harmonicMoment(k+1,A).

This avoids the unnecessary exponential-in-k loss obtained by replacing
all Euler factors by their exponential upper bounds before taking the
large-order limit.

Implementation repairs: added the `Topology` notation scope; used
`le_add_of_nonneg_right` rather than `positivity` for goals `1<=1+x`; made
the harmonic-moment nonnegativity argument explicit and commuted the final
product in a separate calc step. All nine declarations have allowed-axiom
audits in `SubexponentialEulerCostCheck.lean`.

### `DivisorRankin.lean`

This new file supplies finite Rankin bounds with the order dependence
retained. No infinite-series identity for divisor powers is needed. A finite
weighted divisor convolution gives, for any real s,

    sum_{n<=A} tau(k,n)*n^(-s)
      <= (sum_{n<=A} n^(-s))^k.

An elementary antitone integral comparison gives, for s>0,

    sum_{n<=A} n^(-1-s) <= 1+1/s.

Thus

    harmonicMoment(k,A) <= A^s*(1+1/s)^k.

For k>0 and A>1, taking s=k/log A proves

    harmonicMoment(k,A)
      <= (exp(1)/k)^k*(log A+k)^k.

This retains the (e/k)^k scale, unlike the coarse H_A^k bound. The six
lemmas are audited in `DivisorRankinCheck.lean`.

### `WeightedRoughPrimes.lean`

Define `roughPrimeMoment(k,X,Y)` as the sum of tau(k,p-1) over p<=X prime
whose predecessor has a prime factor >=Y. For X<=K*Y, a finite sigma-image
cover, with nonnegative weights, proves

    roughPrimeMoment(k+1,X,Y)
      <= (k+1)*sum_{a<=K} tau(k+1,a)*primePairCofactorCount(X,a).

The removed large prime may divide a; `tau_prime_mul_le` handles that case.
No assumption of pairwise disjointness in the cover is made. The final
prime-pair bound is, for K<=X and J>0,

    roughPrimeMoment(k+1,X,Y)
      <= (k+1) * [
           16*X/(J*log 2)^2
             * eulerCost(k+1)*harmonicMoment(k+1,K)
           + (2^(64J)+2^(16J)+1)*K*H_K^k
         ].

The underlying weighted prime-pair bound and unweighted summatory tau bound
are also exported. All four theorems are audited in
`WeightedRoughPrimesCheck.lean`.

### What remains missing, and the order-dependence check

The new files complete an upper-bound component of the prospective
higher-moment argument. They do not provide the lower bound for

    T_r(X) = sum_{p<=X, p prime} tau(r,p-1).

Schematic comparison (not an asserted new Lean theorem): with K of size
X^(1-delta), J a small positive multiple of delta*log X, and fixed r, the
rough main term has the form

    constant_delta * r*eulerCost(r)*(e/r)^r
      * (1-delta)^r * X*(log X)^(r-2).

Relative to the expected full moment coefficient 1/(r-1)!, the extra
order-dependent factor is subexponential in r (using Stirling). Therefore a
full-size lower moment with sufficiently sharp dependence on r would be
useful. Merely knowing an unspecified positive lower constant for each r
is not enough.

Restricting a divisor expansion to the existing progression-distribution
range below X^(1/2) does not automatically give such constants. At the
schematic logarithmic-simplex main-term level, a cutoff X^theta replaces
(log X)^(r-1) by (theta*log X)^(r-1), losing theta^(r-1). This loss remains
exponential in r when theta is fixed below one. The new subexponential
Euler bound removes a separate avoidable upper-bound loss, not this
lower-bound range restriction. No generalized Titchmarsh asymptotic, nor
an extension of the progression level, was assumed.

### Verification and current state

Audit logs:

- `/tmp/HigherDivisorWeightsCheck.log`
- `/tmp/SubexponentialEulerCostCheck.log`
- `/tmp/DivisorRankinCheck.log`
- `/tmp/WeightedRoughPrimesCheck.log`

All audited declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. There are no source `sorry`s in the four new auxiliary files.
Temporary probes for shifted divisor weights, the Euler cost, Rankin's
bound, and the weighted cover have been removed.

The original conjecture remains **unsolved**. `Submission/Spec.lean` has
not been changed; its SHA-256 remains

    8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.

No proof/disproof was submitted in this continuation.

## Divisor-pair overlap: an actual shifted-prime obstruction to a pointwise shortcut

The next continuation examined whether Cauchy--Schwarz could promote a
lower divisor moment into the sharp higher moments missing from the new
rough-prime comparison. It completed `DivisorMomentOverlap.lean` (with
`DivisorMomentOverlapCheck.lean`), rather than assuming an unjustified
pointwise comparison.

### Verified results

For every n>0,

    tau(2,n)^2 >= (4/3)^omega(n) * tau(3,n),

where omega(n)=n.primeFactors.card. At a positive prime exponent e the
local calculation is

    (e+1)^2 >= (4/3)*choose(e+2,2).

Multiplicative factorization gives the global inequality. Dirichlet's
theorem, applied to residue class 1 modulo a product of r distinct primes,
then supplies arbitrarily large primes p with omega(p-1)>=r. Consequently,
for every real C and natural B there exists a prime p>B with

    C*tau(3,p-1) < tau(2,p-1)^2.

In particular, even on actual shifted primes, there is no eventual uniform
pointwise bound tau(2,p-1)^2 <= C*tau(3,p-1).

The file also identifies tau(2,n) with n.divisors.card, exports

    tau(2,n)^2 <= tau(4,n),

and defines

    shiftedPrimeMoment(k,X) = sum_{p<=X, p prime} tau(k,p-1).

The correct direct Cauchy--Schwarz consequence is

    shiftedPrimeMoment(2,X)^2
      <= pi(X)*shiftedPrimeMoment(4,X),

where pi(X) is `(X+1).primesBelow.card`. It lands at order four, not three.
Even if one supplied the expected order-two lower bound of size X, this
direct inequality with pi(X) of size X/log X would only give an order-four
lower bound of size X*log X, one logarithm below its expected scale
X*(log X)^2. No sharp higher-order lower bound follows from that calculation.

### Scope

This rules out only the particular pointwise overlap-absorption shortcut.
It does NOT disprove an averaged comparison, all possible moment methods,
or Erdős 821. The arbitrarily many specified prime factors obtained by
Dirichlet do not have a suitable size bound in terms of p, so they do not
establish the smooth shifted-prime density needed for the conjecture.

All ten lemmas/theorems compile cleanly and their audits use only
`propext`, `Classical.choice`, and `Quot.sound`. The source has no `sorry`.
Logs are `/tmp/DivisorMomentOverlap.log` and
`/tmp/DivisorMomentOverlapCheck.log`; the temporary API probe was removed.

The original conjecture remains **unsolved**. `Spec.lean` is unchanged
with its original `sorry` and the same SHA-256 as recorded above. No
complete proof or disproof was submitted in this continuation.

## Factorial harmonic lower bound and explicit shifted-prime moment transfer

This continuation completed three further auxiliary files, all cleanly
compiled, built, and audited. It did NOT establish the sharp prime-weighted
lower moment or settle the original conjecture.

### Distribution-hypothesis review

A closer review of `PrimeProgressions.lean` and the composite extensions is
important: the available theorems concern prime moduli or specified products
of large primes. They are NOT an all-modulus, higher-divisor-weighted
Bombieri--Vinogradov theorem. The prime-modulus arguments use primitivity of
nonprincipal characters, and the product-modulus extensions control their
particular conductor decomposition. They cannot simply be applied to

    sum_{d<=Q} tau(k,d)*abs(psi(X;d,1)-psi(X)/phi(d)).

In particular, the small-conductor terms in that unrestricted sum have not
been eliminated. No Siegel--Walfisz estimate or weighted Bombieri--Vinogradov
theorem was silently imported or assumed.

### `HarmonicDivisorLower.lean`

Four verified lemmas establish the unconditional factorial-scale harmonic
lower bound, for A>=1 and every natural k:

    harmonicMoment(k,A) >= log(A+1)^k/k!.

The proof first reindexes divisor convolution exactly as

    harmonicMoment(k+1,A)
      = sum_{m<=A} harmonicMoment(k,floor(A/m))/m.

The antitone logarithmic kernel has exact integral

    integral_1^B (log B-log x)^k/x dx = log(B)^(k+1)/(k+1).

The left Riemann sum bounds this integral from below. The shift A+1 is
useful because

    (A+1)/m <= floor(A/m)+1,

so induction retains the factorial coefficient without floor losses. This
is an estimate over all positive integers; it is not by itself a lower
bound over shifted primes.

### `ShiftedDivisorLowerTransfer.lean`

Definitions in namespace `Erdos821.HigherDivisors`:

    shiftedMangoldtMoment(k,X) = sum_{n<=X} Lambda(n)*tau(k,n-1)
    nonprimeMangoldtMoment(k,X)
      = sum_{n<=X, n not prime} Lambda(n)*tau(k,n-1)
    divisorProgressionError(k,Q,X)
      = sum_{d<=Q} tau(k,d)*abs(psi(X;d,1)-psi(X)/phi(d)).

The seven verified statements provide the exact finite transfer. Truncating
the divisor sum yields

    psi(X)*harmonicMoment(k,Q) - divisorProgressionError(k,Q,X)
      <= shiftedMangoldtMoment(k+1,X).

Here `psi` denotes the already defined `mangoldtSum`; the proof uses
phi(d)<=d and keeps the actual absolute discrepancies. The n=1 term is
handled by Lambda(1)=0 rather than by treating 0 as a nonzero predecessor.
The harmonic lower bound then gives the factorial main term. Separating
primes from nonprime prime powers yields

    shiftedMangoldtMoment(k,X)
      <= log X*shiftedPrimeMoment(k,X)+nonprimeMangoldtMoment(k,X).

The file also gives a finite bound for the nonprime term under an explicit
uniform upper bound on the divisor weights.

### `HigherDivisorSubpower.lean`

Five verified statements remove that upper-bound hypothesis. Elementary
induction over divisor convolution proves

    tau(k+1,n) <= card(n.divisors)^k.

Together with the earlier uniform subpower divisor-count bound, this gives,
for any fixed k and epsilon>0,

    tau(k+1,n) <= n^epsilon                 eventually,
    tau(k+1,n) <= C(k,epsilon)*n^epsilon    for every n.

The global statement includes n=0, where both sides vanish. Taking
epsilon=1/4 and using the established nonprime Mangoldt bound gives

    nonprimeMangoldtMoment(k+1,X)
      <= 2*C(k)*X^(3/4)*log X,             X>=1.

The resulting exported lower transfer has **no distribution hypothesis**,
but keeps the discrepancy explicitly on its left side:

    for each k there exists C>=1 such that, for Q,X>=1,

    psi(X)*log(Q+1)^k/k!
      - divisorProgressionError(k,Q,X)
      - 2*C*X^(3/4)*log X
        <= log X*shiftedPrimeMoment(k+1,X).

Thus the nonprime prime-power error is no longer a missing ingredient.
The weighted progression discrepancy remains unestimated. This is NOT a
conditional conjecture presented as a solution: the formula may have a
negative left side when the discrepancy is large.

### Scope and order dependence

Even if one separately supplied negligible discrepancy with Q of size
X^theta, this particular lower transfer would have main coefficient
proportional to theta^k/k!. At theta=1/2 that still loses 2^(-k). The new
factorial harmonic estimate avoids an additional artificial loss; it does
not extend the distribution range or provide lower constants with
k-th roots tending to one. Those remain genuine obstacles to using the
higher-moment rough-prime comparison to settle Erdős 821.

The sixteen audited lemmas/theorems across the three new files use only
`propext`, `Classical.choice`, and `Quot.sound`. Audit files and logs have
matching `...Check.lean` and `/tmp/...Check.log` names. There are no source
`sorry`s in these auxiliary files. Their temporary API probes were removed.

`Submission/Spec.lean` remains unchanged with its original `sorry` and
SHA-256 `8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The original conjecture is still **unsolved** and no complete proof or
disproof was submitted in this continuation.

## Signed cofinal-error recheck after the divisor-moment lower transfer

This continuation rechecked the one-sided route rather than adding another
bound for the already controlled prime-power remainder. No new analytic
estimate or Lean theorem resulted.

`CofinalSmoothModulusCondition` is an aggregate signed condition, not an
absolute-value bound, but it still concerns growing modulus families. With
r=t-2 prime factors in `primeProductModuli r m` and input scale
X=2^(64*t*m), the modulus scale is close to X^(1-2/t). Letting X tend to
infinity for a fixed modulus family does not preserve this scale relation.
Qualitative prime distribution for each fixed modulus therefore cannot be
substituted for the cofinal growing-family condition.

The currently proved below-half product-modulus estimate requires
2*r+1<=t. For r=t-2 this gives t<=3, not the unbounded t needed by the
criterion. Keeping character sums signed does not create a positivity
lemma: `SignedCharacterKernels.lean` already gives an exact negative
Mangoldt-weighted example. That finite example does not rule out a new
asymptotic signed-average theorem; no such theorem was established here.

The local reference environment was rechecked. `/opt` still contains
Pantograph documentation rather than a number-theory reference corpus.
The documented DNS and connection failures were not retried, because no
change in network availability was identified. No new paper or updated
status was obtained or assumed.

This was a review of the remaining arithmetic gap, not a settlement or a
new impossibility theorem. `Submission/Spec.lean` is unchanged with its
original `sorry`; no proof/disproof was submitted.

## Fixed-iterate amplification recheck after the moment investigation

This continuation revisited the possible alternative of constructing large
fixed-iterate fibers and transferring them to one-step fibers. No new
exponent-preserving transfer or arithmetic lower bound was proved.

The exact recurrence in `IteratedTotientFibers.lean` sums earlier
multiplicities over a one-step fiber. Its available unconditional transfer
adds exponents; under a one-step upper exponent a, it gives at most k*a
(up to an arbitrarily small loss) after k steps, not exponent a. Hence a
near-linear k-step lower bound alone is insufficient.

`IteratedPowerfulTotient.lean` gives injectivity on inputs whose positive
prime exponents exceed the iterate count. More generally, it injectively
encodes an iterated fiber by its low-exponent signature. Neither assertion
bounds the number or size of the possible prime labels in those signatures.
Forcing the high-power condition by padding requires an independent size
and multiplicity argument. The already audited radical-lift example rules
out a uniform subpower size claim for that particular padding construction;
it does not rule out all restricted-fiber constructions.

No counting estimate controlling the signatures at the strength required
for an exponent-preserving transfer was obtained. No statistical claim
about Pratt trees or iterated smoothness was assumed. This review produced
no new Lean theorem and is not a disproof of the original conjecture.

`Submission/Spec.lean` remains unchanged with its original `sorry`, and
there is no complete proof or disproof ready for submission.

## Unconditional shifted-prime moment lower information from fixed moduli

This continuation obtained a genuine unconditional, but quantitatively weak,
lower statement on the shifted primes. Three new auxiliary files (494 source
lines in total) compile cleanly and have built oleans and type/axiom audits.
They do NOT settle Erdős 821 or supply the sharp high-moment lower bound.

### `ShiftedDivisorPole.lean`

Define

    shiftedMangoldtDirichlet(k,s)
      = sum_{n>=0} Lambda(n)*tau(k,n-1)/n^s.

For each fixed positive order this series is summable for s>1, by the
previous subpower tau bound, `Real.log_le_rpow_div`, and the p-series test.
The n=0 and n=1 terms are handled explicitly.

The fixed-cutoff lower theorem is:

    for every k,Q there exists C=C(k,Q) such that, for 1<s<=2,

    harmonicMoment(k,Q)/(s-1)-C
      <= shiftedMangoldtDirichlet(k+1,s).

It uses Mathlib's `vonMangoldt.LSeries_residueClass_lower_bound` separately
for the finitely many residue classes 1 modulo d<=Q. This is an actual
available fixed-modulus theorem, not a uniform PNT in progressions. Finite
summation, positivity, and phi(d)<=d give the displayed lower bound. There
is NO bound on how C depends on Q or k.

Since harmonicMoment(k+1,Q) is unbounded in Q, the theorem gives, for every
fixed k>=0,

    (s-1)*shiftedMangoldtDirichlet(k+2,s) -> +infinity
        as s -> 1+.

The cutoff Q is fixed before taking the limit in s; no growing-modulus
estimate is inferred. Seven declarations are audited in
`ShiftedDivisorPoleCheck.lean`.

### `ShiftedPrimeMomentPole.lean`

Split the coefficients into `primeMomentWeight` and
`nonprimeMomentWeight`, and define `shiftedPrimeDirichlet` and
`nonprimeDirichlet` accordingly. In particular,

    shiftedPrimeDirichlet(k,s)
      = sum_{p prime} log(p)*tau(k,p-1)/p^s.

The nonprime contribution is summable at s=1. Its proof groups positive
terms into [2^(4j),2^(4(j+1))) and applies the previously established
nonprime Mangoldt moment bound. The block is at most

    64*C*log(2)*(j+1)*2^(-j),

which is summable. For s>=1 the nonprime Dirichlet sum is bounded by its
value at 1. The exact prime/nonprime decomposition consequently proves

    (s-1)*shiftedPrimeDirichlet(k+2,s) -> +infinity
        as s -> 1+.

Thus the unbounded normalized residue comes from actual primes, not
higher prime powers. Ten declarations are audited in
`ShiftedPrimeMomentPoleCheck.lean`.

### `ShiftedPrimeMomentLower.lean`

An elementary Abelian upper bound converts the Dirichlet conclusion into
finite-cutoff lower information. For a nonnegative sequence f with f(0)=0
and partial sums at most C*N, dyadic blocks give

    sum_n f(n)/n^s <= 2*C/(1-2^(1-s)),        s>1.

For 1<s<=2 this implies

    (s-1)*sum_n f(n)/n^s <= 4*C/log 2.

No Tauberian asymptotic is assumed. Applied contrapositively to the prime
moment weights, with the finite initial segment absorbed into the constant,
this proves the exported unconditional theorem

    frequently_shiftedPrimeMoment_gt (k : Nat) (A : Real) :
      frequently X -> infinity,
        A*X < log(X)*shiftedPrimeMoment(k+2,X).

Equivalently, for every fixed order r>=2 and every fixed A, arbitrarily
large X satisfy

    sum_{p<=X} tau(r,p-1) > A*X/log X.

The four declarations are audited in `ShiftedPrimeMomentLowerCheck.lean`.

### Scope and the unchanged conjecture gap

This is weak lower information at fixed order, not the full expected size
X*(log X)^(r-2). It gives no rate for the coefficient tending to infinity,
no uniformity in r, and no usable relation between Q and the scale X.
In particular, for r=2 it does not even establish a lower bound of size X;
for larger r the missing logarithmic powers are larger. The high-order
rough-prime upper bound cannot be made smaller than this lower bound by
any argument proved here. Neither limit order nor the cutoff-dependent
constant may be exchanged for free.

All twenty-one audited declarations use only `propext`, `Classical.choice`,
and `Quot.sound`. Audit logs are `/tmp/ShiftedDivisorPoleCheck.log`,
`/tmp/ShiftedPrimeMomentPoleCheck.log`, and
`/tmp/ShiftedPrimeMomentLowerCheck.log`. The three source files contain no
`sorry`. All temporary API probes from this continuation were removed.

The original conjecture remains **unsolved**. `Submission/Spec.lean` is
unchanged with its original `sorry` and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof or disproof was submitted in this continuation.

## Pole-normalization and quantifier check

The next continuation compared the new fixed-modulus lower limit with the
normalization required by the higher-order rough-prime comparison. No new
analytic estimate or Lean theorem was obtained.

For D_r(s)=sum_{p prime} log(p)*tau(r,p-1)/p^s, the proved conclusion is

    (s-1)*D_r(s) -> infinity,               fixed r>=2.

The expected full moment scale would instead concern (s-1)^r*D_r(s), with
suitable dependence of its lower coefficient on r. Unboundedness with the
first normalization does not imply a positive lower coefficient with the
second. As a purely analytic illustration (not a model asserted for the
primes), D(s)=(s-1)^(-3/2) has the first property and
(s-1)^2*D(s)->0. No rate was inferred from the new limit theorem.

Likewise, `frequently_shiftedPrimeMoment_gt` fixes the constant A before
choosing arbitrarily large X. Substituting a growing power of log X for A
would change the quantifier statement and is not justified. In the
fixed-cutoff Dirichlet lower theorem, C depends on Q without a proved
uniform bound, so Q cannot silently be taken to grow exponentially in
1/(s-1).

Even lower constants at the full logarithmic order, if obtained separately
for each r without adequate order dependence, would still leave the
subexponential-versus-exponential comparison unresolved. No such stronger
lower bound was proved in this check. This identifies the remaining gap,
not an impossibility theorem for all moment methods or a disproof of
Erdős 821.

`Submission/Spec.lean` remains unchanged with its original `sorry`. There
is no complete proof or disproof ready for submission.

## Fixed-modulus constant: direct source check

The continuation inspected the implementation of
`ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound` in
Mathlib's `NumberTheory/LSeries/PrimesInAP.lean`, rather than relying only
on its exported statement. Its constant is obtained by applying
`IsCompact.bddBelow_image` to the real part of
`LFunctionResidueClassAux` on [1,2], for a fixed modulus. The proof gives
no quantitative dependence on that modulus. The auxiliary function
involves logarithmic derivatives of the nonprincipal Dirichlet
L-functions; their nonvanishing and continuity do not themselves provide
the uniform estimate needed here.

Thus this source check yields no justification for a modulus cutoff
growing with 1/(s-1), and no stronger shifted-prime moment lower bound.
No new Lean declaration was added. `Submission/Spec.lean` is unchanged;
the conjecture remains unresolved in this development, with neither a
complete proof nor a disproof available for submission.

## Growing divisor order: a finite uniform comparison

New completed file `Submission/GrowingOrderMomentAudit.lean`, importing
`HarmonicDivisorLower`. It has a clean build and an olean. Its four theorem
types and axiom dependencies are checked by
`Submission/GrowingOrderMomentAuditCheck.lean`; only `propext`,
`Classical.choice`, and `Quot.sound` occur.

Writing H_k(A)=harmonicMoment(k,A), the new exact inequalities are:

* `harmonicMoment_rectangle_lower`: if Q>=1 and Q*B<=K, then

      H_k(Q)*H_1(B) <= H_(k+1)(K).

  This retains the rectangle m<=B, n<=Q in the convolution sum. It is
  uniform in k, with no fixed-order asymptotic assumption.

* `harmonicMoment_log_rectangle_lower`: for B>=1 this implies

      H_k(Q)*log(B+1) <= H_(k+1)(K).

* `truncated_main_le_rough_sieve_main`: for L>0 and J>0, if

      (J log 2)^2 <= 16(k+1)*eulerCost(k+1)*L*log(B+1),

  then the idealized truncated prime-moment main term X*H_k(Q)/L is
  at most the rough sieve's main upper expression

      (k+1)*16X/(J log 2)^2 * eulerCost(k+1)*H_(k+1)(K).

* `truncated_main_le_rough_of_large_order`: sufficient finite conditions
  are J log 2 <= A L, b L <= log(B+1), b>0, and

      A^2 <= 16(k+1)b.

  Thus a positive logarithmic cutoff gap with bounded sieve scale makes
  these two main expressions overlap once the order is large enough.
  The statement remains valid if the order is chosen as a function of X.

These compare the currently available estimates only. In particular the
rough sieve expression is an UPPER bound, not a lower bound for the actual
rough-prime moment; no obstruction to other arithmetic estimates is
claimed. The idealized lower main term here is not asserted to be an
unconditional shifted-prime lower bound. No new multiplicity exponent or
settlement follows.

`Submission/Spec.lean` remains unchanged with its original `sorry`. There
is no complete proof or disproof to submit.

## Full avoiding-tree counting review

The next continuation inspected `GrowingSmoothPrimeChains`,
`LargeChildAvoidingTrees`, `LargeChildMass`, and
`GrowingCofactorReciprocals` for an arithmetic counting bridge, rather than
another consequence of the negation. No new estimate was obtained.

The negation theorem would give at least half the primes in full avoiding
trees of depth L at cutoffs X_L=2^(R(2k)^(2L)). Its depth is a fixed
multiple of log log X_L. The existing growing-cofactor sieve controls
parents p=a*q+1 only when a<=exp(C sqrt(log p)), for fixed C. A large-child
edge permits cofactors of polynomial size, roughly up to p^(1-1/k).
Consequently the former estimate cannot be applied to the full family of
eligible edges or iterated as a contraction for the avoiding-tree family.

The tree predicate does retain every eligible branch, but it supplies
neither independent prime events across branches nor a relative sieve
estimate inside the avoiding family. No independence or relative-density
claim was assumed. A new arithmetic bound on the full avoiding-tree count
would be needed to turn the conditional lower count into a contradiction.
This review is not a theorem excluding every possible prime-chain method.

No Lean proof source was changed in this continuation. `Spec.lean` still
has its original `sorry`; no complete proof or disproof is available.

## Dense prime-predecessor products have subpower radicals

New completed source `Submission/DensePredecessorSupport.lean` (330 lines),
with fresh olean and a clean build. `DensePredecessorSupportCheck.lean`
checks all 23 lemma/theorem types and their axioms; only `propext`,
`Classical.choice`, and `Quot.sound` occur. No source sorry or added axiom.
Namespace: `Erdos821.DensePredecessors`.

Definitions:

    support(X) = union_{p<=X, p prime} primeFactors(p-1)
    radicalPool(X) = product_{q in support(X)} q
    predecessorProduct(X) = product_{p<=X, p prime} (p-1).

The finite cofactor cover proves, when Z>0 and X<=A*Z,

    #support(X) <= Z + sum_{a<=A} primePairCofactorCount(X,a).

The same q may have several witnesses, but the union cover only uses an
upper bound and does not assume uniqueness. Using the existing averaged
two-prime sieve, at X_m=2^(128*m^2) with A=2^m and Z=X_m/A, proves

    m^2 * #support(X_m)/X_m
      <= cofactorSieveConstant*(1/m^2+1/m) + 4*m^2*(1/2)^m.

Consequently `tendsto_scaled_support` and
`tendsto_log_radicalPool_div` establish

    m^2 * #support(X_m)/X_m -> 0,
    log(radicalPool(X_m))/X_m -> 0.

The product interpretation is exact:

* `predecessorProduct_primeFactors`: its prime factors are `support(X)`;
* `radicalPool_eq_radical_predecessorProduct`: radicalPool is exactly the
  radical of predecessorProduct, not an unrelated majorant;
* `predecessorProduct_eq_totient`: the predecessor product is the totient
  of the product of all primes <=X;
* `log_predecessorProduct_lower`: log(predecessorProduct(X_m))>=X_m/64 for
  m>=1, using the existing Chebyshev theta lower bound.

The main structured size conclusion is
`eventually_radicalPool_le_predecessorProduct_rpow`: for every epsilon>0,

    eventually m: rad(N_m) <= N_m^epsilon,
    N_m = predecessorProduct(X_m).

Two further exact properties are supplied:

    phi(radicalPool(X)) divides predecessorProduct(X),
    2^(pi(X)-#support(X)) <= g(predecessorProduct(X)).

The second specializes the existing independent-optional-support theorem
in `Work.lean`; it is not a new arbitrary-power multiplicity bound.

### Scope and remaining amplification gap

This positively confirms that the earlier *uniform* radical-lift size
obstruction does not apply to every specially chosen output family. The
full prime-predecessor products really do have subpower radicals. However,
the size estimate is relative to the FULL product N_m, with logarithm at
least a constant times X_m. It has not been shown relative to the much
smaller selected outputs used in the fixed positive-exponent constructions.

The optional-support construction guarantees only a number of independent
binary choices on the scale pi(X), whereas log N is on the scale X. Even
making every prime in this pool optional would not by itself yield a fixed
positive multiplicity exponent as X grows. This is a limitation of that
lower construction, NOT an upper bound on the full g(N). Additional primes
outside the pool must not be silently excluded from the actual fiber.

No common-output encoding or exponent-improving amplification was obtained.
The original conjecture is still unresolved. `Submission/Spec.lean` is
unchanged with its original sorry and hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No proof/disproof is ready to submit. The temporary probe in /tmp was only
an API lookup and is not a pending proof repair.

## Selected-output scale after the dense-radical theorem

The continuation checked `SquarefreeInput`, `SmoothInputFamilies`,
`RationalSmoothMultiplicity`, and the existing common-core bounds for a
transfer of the new full-product radical estimate to sparse selected
outputs. No new Lean theorem or amplification resulted.

`exists_divisor_large_gSquarefree` selects a divisor d of an output N with
loss at most the number of divisors of N. Its statement does not give a
fixed-power lower bound d>=N^c. In the prime-subset constructions a product
of k primes <=X has logarithm at most k log X. For k on a fixed power scale
X^theta, theta<1, this is much smaller than the full predecessor product's
logarithm, which the new theorem bounds below by X/64 on its cutoffs.
Thus the proved rad(N)<=N^eta cannot simply be rewritten as a subpower
padding bound relative to that selected output d.

This observation does not prove that a suitable selected output has a
large radical, nor rule out a refined selection argument. The missing
obligations remain a padding estimate at the selected-output scale and an
encoding producing a common one-step totient output while increasing the
multiplicity exponent. Neither was obtained. No independence of support
choices after further restrictions was assumed.

`Submission/Spec.lean` remains unchanged with its original sorry. There is
still no complete proof or disproof to submit.

## Stripping the explicit optional-support fiber

The next continuation inspected the actual construction in
`two_pow_card_sdiff_le_g_prod_pred`, together with the radical-map
injection and divisor-indexed squarefree reduction. No new proof source
was added and no exponent improvement was obtained.

In the full-pool construction, the admissible supports are C union T,
where C is the predecessor-prime support and T ranges through subsets of
P minus C. Taking the radical of each input preserves distinctness, but
its totient is phi(product(C))*product_{p in T}(p-1), generally a different
value for different T. Thus stripping prime powers is not an encoding
into a single smaller totient fiber. The established reduction regroups
these inputs by divisor outputs and loses a factor bounded by the divisor
count. It provides no simultaneous quantitative guarantee of a retained
large fiber and an output small enough to increase the exponent.

The new subpower bound on the common radical addresses a size component,
not this common-output and multiplicity-retention issue. In particular,
repeating padding and stripping has not been shown to yield successive
exponent improvements. This is not an impossibility theorem for refined
selections or other encodings.

`Submission/Spec.lean` is still unchanged with its original sorry. There is
no complete proof or disproof ready for submission.

## Dense-product divisor entropy: the stripping loss is now quantified

New completed file `Submission/DenseDivisorEntropy.lean` (194 lines),
importing `DensePredecessorSupport`. It compiles without diagnostics and
has a fresh olean. `DenseDivisorEntropyCheck.lean` checks all eight theorem
and lemma types and their axioms; only `propext`, `Classical.choice`, and
`Quot.sound` occur. No source sorry or added axiom.
Namespace: `Erdos821.DensePredecessors`.

The general finite result `log_card_divisors_le_support` is

    log(tau(n)) <= omega(n)*log(A) + log(n)/(A*log(2)),
    n>0, A>=1.

Here omega is the number of distinct prime factors and tau the divisor
count (not the higher-divisor function). The proof uses
log(v+1)<=log(A)+v/A and sum_q nu_q(n)<=log(n)/log(2).

Also proved `log_predecessorProduct_upper`:

    log(N(X)) <= log(4)*X.

With X_m=2^(128*m^2), N_m=predecessorProduct(X_m), and A=m^3, the new
explicit estimate `scaled_log_divisors_bound` gives, for m>=1,

    m^2*log(tau(N_m))/X_m
      <= 12*cofactorSieveConstant/sqrt(m)
         +24*m^3*(1/2)^m+2/m.

`tendsto_scaled_log_divisors` proves that the left side tends to zero.
`eventually_divisors_le_exp_prime_scale` exports, for every epsilon>0,

    eventually m: tau(N_m) <= exp(epsilon*X_m/m^2).

Thus the divisor-indexed regrouping loss for this FULL dense product is
subexponential on the scale X/log X, not merely subpower relative to N.
This quantitatively resolves that particular loss term left open in the
preceding stripping review. It does not by itself select a divisor output
with both a specified size and a specified fiber count; those properties
must still be assembled if used.

The overall amplification gap is unchanged. The full-pool construction's
explicit independent choices have logarithm on the scale pi(X), whereas
log(N) has scale X. The new entropy estimate does not turn this lower
construction into a fixed positive multiplicity exponent, let alone
exponents approaching one. No upper bound on the FULL g(N) is inferred.

No complete proof or disproof exists in this development.
`Submission/Spec.lean` is unchanged with its original sorry and SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No verification submission was made. There is no pending repair in the
new proof file; the temporary API probe has been removed.

## Comparable selected outputs via complementary prime subsets

New completed file `Submission/DenseComplementFibers.lean` (156 lines),
importing `DenseDivisorEntropy` and `SquarefreeInput`. It compiles cleanly,
has a fresh olean, and has a clean `DenseComplementFibersCheck.lean` audit
of all eight theorem/lemma types and axioms. Only the allowed three axioms
occur. There is no source sorry or added axiom.
Namespace: `Erdos821.DensePredecessors`.

For a finite prime pool P, define predProduct(P)=product_{p in P}(p-1)
and subsetPredFiber(P,d) as the subsets T of P with predProduct(T)=d.
The product of the primes in T injects this restricted fiber into the
squarefree totient fiber at d.

Complementation T |-> P minus T injects the restricted fiber at d>0 into
the restricted fiber at predProduct(P)/d. Choosing a largest restricted
fiber, and replacing it by its complementary fiber when necessary, proves
`exists_large_complementary_squarefree_fiber`:

    exists d dividing N=predProduct(P),
      N <= d^2,
      2^#P <= tau(N)*gSquarefree(d).

This does not assume a complement symmetry for ALL squarefree preimages;
only the explicitly restricted prime-subset fibers have that symmetry.

The dense-pool specialization is combined with the two preceding files.
`eventually_dense_complementary_fiber` proves that for every epsilon,eta>0,
eventually in m there is a divisor d of N_m=predecessorProduct(X_m), where
X_m=2^(128*m^2), with

    N_m <= d^2,
    rad(d) <= d^epsilon,
    2^pi(X_m) <= exp(eta*X_m/m^2)*gSquarefree(d).

The radical inequality uses rad(d)<=rad(N_m), the subpower radical bound
at exponent epsilon/2, and N_m<=d^2. The multiplicity inequality uses the
new divisor-entropy estimate. Since d divides positive N_m, also d<=N_m.

### What this resolves and what it does not

For this FULL dense-product construction, the comparable selected-output
size and divisor-regrouping-loss issues are now positively resolved. The
earlier cautions remain applicable to arbitrary sparse prime-subset
families, not as a denial of this new theorem.

The original exponent gap remains. The explicit count supplied by all
prime-subset choices has logarithm of order pi(X), while the selected d
now has logarithm of order X. This construction therefore still supplies
only a subpower-in-d count, not exponents approaching one. This observation
is NOT an upper bound on the actual gSquarefree(d) or g(d).

`Submission/Spec.lean` is unchanged with its original sorry and SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof or disproof is ready to submit. There is no pending proof
repair in the new file.

## Closed-support padding at the selected output's scale

Completed `Submission/ClosedSupportPadding.lean` (204 lines, 13 audited
lemma/theorem declarations) and `Submission/ClosedSmoothFibers.lean`
(161 lines, three audited declarations). Both compile cleanly and have
fresh oleans. Their corresponding `...Check.lean` files check the exact
types and axioms; only `propext`, `Classical.choice`, and `Quot.sound` occur.
No source sorry, added axiom, or pending Lean repair.

Namespace: `Erdos821.ClosedPadding`.

For a finite prime set C, put

    primeProduct(C) = product_{p in C} p,
    predProduct(C) = product_{p in C} (p-1) = phi(primeProduct(C)).

The closure hypothesis is primeFactors(predProduct(C)) subset C.
`union_mem_admissible` proves that adjoining C to an admissible support
for n gives an admissible support for n*predProduct(C). The map

    S |-> (S intersect C, S union C)

is injective, giving the finite inequality
`multiplicity_padding_bound`, for n>0:

    g(n) <= 2^#C * g(n*predProduct(C)).

This works for the full g, not just squarefree inputs. It does not assert
unrestricted monotonicity under divisibility. If primeFactors(n) subset C,
`padded_output_structure` proves, with N=n*predProduct(C):

    n <= N <= n*primeProduct(C),
    rad(N) <= primeProduct(C),
    phi(rad(N)) | N.

The exact real exponent budget is `padding_power_bound`:

    gamma>=0,
    (1+eta)*gamma+eta <= alpha,
    primeProduct(C) <= n^eta,
    n^alpha < g(n)
      ==> N^gamma < g(N).

Thus a subpower core preserves any strictly smaller input exponent. It
has not been shown to increase the exponent. `primesBelow_closed` supplies
the closure hypothesis for C=primesBelow(y), and
`primeProduct_primesBelow_le` gives the crude but sufficient bound
primeProduct(C)<=B^y when 1<=B and y<=B.

### Quantitative preservation in the smooth-prime construction

`small_core_fibers_of_weak_density` retains the selected output n from the
old weak dyadic smooth-prime construction. Under that same supply
hypothesis for t>=6, for every r and N it gives n,y with

    N<n,
    n^(2/t)<g(n),
    primeFactors(n) subset primesBelow(y),
    primeProduct(primesBelow(y))^r <= n.

The last inequality is relative to the SELECTED n, not the full dense
predecessor product. It uses `CommonCore`'s explicit dyadic bound and the
actual lower bound n>=2^(k-1) from `SmoothInputFamilies`.

`exists_closed_small_radical_fiber_of_weak_density` then proves, for every
0<=gamma<2/t and every r,N, that some n satisfies

    N<n,
    n^gamma<g(n),
    rad(n)^r<=n,
    phi(rad(n))|n.

The unconditional `exists_fixed_power_closed_small_radical_fibers` uses the
established weak smooth-prime supply and gamma=1/t. It says:

    exists delta in (0,1), forall r,N, exists n>N,
      n^delta<g(n) and rad(n)^r<=n and phi(rad(n))|n.

This positively resolves the previously pending question of arranging a
fixed positive multiplicity exponent together with closed output support
and arbitrarily small radical at the selected output's own scale. It does
NOT prove exponents approaching one. The construction preserves every
strictly smaller exponent than its existing 2/t input bound; no
exponent-increasing operation was obtained.

## Small-radical intermediate values: a restricted two-step bound

Completed `Submission/SmallRadicalMiddleFibers.lean` (93 lines, four audited
declarations), with fresh olean and a clean type/axiom audit. Namespace:
`Erdos821.RadicalLift`. Only the three permitted axioms occur.

`card_le_of_bounded_radical` and its real-valued version formalize the
previously noted radical-map injection: a fixed totient fiber contains at
most R inputs m with rad(m)<=R. The injection goes into the integers in
[1,R], not into all numbers with bounded radical. In particular,
`small_radical_first_fiber_card_le` gives

    #{m: phi(m)=n, rad(m)<=n^eta} <= n^eta.

This is not in conflict with the new structured-output construction:
small radical of the OUTPUT n is distinct from small radical of the
PREIMAGES m in its fiber.

`eventually_small_radical_second_le` proves, for a>=0, epsilon>0,

    eventually g(n)<=n^a
      ==> eventually
        #{m: phi(phi(m))=n, rad(phi(m))<=n^eta}
           <= n^(a+eta+epsilon).

The proof uses the exact restricted fiber recurrence, the cardinality
bound above, and the previously established uniform input-size estimate
m<=n^(1+delta) within a one-step fiber. It is only a bound for this
restricted two-step family under an eventual one-step upper bound. It is
not an impossibility theorem for every possible lifting/encoding scheme
and is not a disproof of Erdős 821.

### Current state after this continuation

The original conjecture remains UNSOLVED. `Submission/Spec.lean` was not
changed and still has its original sorry, with SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof or disproof is ready for submission. The three new
source files and their audits are complete; no temporary proof probe,
pending Lean repair, or background process remains. Probes in /tmp were
API lookups only.

The genuinely missing step remains an exponent increase or an independent
arithmetic input giving arbitrary-root smooth shifted-prime abundance.
Do not claim that closed support and small radicals themselves supply
that step; the exact verified padding budget preserves exponents only.

## Divisor-order constants: exact factorial normalization of the rough main term

Completed `Submission/MomentOrderConstants.lean` with seven audited
lemma/theorem declarations, a clean build, fresh olean, and the exact-type
and axiom audit `Submission/MomentOrderConstantsCheck.lean`. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. Namespace:
`Erdos821.HigherDivisors`. No source sorry or pending Lean repair.

The source proves:

* `factorial_rankin_coefficient_le`, for k>=1:

      k! * (e/k)^k <= e*k.

  This uses the upper bound from monotonicity of Mathlib's Stirling
  sequence. It does not replace the factorial by the much weaker k^k.

* `tendsto_polynomial_eulerCost_geometric`, for any fixed natural d and
  0<=rho<1:

      k^d * eulerCost(k) * rho^k -> 0.

* `tendsto_factorial_rough_coefficient`:

      k*k!*(e/k)^k*eulerCost(k)*rho^k -> 0.

* `exists_order_rough_coefficient_lt_factorial`: for any real constant C,
  any 0<=rho<1, and any prescribed B, some k>B with k>=2 satisfies

      C*k*(e/k)^k*eulerCost(k)*rho^k < 1/k!.

* `tendsto_symmetrized_cutoff_ratio`, for 0<=theta<rho and rho>0:

      (k+1)*(theta/rho)^k -> 0.

  Thus merely choosing a distinguished factor in k+1 ways does not
  repair a fixed exponential loss from a smaller logarithmic cutoff.
  This is a coefficient comparison, not a theorem excluding every
  symmetric hyperbola decomposition or every possible moment method.

The actual finite Rankin/rough-sieve normalization is also connected:
`rough_sieve_main_le_normalized` assumes k>=2, K>1, L>0, kappa>0,

    log K + k <= rho*L,
    kappa*L <= J*log 2.

It bounds the existing rough-sieve main expression

    k * 16X/(J log 2)^2 * eulerCost(k)*H_k(K)

by

    [16/kappa^2 * k*(e/k)^k*eulerCost(k)*rho^k] * X*L^(k-2).

Consequently `exists_order_rough_main_lt_factorial`, for fixed
0<=rho<1 and kappa>0, chooses an arbitrarily large order k, uniformly
before the scale parameters, such that this main expression is less
than

    X*L^(k-2)/k!

at every positive scale satisfying those explicit cutoff conditions.
This is only the MAIN expression. The finite rough-prime theorem also
has its separately displayed sieve remainder. No total shifted-prime
moment lower bound has been asserted or proved here.

### What this continuation establishes and leaves open

The desired all-order coefficient comparison is favorable: the existing
subexponential Euler cost and sharp-order Rankin constant really can
be dominated by a fixed geometric saving, after normalization by a
factorial-scale moment. The arithmetic lower bound for the TOTAL
shifted-prime moments remains unproved. The fixed-modulus pole result
only yields arbitrarily large fixed multiples of X/log X, and the
truncated progression lower estimate still has the theta^k loss.
Neither result may be silently substituted for a factorial-scale
all-order lower bound.

`Submission/Spec.lean` is unchanged with its original sorry and SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
The original conjecture remains UNSOLVED. No complete proof or disproof
is ready for submission. The new file and its audit are complete, with
no pending Lean repair or background process. The /tmp API probe was
removed.

## Complete conditional transfer from sharp moments to Erdős 821

Completed `Submission/MomentSmoothTransfer.lean` (353 lines), importing
`MomentOrderConstants` and `HigherDivisorSubpower`. It compiles cleanly,
has a fresh olean, and `MomentSmoothTransferCheck.lean` audits all fifteen
lemma/theorem declarations plus the exact definition of the remaining
hypothesis. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
There is no source sorry, extra axiom, or pending Lean repair.
Namespace: `Erdos821.HigherDivisors`.

Use the explicit scales

    X(t,L) = 2^(128*t*L),
    K(t,L) = 2^(128*(t-1)*L),
    Y(L)   = 2^(128*L),
    J      = L.

For t>=1, X=K*Y and Y=(2^(64L))^2. The finite partition lemma
`moment_le_rough_add_pool_card` keeps the smooth-prime cardinality and
its weight bound explicit.

### The sieve remainder is now included

`eventually_momentSieveError_le` proves, for fixed k,t with t>=1 and any
c>0,

    eventually L:
      k*(2^(64L)+2^(16L)+1)*K(t,L)*harmonic(K(t,L))^(k-1)
        <= c*X(t,L).

It uses harmonic(K)<= (128t+1)(L+1) and the existing elementary fact that
fixed polynomials are eventually below 2^L. Constants are allowed to
depend on the fixed divisor order; no uniform-in-k limit is claimed.

`exists_order_eventually_rough_le` chooses the order before the scale:
for every t>=2, there is k>=2 such that eventually L,

    roughPrimeMoment(k,X(t,L),Y(L))
      <= X(t,L)*(log X(t,L))^(k-2)/(2*k!).

This is the FULL rough moment, not merely its main expression. It combines
the previous coefficient theorem at rho=1-1/(2t) and kappa=1/(128t),
with the remainder estimate above. The logarithmic cutoff condition holds
for L>=k. No shifted-prime total lower bound is used in this theorem.

### Removing the fixed-order weights

`exists_moment_weight_bound` uses the already proved subpower bound on
tau(k,n), with exponent 1/(2t), to give a constant C>=1 such that

    n<=X(t,L) ==> tau(k,n)<=C*2^(64L).

The exact identity X(t,L)^(1/(2t))=2^(64L) is separately verified.

Given the eventual rough-moment estimate,
`eventually_smooth_count_of_moment_lower` proves eventually L the explicit
IMPLICATION

    X(t,L)*(log X(t,L))^(k-2)/k! <= shiftedPrimeMoment(k,X(t,L))
      ==> # {p<=X(t,L) prime : p-1 is Y(L)-smooth} >= K(t,L).

The positive gap beats the weight loss because
2*C*k!<2^(64L) eventually. The large-scale condition and the total moment
hypothesis are not omitted.

### Exact remaining arithmetic hypothesis

The new Prop definition `SharpDyadicMomentLower` is:

    forall k>=2, forall t>=2, forall M,
      exists L>=M,
        X(t,L)*(log X(t,L))^(k-2)/k!
          <= shiftedPrimeMoment(k,X(t,L)).

THIS PROP IS NOT PROVED OR ADDED AS AN AXIOM. It is a cofinal lower bound
for each fixed k,t, not a claim uniform in growing divisor order.

`dyadic_smooth_density_of_sharp_moments` derives the strong smooth-prime
supply used in `Work.lean`, retaining the quantifier order. Finally:

    erdos_821_of_sharp_dyadic_moments
        (H : SharpDyadicMomentLower) : original_conjecture

is a complete CONDITIONAL implication. The former informal assertion that
sharp factorial-scale moments suffice is now implemented through the full
sieve error, deweighting, cofinal scale choice, and multiplicity transfer.
It is not an unconditional settlement.

### Current state

The original conjecture remains UNSOLVED. The missing arithmetic theorem
is now an exact, sufficient Prop above; neither the fixed-modulus pole
result nor the truncated weighted-progression lower bound proves it.
Do not instantiate it without an actual proof, or present the conditional
`erdos_821_of_sharp_dyadic_moments` as the requested theorem.

`Submission/Spec.lean` is unchanged, with its original sorry and SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof/disproof is ready to submit. No pending Lean repair,
unfinished auxiliary theorem, or background process remains. The API
probe in /tmp was removed.

## Recheck of the signed arithmetic input after the sharp-moment transfer

This continuation inspected the actual prime/progression estimates and the
finite partition certificates. No new arithmetic estimate or Lean theorem
was obtained, and no auxiliary proof repair was started.

The unconditional composite distribution result is for the special
`primeProductModuli r m` families and requires `2*r+1<=t`. It is not a
higher-divisor-weighted discrepancy estimate over all d up to a cutoff.
The earlier cofinal signed-deficit route uses r=t-2, so this available
range would restrict it to t<=3. The signed formulation does not extend
that range. Even a negligible error for all d<=X^theta, with fixed theta<1,
would leave the existing lower-moment transfer's theta^(k-1) loss. None of
these estimates proves `SharpDyadicMomentLower`.

The partition inference review checked the strength and scope of the
existing countermodels. The Lean-certified size-12 model already preserves
total size exactly, all single-part means, and every joint binomial moment
of selected total weight <=6 INCLUDING the half endpoint, while having no
fourth-root-smooth outcomes. The independently exactly checked finer models
at sizes 24 and 36, and the size-18 two-thirds-level model, have the scope
recorded earlier. These are finite moment-inference certificates only;
there is still no continuum/asymptotic model or theorem about actual primes.
No claim was made that they exclude every use of complete asymptotic data.

The review did not produce a replacement for the missing arithmetic lower
bound, nor a disproof of the conjecture. `Submission/Spec.lean` remains
unchanged with its original sorry and hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
The conjecture is still UNSOLVED. No complete proof/disproof is ready for
submission, and no Lean repair or background process is pending.

## Totient fibers as sparse modulus families: cofactor accounting

Completed `Submission/FiberModulusAudit.lean` (114 lines, eight audited
lemma/theorem declarations), with fresh olean and clean build. The exact-type
and axiom audit is `Submission/FiberModulusAuditCheck.lean`; only `propext`,
`Classical.choice`, and `Quot.sound` occur. Namespace:
`Erdos821.FiberModuli`. No source sorry, added axiom, or pending repair.

This investigation tested a different possible bootstrap: use a large
root-smooth totient fiber F as a sparse family of moduli for p=am+1.
For phi(m)=n throughout F, the exact progression main term is

    sum_{m in F} 1/phi(m) = #F/n.

`progression_total_lower` specializes the already proved finite composite
progression estimate to this common denominator, keeping the entire
conductor error explicit. No improved sparse-modulus discrepancy or
large-sieve estimate was obtained.

### The apparent exponent gain omitted the cofactor cost

If #F is on the scale Q^alpha, its moduli are near Q, and primes are sought
up to Q^beta (beta>1), an ideal progression main count would have scale
Q^(alpha+beta-1). Even ignoring every incidence overcount and logarithmic
loss, the cofactor a can be as large as Q^(beta-1). The corresponding
smooth-prime transfer budget is

    (alpha+beta-1)/beta - (beta-1)/beta = alpha/beta < alpha

for alpha>0. This exact algebra and its strict inequality are verified.
The initially tempting choices beta=1+alpha and beta=2-alpha therefore
DO NOT yield an improvement once the cofactor smoothness cutoff is charged.
No improved exponent was ever proved or should be inferred from the ideal
incidence count alone.

If the cofactors additionally have a relative smoothness exponent u, the
idealized budget becomes

    [alpha+(1-u)*(beta-1)]/beta.

`controlled_cofactor_improves_iff` proves that this exceeds alpha exactly
when u<1-alpha. This does NOT assert that such cofactors fail to exist, or
that primes with such cofactors cannot be counted. It identifies the
additional arithmetic estimate required by this version of the bootstrap;
ordinary unweighted progression abundance alone does not supply it.

### Common totients do not imply improved minimum Farey separation

`exists_fiber_with_close_reduced_fractions` proves that for every B there
are n>B and distinct coprime squarefree d,e in the ACTUAL totient fiber of n,
and reduced fractions a/d,b/e in (0,1), with

    0 < |a/d-b/e| = 1/(de) <= 1/n^2.

The construction uses the previously proved arbitrarily large primitive
semiprime collision outputs and `exists_reduced_fractions_exact_gap`.
This only rejects an automatic improvement of minimum separation based
solely on equal totients. It does not reject average-spacing estimates,
local-density bounds, or estimates for specially selected polynomially
large fibers; no such estimates were proved in this continuation.

### Current state

The sparse-modulus investigation did not produce a multiplicity exponent
increase or a new prime-distribution theorem. The original conjecture is
still UNSOLVED. `Submission/Spec.lean` remains unchanged with its original
sorry and hash
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No proof/disproof is ready to submit. The new file and its audit are
complete, with no pending Lean repair or background process.

## Smooth predecessor products: finite transfer and a local obstruction

Completed and audited:

- `Submission/SmoothPredecessorProducts.lean` (namespace
  `Erdos821.PredecessorProducts`);
- `Submission/SmoothPredecessorProductsCheck.lean`;
- fresh olean `.lake/build/lib/lean/Submission/SmoothPredecessorProducts.olean`;
- build and audit logs `/tmp/SmoothPredecessorProducts.log` and
  `/tmp/SmoothPredecessorProductsCheck.log`.

The source compiles cleanly. The exact-type checks pass, and all ten theorem
axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`.

### Counting and smoothness are valid, but require surviving prime pairs

For a finite set `E` of positive ordered pairs, `productImage E` is the set
of products `a*b`. Its fiber at `n` injects into `n.divisors` by the first
coordinate. Consequently the file proves:

```
#E <= sum_{n in productImage(E)} #divisors(n).
```

If the divisor counts on that image are at most `D`, this gives
`#E <= D * #productImage(E)`.

`primePairs E` filters the pairs by primality of `a*b+1`; `primeImage E`
is the set of those prime successors. Successor is injective, and therefore

```
#primePairs(E) <= D * #primeImage(E)
```

under the corresponding divisor-count bound. Crucially, the left-hand side
is **not** `#E`.

The root improvement is also proved. If `a,b` are `y`-smooth, `Q<=a,b`, and
`y^r<=Q`, every prime factor `q` of `a*b` satisfies `q^(2*r)<=a*b`.
**Assuming** `a*b+1` prime, it is a member of
`rationalSmoothShiftedPrimes (2*r) 1`. The same statement is proved for
all members of `primeImage E`.

### The unrestricted pool-to-prime assertion is false

`finite_pool_counterexample` gives the explicit pool `{12,162}`:

- both numbers are 4-smooth;
- both successors, 13 and 163, are prime;
- no pair in the Cartesian square has a prime product successor.

The obstruction is exact, not numerical: both predecessors are 2 modulo 5,
so every product successor is divisible by 5 and exceeds 5. The general
modulo-5 obstruction is a separate lemma.

This finite example rejects an **unqualified assertion about arbitrary
pools**, not an asymptotic statement with adequate local admissibility.
Neither the image-size bound nor the smoothness bound supplies the missing
prime-surviving pair count. Imposing primality merely moves the unresolved
shifted-smooth-prime problem into that count.

### Current state

No new unconditional multiplicity exponent or complete settlement results
from this product investigation. `Submission/Spec.lean` is unchanged and
still contains its original `sorry`; SHA-256 remains
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
There is no pending Lean proof repair or background process.

## Exact symmetric higher-divisor hyperbola decompositions

Completed and audited `Submission/SymmetricDivisorHyperbola.lean`, in
namespace `Erdos821.HigherDivisors`, with corresponding
`Submission/SymmetricDivisorHyperbolaCheck.lean`. The source compiles cleanly
and has a fresh olean. All sixteen theorem axiom audits report only the
permitted axioms. Logs:

- `/tmp/SymmetricDivisorHyperbola.log`
- `/tmp/SymmetricDivisorHyperbolaCheck.log`

### One large factor, with the remainder retained

`lowZeta H` is the zeta arithmetic function truncated to inputs at most H;
`highZeta H` is its complementary truncation. Their sum is zeta. The file
proves:

- equality of convolution powers below a cutoff when the base functions
  agree below that cutoff;
- `(lowZeta H)^k(n)=tau(k,n)` for n<=H;
- `(highZeta H)^k(n)=0` for n<(H+1)^k;
- the necessary evaluated binomial and convolution identities.

The main exact decomposition, for n<(H+1)^2, is:

```
tau(k+1,n) = (lowZeta(H)^(k+1))(n)
             + (k+1) * sum_{d|n, H<n/d} tau(k,d).
```

Thus the factor k+1 from distinguishing the unique large factor is valid.
The all-small-factor term is nonnegative, but is not zero in general and
cannot be deleted from an equality.

`lowZeta_pow_eq_zero_of_large_prime` proves this remainder vanishes if n
has a prime factor greater than H. Consequently it vanishes for n outside
`Nat.smoothNumbers (H+1)`, and there is a separate exact rough-input formula.
This is a support statement, NOT a lower bound for prime-weighted sums of
the all-small-factor remainder.

### Balanced blocks keep the complementary weight

`tau_balanced_hyperbola` is the second exact identity:

```
tau(2*k,n)
  = 2 * sum_{d|n, d<n/d} tau(k,d)*tau(k,n/d)
    + sum_{d|n, d=n/d} tau(k,d)*tau(k,n/d).
```

The proof uses the swap involution on divisor pairs, retaining the diagonal.
The right side is NOT an unweighted progression sum: it retains the
cofactor-dependent weight `tau(k,n/d)`. Nothing in this file supplies the
prime/cofactor-weight correlation needed to evaluate that sum. Enumerating
possible balanced groupings is not a justification for inserting an extra
binomial gain without accounting for overlap.

### Factorial normalization after symmetrization

The coefficient from a cutoff X^theta, even after the valid k+1 symmetry
factor, is `(k+1)*theta^k/k!` at moment order k+1. Its ratio to the required
sharp factorial coefficient is exactly `(k+1)^2*theta^k`.

`tendsto_symmetrized_factorial_coefficient` proves this ratio tends to zero
for each fixed 0<=theta<1. The exported eventual strict inequality makes it
smaller than ANY fixed positive multiple of `1/(k+1)!` at large k.

This is a precise limitation of this truncated lower coefficient, not an
impossibility theorem for other moment methods. It does not estimate the
weighted progression discrepancy, the all-small-factor remainder, or the
balanced cofactor correlation. The full original conjecture remains open
in this development; the conditional theorem from `SharpDyadicMomentLower`
remains conditional.

### Current state

No pending Lean repair or background process remains. No new unconditional
multiplicity exponent was obtained. `Submission/Spec.lean` is unchanged
with its original `sorry`, SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
There is still no valid proof or disproof to submit.

## Cofactor-weighted moments: exact product-modulus reindexing

The latest continuation inspected the actual Type II and hyperbolic large
sieve statements. `adaptive_hyperbolic_large_sieve_nat` bounds sums of
`a(m)*b(n)*chi(m*n)` (with hyperbolic cutoffs). Its arbitrary coefficient
norms do not turn it directly into a lower estimate for
`tau(r,d)*tau(s,m)*Lambda(d*m+1)`. The shift and the cofactor-dependent
weight remain an arithmetic correlation to estimate. This observation does
not rule out a genuinely new bilinear or dispersion estimate.

Completed `Submission/CofactorMomentSwitching.lean`, namespace
`Erdos821.HigherDivisors`, with clean build, fresh olean, and audit file
`Submission/CofactorMomentSwitchingCheck.lean`. All twelve theorem audits
use only `propext`, `Classical.choice`, and `Quot.sound`.

Logs: `/tmp/CofactorMomentSwitching.log` and
`/tmp/CofactorMomentSwitchingCheck.log`.

### Exact cofactor expansion

Define

```
cofactorMangoldtMoment(k,d,X)
  = sum_{n<=X, d|(n-1)} Lambda(n)*tau(k,(n-1)/d).
```

The n=1 term is zero because Lambda(1)=0. For d>0 the exact identity is

```
cofactorMangoldtMoment(k+1,d,X)
  = sum_{e<=X/d} tau(k,e)*psi(X;d*e,1).
```

Thus expanding the complementary divisor weight changes the progression
modulus from d to d*e, with the product potentially as large as X. A
truncation e<=T<=X/d gives a lower bound, not an equality for the full weight.
Both statements are proved, including all finite endpoint conditions.

### Aggregation, with its actual modulus range

Define the real-valued arithmetic function

```
truncatedConvolution(r,s,Q) = shortPart(zeta^r,Q) * zeta^s,
```

where multiplication is Dirichlet convolution. For Q<=X:

```
sum_{d<=Q} tau(r,d)*cofactorMangoldtMoment(s+1,d,X)
  = sum_{m<=X} truncatedConvolution(r,s,Q)(m)*psi(X;m,1).
```

Its coefficients are nonnegative and bounded by tau(r+s,m), and equal that
full divisor weight when m<=Q. Consequently the reindexed absolute
progression error is bounded by `divisorProgressionError (r+s) X X` — a
**full-range**, not below-square-root, discrepancy. No small upper bound
for that discrepancy was proved or assumed.

When Q=X, a further exact identity shows that the cofactor sum is simply
`shiftedMangoldtMoment (r+s+1) X`. Reorganizing it therefore returns the
original higher moment rather than furnishing the missing lower estimate.

### Current state

No new unconditional multiplicity exponent or complete settlement results.
`Submission/Spec.lean` remains unchanged with the original `sorry` and
SHA-256 `8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
There is no pending Lean repair or background process. Do not submit the
conditional sharp-moment transfer or these finite reindexings as a proof of
the conjecture.

## Full-range absolute progression errors have a linear obstruction

New unconditional arithmetic result, rather than just a reindexing:
`Submission/FullRangeProgressionError.lean`, namespace
`Erdos821.FullRangeError`, compiles cleanly, has a fresh olean, and passes
`Submission/FullRangeProgressionErrorCheck.lean`. All thirteen theorem
axiom audits use only the permitted axioms. Logs:

- `/tmp/FullRangeProgressionError.log`
- `/tmp/FullRangeProgressionErrorCheck.log`

### Exact large-modulus behavior

For 0<d<X<=2d,

```
psi(X;d,1) = Lambda(d+1).
```

The only other candidate is 1, whose Mangoldt weight is zero. For a finite
pool of such moduli with d+1 even, the total actual progression weight is
at most

```
characterLiftError(2,X) = floor(log_2 X)*log 2.
```

This follows by an injective successor map into the non-coprime-to-2
Mangoldt sum, retaining all powers-of-2 contamination rather than claiming
that every even candidate is nonprime-power.

### A quantitative full-range lower bound

Take X=4N and the N moduli

```
d_j = 2N+2j+1,  0<=j<N.
```

They are odd and greater than X/2. Since phi(d)<=X, their combined expected
weight is at least psi(X)/4. Therefore, for N>0,

```
psi(4N)/4 - characterLiftError(2,4N)
  <= divisorProgressionError(1,4N,4N).
```

Every positive divisor order has weight tau(k,d)>=1 on d>=1, so its full
absolute discrepancy is at least the order-one discrepancy.

`eventually_full_error_ge_psi` proves, UNIFORMLY for all k>=1, eventually
at X=2^(L+2):

```
psi(X)/8 <= divisorProgressionError(k,X,X).
```

The initial proof uses the elementary dyadic Mangoldt lower bound and
exponential domination of a quadratic to absorb prime-power contamination.
The file also exports the explicit X/[32*(L+2)] lower bound and the eventual
strict inequality exceeding X/(L+1)^2.

Finally `eventually_full_error_ge_linear` applies the earlier genuine
linear Chebyshev bound at `progressionScaleN s = 2^(64*s)` and proves:

```
eventually s, for EVERY k>=1:
  progressionScaleN(s)/64
    <= divisorProgressionError(k,progressionScaleN(s),progressionScaleN(s)).
```

Thus a full-range absolute discrepancy o(X), or one with every fixed
logarithmic saving, is **false**, not merely unproved. This rules out
silently feeding such an estimate into the full cofactor expansion.

### Scope and current state

This result concerns the ALL-modulus cutoff Q=X. It does not rule out
absolute errors at Q=X^theta for fixed theta<1, does not rule out signed
cancellation, and does not disprove `SharpDyadicMomentLower` or Erdős 821.
For higher orders it does not by itself rule out errors small compared to
X*(log X)^(k-1); the exported lower bound is linear in X, not that stronger
weighted scale.

No complete proof or disproof of the original conjecture has been found.
`Submission/Spec.lean` remains unchanged with its original `sorry` and
SHA-256 `8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No proof repair or background process is pending.

## Weighted full-range error: logarithmic order of the odd-modulus obstruction

Three new files compile cleanly, have fresh oleans, and have corresponding
`...Check.lean` exact-type/axiom audits:

- `Submission/OddHarmonicMoments.lean` (5 theorems), namespace
  `Erdos821.HigherDivisors`;
- `Submission/OddIntervalDivisorMoments.lean` (4 theorems), namespace
  `Erdos821.FullRangeError`;
- `Submission/WeightedFullRangeError.lean` (10 theorems), same namespace.

All nineteen audited declarations depend only on the permitted axioms.
Build and audit logs have the corresponding names under `/tmp`.

### Odd harmonic moments

Define

```
oddHarmonicMoment(k,A) = sum_{1<=n<=A, n odd} tau(k,n)/n.
```

The decomposition n=2^a*b with b odd is injective. Multiplicativity of tau
and the exact binomial-geometric series

```
sum_{a>=0} tau(k+1,2^a)/2^a = 2^(k+1)
```

give

```
harmonicMoment(k+1,A) <= 2^(k+1)*oddHarmonicMoment(k+1,A).
```

Combining this with the earlier factorial lower bound, including order 0,
proves for A>=1:

```
log(A+1)^k/(2^k*k!) <= oddHarmonicMoment(k,A).
```

### Divisor weight in the large odd interval

For odd e>0 and 2e<=N, an explicit injective progression of odd multiples
proves

```
N <= 4e * #{d in oddLargeModuli(N) : e|d}.
```

Here `oddLargeModuli(N)` is exactly the odd integers strictly between 2N
and 4N. Weighted divisor incidence and tau's convolution recurrence then
give, whenever 2T<=N,

```
(N/4)*oddHarmonicMoment(k,T)
  <= sum_{d in oddLargeModuli(N)} tau(k+1,d).
```

These are integer estimates, not lower bounds for shifted primes.

### The full error with weights retained

With an explicit bound `tau(k+1,d)<=B` on the odd interval, the finite
inequality is

```
(psi(4N)/16)*oddHarmonicMoment(k,T)
  - B*characterLiftError(2,4N)
    <= divisorProgressionError(k+1,4N,4N).
```

On `X_s=progressionScaleN(s)=2^(64s)`, the fixed-order divisor subpower
bound gives a global weight bound `tau(k+1,d)<=C(k)*2^s` for d<=X_s. The
weighted powers-of-2 contamination is negligible compared with any fixed
positive multiple of X_s. Taking the odd harmonic cutoff T=2^(32s) and
using the linear Chebyshev bound therefore proves:

```
for each fixed k>=0, exists c_k>0, eventually s:
  c_k * X_s * (log X_s)^k
    <= divisorProgressionError(k+1,X_s,X_s).
```

Both the scale-s and logarithmic versions are exported. There is also an
explicit theorem negating little-o of `X_s*(log X_s)^k` for this error.
Constants and eventual thresholds may depend on k; no uniform-in-order
natural-scale lower bound is asserted.

### Crucial distinction: one logarithm is still missing for the sharp transfer

At discrepancy order k+1, the harmonic main term used to transfer to the
shifted-prime moment of order k+2 is `X*(log X)^(k+1)`. The new obstruction
has size `X*(log X)^k`, ONE LOGARITHMIC FACTOR SMALLER.

Accordingly this does NOT rule out an error o(`X*(log X)^(k+1)`), and does
NOT refute the sharp-moment hypothesis. It strengthens the prior linear
obstruction at the summatory-divisor scale but is not a proof that every
full-range absolute-error approach must fail at the scale actually needed
by the moment transfer. Signed cancellation and shorter-range estimates
are likewise not ruled out.

### Current state

The original conjecture remains unsolved. `Submission/Spec.lean` is unchanged
with the original `sorry`, SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No new unconditional multiplicity exponent was obtained. There is no pending
Lean repair or background process, and no valid settlement to submit.

## Central-binomial Mangoldt lower bound above the half threshold

Completed and compiled `Submission/BinomialMangoldtLower.lean`, with exact-type
and permitted-axiom checks in `Submission/BinomialMangoldtLowerCheck.lean`.
Namespace: `Erdos821.AnalyticSieve`.

* `log_choose_le_mangoldt N K hN` proves `log (choose N K) ≤ mangoldtSum N`
  for positive N. Prime powers from the binomial coefficient's factorization
  inject into the prime powers up to N, using
  `Nat.pow_factorization_choose_le`; their Mangoldt weights sum to its log.
* `central_binomial_mangoldt_lower m hm` proves
  `2*m*log 2 - log (2*m) ≤ mangoldtSum (2*m)`.
* `dyadic_binomial_mangoldt_lower r hr` gives
  `(2^r-r)*log 2 ≤ mangoldtSum (2^r)` for r≥1.
* `eventually_dyadic_mangoldt_five_eighths` gives eventually
  `(5/8)*2^r ≤ mangoldtSum (2^r)`.

The proof uses the central binomial coefficient lower bound and elementary
exponential-versus-polynomial growth, not the prime number theorem.
Build and audit logs: `/tmp/BinomialMangoldtLower.log` and
`/tmp/BinomialMangoldtLowerCheck.log`. All four declarations use only
`propext`, `Classical.choice`, `Quot.sound`.

This repairs the two errors recorded in the latest context summary. It is
only groundwork for the proposed relative full-range error reduction; it
does not establish that error estimate or the original conjecture.
`Submission/Spec.lean` remains unchanged, with the original `sorry`.

## Full-range relative discrepancy: complete conditional transfer

Completed and cleanly compiled:

* `Submission/RelativeDiscrepancyTransfer.lean`
* `Submission/RelativeDiscrepancyTransferCheck.lean`

Namespace: `Erdos821.HigherDivisors`. All eight audited declarations use only
`propext`, `Classical.choice`, `Quot.sound`. Logs are in `/tmp/` with the
corresponding base names. The implementation imports the completed
binomial-Mangoldt lower bound and the prior sharp-moment transfer.

### Unconditional preliminary estimates

`eventually_nonprimeMangoldtMoment_le_linear k c hc` proves, for every fixed
k and c>0, eventually at natural X:

    nonprimeMangoldtMoment(k+1,X) ≤ c*X.

It combines the existing O(X^(3/4)*log X) estimate with Mathlib's global
`isLittleO_log_rpow_atTop` (not in the `Real` namespace). It applies at all
large X, not only dyadic ones.

`tendsto_momentScale_exponent`, `tendsto_momentScaleX`, and
`eventually_momentScale_mangoldt_five_eighths` transfer the growth and
psi(X)≥(5/8)X bound to X=momentScaleX(t,L).

`shiftedPrimeMoment_lower_of_relative_errors r X hr hX hlog hpsi hD hN`
proves the following finite implication for r≥1 and log X≥1:

    psi(X) ≥ (5/8)*X,
    D_r(X,X) ≤ X*(log X)^r/(16*r!),
    nonprimeMangoldtMoment(r+1,X) ≤ X/(16*r!)
      ==> shiftedPrimeMoment(r+1,X)
            ≥ X*(log X)^(r-1)/(r+1)!.

The 5/8 constant leaves at least 1/2 after the two errors; 2*r!≤(r+1)!
then gives the exact desired factorial coefficient.

### The explicit, STILL UNPROVED hypothesis

    def RelativeFullRangeDiscrepancy : Prop :=
      ∀ r≥1, ∀ t≥2,
        (L ↦ D_r(X(t,L),X(t,L)))
          =o[atTop] (L ↦ X(t,L)*(log X(t,L))^r).

No theorem supplies this proposition. It is neither an axiom nor asserted
unconditionally. Constants and thresholds may depend on fixed r and t.
The existing lower obstruction at this order is only
Omega_r(X*(log X)^(r-1)); it does NOT contradict this hypothesis.

Completed conditional implications:

* `eventually_sharp_moment_of_relative_discrepancy H r t hr ht`
* `sharp_dyadic_moments_of_relative_discrepancy H`
* `erdos_821_of_relative_discrepancy H`

The last theorem has the EXACT original conjecture as its conclusion but
retains H as an explicit hypothesis. It is not an acceptable replacement
for the original `sorry` without a proof of H.

## Totient correction in a truncated harmonic main term

Completed and cleanly compiled, with corresponding exact-type and
permitted-axiom checks:

* `Submission/TotientHarmonicCutoff.lean`
* `Submission/TotientHarmonicCutoffCheck.lean`

Namespace: `Erdos821.HigherDivisors`.

Definition:

    totientHarmonicMoment(k,A) = sum_{n≤A} tau(k,n)/phi(n).

Proved for k≥1:

    totientHarmonicMoment(k,A) ≤ eulerCost(k)*harmonicMoment(k,A).

This follows by bounding n/phi(n) by its square and using the existing
squared-ratio harmonic estimate. Thus the arithmetic correction is at
most subexponential in k, uniformly in A.

With A>1 and log A+k≤theta*L, the Rankin bound gives

    totientHarmonicMoment(k,A)
      ≤ eulerCost(k)*(e/k)^k*theta^k*L^k.

For each fixed 0≤theta<1, both

    k!*eulerCost(k)*(e/k)^k*theta^k
    (k+1)!*eulerCost(k)*(e/k)^k*theta^k

converge to zero as k→infinity. The successor factorial matches the shifted
moment order in the progression transfer. Therefore retaining 1/phi(d),
instead of replacing it by 1/d, does not remove the fixed-cutoff geometric
loss in THIS truncated-main-term argument. This is not an upper bound on
the full shifted-prime moment and does not rule out other arithmetic
arguments or signed cofactor correlations.

### State after these developments

The original conjecture is still UNSOLVED. `Submission/Spec.lean` remains
unchanged with its original `sorry`, SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
There are no pending repairs or background Lean processes for the three
new result files. No unconditional multiplicity-exponent gain was obtained.
A genuine settlement still requires new arithmetic input, not just these
conditional implications or coefficient bounds.

## Coprime pairs occupy almost all of suitable full record fibers

New completed source:

* `Submission/CoprimeRecordFibers.lean` (namespace `Erdos821.CoprimeRecords`)
* `Submission/CoprimeRecordFibersCheck.lean`

Both compile cleanly, with a fresh result olean. All thirteen audited
principal lemmas/theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound`. Logs: `/tmp/CoprimeRecordFibers.log` and
`/tmp/CoprimeRecordFibersCheck.log`.

### Full restricted fibers and record divisibility

`avoidingFiber K n` is the finite set counted by the existing `gAvoiding K n`:
all squarefree m with phi(m)=n and gcd(m,K)=1. This is the entire restricted
fiber, not an arbitrarily chosen sparse subfamily.

`card_avoidingFiber_dvd_le` divides the d-divisible subfamily by d and injects
it into the restricted fiber at n/phi(d). It retains coprimality with K.

`normalized_record_core_bound` proves that at a positive-output record for
`gAvoiding K n / n^s`, for EVERY d,

    phi(d)^s * #{m in avoidingFiber K n : d|m} ≤ gAvoiding K n.

For d>0, `normalized_record_core_square_bound` consequently gives

    #{m in avoidingFiber K n : d|m}^2
      ≤ gAvoiding(K,n)^2 * phi(d)^(-2s).

No lower frequency or independence assertion is used.

### Exact-gcd counting and the summable tail

`coprimePairs K n` and `noncoprimePairs K n` partition the Cartesian square
of the full restricted fiber; `pair_card_partition` records the exact
cardinality identity.

If inputs avoid B!, a noncoprime pair has a common prime p>B, hence gcd>B.
`noncoprimePairs_le_core_sum` partitions bad pairs by their EXACT gcd d,
then bounds each gcd class by the Cartesian square of the d-divisible
subfamily. At a normalized record this gives

    #noncoprimePairs(B!,n)
      ≤ gAvoiding(B!,n)^2 * sum_{B<d≤U} phi(d)^(-2s),

where U is the maximum input in the fiber.

For s>1/2, the already proved `summable_totient_neg_rpow (2*s)` makes this
tail uniformly small in U. `exists_small_totient_tail` implements this
using `Summable.vanishing` and a finite cutoff, with no asymptotic assumption
on the distribution of primes.

### New unconditional structural conclusions

`exists_cutoff_record_coprime_proportion s eta hs heta` proves:

    for s>1/2 and eta>0, there exists a FIXED B such that EVERY
    positive-output record for gAvoiding(B!,n)/n^s satisfies

        #coprimePairs(B!,n) ≥ (1-eta)*gAvoiding(B!,n)^2.

Combine this with the existing fixed-prime-exclusion lower bound and the
normalized-record selection principle. The theorem
`exists_large_mostly_coprime_records` proves, for every

    1/2 < alpha < 1/2+1/(80000000*Sieve.totientRatioAverageConstant+10)

and eta>0, some fixed B has arbitrarily large outputs n>1 for which

    gAvoiding(B!,n) > n^alpha,
    #coprimePairs(B!,n) ≥ (1-eta)*gAvoiding(B!,n)^2.

`coprimePairs_distinct` shows every coprime pair at n>1 is off the diagonal.
Thus these are distinct primitive squarefree collisions at the SAME common
output, without first dividing the pairs by their gcd.

`infinite_large_primitive_pair_count` gives the clean corollary: for each
gamma in the same above-half range, there is a fixed B with infinitely many
n>1 such that

    #coprimePairs(B!,n) > n^(2*gamma).

The pair count is superlinear because gamma>1/2. THIS IS A COUNT OF ORDERED
PAIRS, NOT A DOUBLING OF THE MULTIPLICITY EXPONENT.

### Amplification check and scope

`coprimePair_product_mem` verifies the actual product construction:

    (a,b) in coprimePairs(K,n) ==> a*b in avoidingFiber(K,n^2).

So even after controlling product collisions, a pair supply of order
n^(2*alpha) at output n^2 preserves alpha. It does not give exponent
2*alpha at output n. The new result supplies no prime-producing operation
that would reduce the relative smoothness parameter.

Likewise, a proportion close to one of coprime pairs does not imply a large
PAIRWISE-coprime subfamily. The earlier subpower bound for such subfamilies
still applies. Nor does the result rule out polynomially rare large-overlap
pairs: the upper bad-pair fraction can be made a small fixed constant, not
an arbitrary negative power of n. It is not a disproof of the conditional
LCM-amplification hypothesis.

The original conjecture remains UNSOLVED. `Submission/Spec.lean` is unchanged
with its original `sorry` and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No unconditional multiplicity exponent was increased. No auxiliary repair
or background Lean process is pending, and there is no valid completed
submission to verify.

## Coprime record products: collision loss and square-output multiplicities

New completed files:

* `Submission/CoprimeRecordProducts.lean`
* `Submission/CoprimeRecordProductsCheck.lean`

Namespace: `Erdos821.CoprimeRecords`. Both compile cleanly; the result olean
is fresh. All six audited declarations use only `propext`, `Classical.choice`,
and `Quot.sound`. Logs: `/tmp/CoprimeRecordProducts.log` and
`/tmp/CoprimeRecordProductsCheck.log`.

### Finite product accounting

The existing `PredecessorProducts.productImage` and product-fiber divisor
bound are applied to `coprimePairs K n`.

* Each pair has positive inputs and product at most `576*n^4`, using the
  uniform input bound `a≤24*phi(a)^2` on both sides.
* Every product is in `avoidingFiber K (n^2)`, by squarefreeness, coprimality,
  and multiplicativity of phi.
* If all product divisor counts are at most D, then

      #coprimePairs(K,n) ≤ D * gAvoiding(K,n^2).

  Distinct ordered pairs are NOT assumed to have distinct products.

### Uniform subpower loss

`eventually_coprimePairs_card_le_mul_gAvoiding_square` proves, for every
fixed epsilon>0, eventually n, uniformly for ALL K:

    #coprimePairs(K,n) ≤ n^epsilon * gAvoiding(K,n^2).

The previous uniform divisor bound on the full range `m≤576*n^4` is used;
there is no pointwise-to-uniform asymptotic substitution.

### Unconditional square-output corollary

`infinite_square_output_multiplicity` proves for every

    1/2 < gamma < 1/2 + 1/(80000000*Sieve.totientRatioAverageConstant+10)

that some fixed B has infinitely many n>1 satisfying

    gAvoiding(B!,n^2) > (n^2)^gamma.

It applies the preceding bound to the primitive-pair count at a slightly
larger attained exponent, absorbing the subpower collision loss. Thus the
same above-half multiplicity range occurs at square outputs, with squarefree
inputs avoiding a fixed finite set of primes.

### Scope and unchanged main gap

This is exponent PRESERVATION, not amplification. The pair exponent 2*gamma
is measured at output n^2, giving multiplicity exponent gamma. Restricting
outputs to squares does not itself improve the smoothness of prime
predecessors relative to those primes: the input primes may be much smaller
than the overall output. The earlier large-fiber results with no polynomially
large input primes already warn against that inference.

There is no new prime-distribution theorem or all-order sharp-moment lower
bound. The original conjecture is still UNSOLVED. `Submission/Spec.lean` is
unchanged, with its original `sorry`, SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No auxiliary repair or background build is pending, and no valid complete
proof/disproof is ready to submit.

## Averaging and moving-cutoff recheck after the coprime-product construction

This continuation returned to the missing arithmetic estimate rather than
adding another pair-counting or conditional implication theorem.

Rechecked the actual types in `CompositeBelowHalfScales.lean`,
`OneSidedDistributionCriterion.lean`, `ShiftedDivisorPole.lean`, and
`ShiftedPrimeMomentLower.lean`.

* `eventually_product_mangoldt_total_lower` still requires `2*r+1≤t`.
  To force the entire remaining cofactor below the smoothness threshold in
  the direct near-full construction requires `r≥t-2`. Together these imply
  `t≤3`; no unbounded smoothness parameter follows.
* The fixed-modulus Dirichlet-series lower estimate has a cutoff-dependent
  constant. It yields arbitrarily large FIXED multiples of X/log X cofinally,
  not the required full logarithmic moment order. Averaging or passing to
  cofinal scales does not justify making that cutoff grow with X.
* Holding moduli fixed while taking X large loses the cofactor smoothness
  relation. Allowing the cutoff to grow again requires a uniform arithmetic
  estimate that has not been proved.

No new signed smooth-modulus estimate, exponent improvement, proof, or
disproof was obtained in this review. No Lean source was changed and no
auxiliary proof is pending. `Submission/Spec.lean` remains unchanged with
its original `sorry`; there is still no valid completed submission.

## Higher-order collision amplification review

The next continuation examined using r-tuples instead of pairs. No new Lean
source or unproved hypothesis was added.

For pairwise-coprime inputs all having totient n, the product has totient
n^r. A tuple supply on the scale g(n)^r therefore preserves the multiplicity
exponent; it does not multiply that exponent when measured against the new
output.

Allowing overlaps can compress the LCM output, but the map from tuples to
LCMs then has nontrivial fibers. A growing number of tuple entries also
requires a uniform collision estimate; fixed-order subpower bounds cannot
be silently used uniformly in that order. No lower bound on distinct LCMs
strong enough to increase the exponent was obtained. This is not a theorem
excluding all higher-order overlap methods.

The conjecture remains unproved and undisproved. `Submission/Spec.lean` is
unchanged with its original `sorry`. No complete proof is available for
submission and no auxiliary proof repair is pending.

## Variable-cofactor criterion and all stretched-log exponents

New completed and audited files:

* `Submission/VariableCofactorReciprocals.lean`
* `Submission/VariableCofactorReciprocalsCheck.lean`

Namespace `Erdos821`. The result olean is fresh, both Lean files compile
cleanly, and all ten audited declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`. Logs:
`/tmp/VariableCofactorReciprocals.log` and
`/tmp/VariableCofactorReciprocalsCheck.log`.
The temporary API probe was removed.

### General criterion

`variableCofactorParentSet A` consists of p in
`boundedCofactorParentSet (A p)`. Thus p=a*q+1 with p,q prime and
1<=a<=A(p).

`summable_variable_cofactor_parent_reciprocal` proves reciprocal convergence
provided:

* A is monotone;
* eventually m, A(2^(128*m)) <= 2^m;
* sum_m harmonic(A(2^(128*m)))/m^2 converges.

The proof compares counts on each full geometric block with the fixed
cutoff at that block's endpoint, then uses the already proved uniform
averaged two-prime sieve and the geometric count summability criterion.

### Stretched-log application

`stretchedLogCofactorCutoff R beta p` is

    2^floor(R * (Nat.log 2 p : Real)^beta).

For every fixed R>=0 and 0<=beta<1:

* `stretchedLogCofactorCutoff_mono` establishes monotonicity.
* `eventually_stretchedLog_block_cutoff_le` establishes the sieve cutoff
  condition, using m^(beta-1)->0.
* `harmonic_stretchedLog_block_le` bounds the harmonic cost by

      (1+R*128^beta*log 2)*m^beta,  m>=1.

* `summable_stretchedLog_harmonic_cost` uses convergence of m^(beta-2).
* `summable_stretchedLog_cofactor_parent_reciprocal` proves reciprocal
  convergence of these parents.
* `prime_outside_variable_cofactor_parent_iff` gives the arithmetic
  complement for any cutoff A:

      p prime ==> (p not in parents(A) iff
        forall q in primeFactors(p-1), A(p)*q < p-1).

* `not_summable_stretchedLog_prime_factor_bound` proves that the primes
  satisfying this complementary factor bound have divergent reciprocals.

### Boundary of this criterion, not an arithmetic disproof

`not_summable_linearLog_harmonic_cost` proves that at beta=1 and R>0 the
harmonic majorant series is NOT summable. Its terms eventually dominate

    (64*R*log 2)/m.

This disproves only the summability hypothesis of this sufficient criterion
for these polynomial-size cutoffs. It is NOT a nonsummability theorem for
the actual corresponding prime-parent set and NOT an obstruction to all
other approaches.

### Main status

These results extend the former beta=1/2 cofactor result to all fixed
beta<1, but all such cutoffs remain p^o(1). They do not provide a fixed
power saving in predecessor prime-factor size, arbitrary-root smooth
shifted primes, a full-tree relative contraction, or the missing all-order
prime moment lower bound. There is no new multiplicity exponent.

The original conjecture remains UNSOLVED. `Submission/Spec.lean` remains
unchanged with its original `sorry` and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No proof repair or background build is pending. There is no valid complete
proof/disproof to submit.

## Recursive prime-factor route recheck after the variable-cofactor theorem

This continuation returned to the main arithmetic gap instead of extending
the subpower cutoff results. Re-read `LargeChildPropagation`,
`LargeChildMass`, `LargeChildAvoidingTrees`, `SparseSmoothPrimeChains`, and
the pointwise canonical-parent mass test.

The available one-step propagation exponent remains

    b -> 1-(1-b)/(2*k),

so the fixed-depth power saving is not uniform over arbitrary depth.
The all-branches avoiding predicate supplies no independence or relative
counting estimate inside the avoiding family. The newly completed variable
cofactor criterion still does not reach polynomially large cofactors.

A logarithmically discounted parent mass was also considered informally.
Adding a factor (log p)^(-c), c>0, can make a candidate contraction easier,
but finiteness of that discounted mass does not imply convergence of the
undiscounted reciprocal series of primes. No tail estimate recovering the
needed undiscounted bound was obtained. This is an argument audit, not a
new formal impossibility theorem about weighted methods.

No new Lean theorem, exponent improvement, proof, or disproof was obtained.
No Lean source was changed during this continuation. The conjecture remains
UNSOLVED, and `Submission/Spec.lean` still has its original `sorry` and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
There is no unfinished proof repair or background build, and no valid complete
submission is ready.


## Binomial Mangoldt lower bound improves the fixed composite-sieve exponent

New completed source and audit:

* `Submission/BinomialCompositeGain.lean`
* `Submission/BinomialCompositeGainCheck.lean`

The result olean is fresh, both files compile cleanly, and all thirteen
checked declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`. Logs: `/tmp/BinomialCompositeGain.log` and
`/tmp/BinomialCompositeGainCheck.log`.

### Quantitative improvement

The previous structured second sieve used the old psi(N)>=N/8 lower bound.
The now available binomial estimate gives eventually psi(N)>=(5/8)*N on
all of its geometric scales. No PNT or new distribution hypothesis is used.

`eventually_product_mangoldt_weight_nine_sixteenths` uses the same
below-square-root discrepancy bound and the same reciprocal modulus mass
W, with its error bounded by N*W/16, to obtain total progression weight
at least (9/16)*N*W. It retains the restriction 2*r+1<=t.

For the existing strict structured parameters

    r=2*a, t=4*a+1, Y=2^(128*a*m), N=2^(64*(4*a+1)*m),

`binomial_structured_sieve_main_small` proves log(N)*SieveMain<=N/2 whenever

    a >= 300000*Sieve.totientRatioAverageConstant.

The key numerical comparison is

    266240*C*(4*a+1) <= (2*a-1)^2.

The old combined sieve/prime-power error remains bounded by N*W/64.
Consequently the surviving weight is at least N*W/32; the margin follows
from 9/16-1/2-1/64=3/64>1/32. The unchanged finite incidence and polynomial
count transfers then give the same structured family at these smaller a.

### Final new unconditional range

`infinite_g_gt_binomial_composite_limit` proves every exponent

    gamma < 1/2 + 1/(8*a+2)

when a>=300000*C. Taking a=ceil(300000*C) gives

`infinite_g_gt_binomial_composite_uniform`:

    gamma < 1/2 + 1/(2400000*C+10)
      ==> {n : Nat | (g n : Real) > (n : Real)^gamma}.Infinite.

`erdos_821_binomial_composite_range` gives the corresponding epsilon range:

    epsilon > 1/2 - 1/(2400000*C+10).

`binomial_composite_gain_gt_thirty_three_old_gain` proves that the gain above
one half is strictly greater than 33 times the old gain with 80000000 in
the denominator. This comparison is exact, not numerical experimentation.

### Scope and remaining gap

This is a genuine improvement to the strongest explicit unconditional
multiplicity exponent in the development, but only through constants. It
does NOT give exponents tending to one. Increasing a still shrinks the gain.
No stronger modulus distribution, arbitrary-root smoothness, or exponent
amplification has been proved.

In the direct near-full construction, the smoothness cutoff is
2^(128*m)=X^(2/t), not X^(1/t); combining its r>=t-2 requirement with
2*r+1<=t still limits t to at most 3. There is no hidden arbitrary-root
consequence at the smallest admissible parameter.

`Submission/Spec.lean` remains unchanged with its original `sorry` and
SHA-256 `8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The original conjecture is still UNSOLVED. No unfinished auxiliary proof
or background build is pending, and no valid complete submission exists.

## Higher-moment follow-up to the binomial constant improvement

This continuation examined whether the binomial argument could supply the
missing all-order shifted-prime moment lower bound, rather than merely
improving the unweighted Mangoldt constant.

Rechecked the actual finite transfer in `ShiftedDivisorLowerTransfer.lean`
and the fixed-cutoff Dirichlet lower bounds in `ShiftedDivisorPole.lean` and
`ShiftedPrimeMomentLower.lean`. The binomial factorization argument controls
psi(X), not the arithmetic weights tau(k,n-1). Expanding those weights
still requires progression counts for divisors of n-1 and leaves the
explicit divisorProgressionError term. No valid weighted binomial identity
or unconditional estimate removing that error was obtained.

The fixed-cutoff pole estimate still has a cutoff-dependent constant; it
cannot be used as a uniform bound with a growing cutoff. In particular,
its cofinal lower bound exceeding every fixed multiple of X/log X is not
the factorial-scale logarithmic moment required by the smoothness transfer.

No new Lean source was created or changed in this continuation. The new
strongest fixed exponent from `BinomialCompositeGain.lean` remains valid,
but the original conjecture is still UNSOLVED. `Submission/Spec.lean`
retains its original `sorry` and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No unfinished auxiliary proof or background build is pending, and no valid
complete proof/disproof is available for submission.

## Record fibers, finite prime pools, and the missing LCM pair supply

This continuation reconsidered the exponent-amplification route through
`LcmFibers.lean`, `RecordPairs.lean`, `RecordInputScale.lean`, and
`CoprimeRecordFibers.lean`.

The verified LCM transfer would improve an attained exponent alpha from a
supply of n^(2*alpha-lambda) pairs having phi(gcd)>=n^eta, provided
lambda<alpha*eta. No such lower pair-count bound was proved. The normalized
record estimates remain upper bounds for large-overlap rows and pairs.
The many coprime pairs instead produce output n^2 and preserve the exponent.

A finite-prime-pool variant was also considered informally: normalize the
subset-product fiber inside a fixed input-prime pool and use its divisibility
frequency bounds together with disjoint samples. This may offer more control
of the input-prime cutoff, but the resulting coverage inequalities did not
force a better power relation between output primes and that cutoff. Counts
of distinct prime representatives or of input tuples cannot be substituted
for counts of distinct compressed LCM outputs. No additional independence
or growing-order uniformity assumption was introduced.

No new Lean theorem or source modification resulted. This audit is not a
formal impossibility theorem for LCM methods. The strongest verified fixed
exponent remains the one in `BinomialCompositeGain.lean`, and the original
conjecture remains UNSOLVED. `Submission/Spec.lean` is unchanged with its
original `sorry`, SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No unfinished auxiliary proof or background build is pending. No complete
proof/disproof is ready to submit.

## Dense-support recursive-compression follow-up

Rechecked `DensePredecessorSupport`, `ClosedSmoothFibers`, and the prior
padding/stripping size accounting. The full predecessor product has a
subpower radical, but this estimate remains relative to that full product,
not automatically to the much smaller sparse selected outputs. Recursive
factorization did not supply a common-output encoding retaining enough
choices at a smaller output scale. Counting relations or independent
support choices is not itself a count in such a smaller totient fiber.

No new size estimate, multiplicity exponent, or Lean theorem was obtained.
This is not a proof that every recursive compression method fails.
`Submission/Spec.lean` is unchanged, with its original `sorry` and hash
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The conjecture remains UNSOLVED. There is no pending proof repair or
background build and no complete proof/disproof to submit.

## Output-valuation refinement of the record argument

Re-read `Valuation.lean`, `RecordOutputs.lean`, `RecordInputScale.lean`, and
`SmallRadicalMiddleFibers.lean`. Considered requiring repeated predecessor
contributions to account for high prime-power valuations in a record output.
No bound was obtained that converted this into a net multiplicity-exponent
increase. In particular, high valuation of the output is not a lower bound
on a common input divisor, and no such inference was used.

No new formal valuation-weighted cover lemma or amplification theorem was
added. The original conjecture remains UNSOLVED; the strongest completed
fixed-exponent result is still `BinomialCompositeGain.lean`.
`Submission/Spec.lean` is unchanged and retains its original `sorry`, with
SHA-256 `8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No unfinished proof repair or background build is pending, and no valid
complete proof/disproof is ready for submission.

## Exact logarithmic budget for record fibers

New completed and audited files:

* `Submission/RecordLogBudget.lean` (218 lines)
* `Submission/RecordLogBudgetCheck.lean`

The source and check file compile cleanly, the result olean is fresh, and
all seven audited declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. Logs: `/tmp/RecordLogBudget.log` and
`/tmp/RecordLogBudgetCheck.log`. The temporary API probe was removed.

### Exact incidence identity

For the FULL odd squarefree fiber at output n, if all its input primes are
at most P, `record_fiber_log_incidence` gives

    gOddSquarefree(n)*log n
      = sum_{p prime, p<=P} log(p-1) * #{m in fiber(n): p|m}.

This follows from the exact squarefree totient product identity and a
finite interchange of sums, without independence assumptions.

At a positive-output normalized record for exponent s,
`normalized_record_log_budget` applies the checked core-frequency bound:

    log n <= sum_{p prime, p<=P} log(p-1)*(p-1)^(-s).

`normalized_record_log_budget_pseries` gives the explicit consequence for
s<=u and u>1:

    log n <= log(P)*P^(u-s) * sum_{a>=1} a^(-u).

### Uniform scale consequence

`eventually_record_log_le_input_cutoff_power` proves, for every s<1 and
fixed epsilon>0, eventually in P, uniformly over all positive-output
records n with positive fiber and the full input-prime cutoff P,

    log n <= P^(1-s+epsilon).

It uses u=1+epsilon/2 and log P=o(P^(epsilon/2)). The input-cutoff
hypothesis concerns the ENTIRE odd squarefree fiber, not an arbitrarily
chosen subfamily or a finite-pool record whose closure properties have
not been proved.

`eventually_record_has_polylog_large_input_prime` removes that cutoff
hypothesis: for s<1, c>0, and c*(1-s)<1, every sufficiently large positive
normalized record contains an input m and a prime p|m such that

    (log n)^c < p.

### Scope

This is a necessary polylogarithmic input-size bound. It does not give a
prime of polynomial size in n, and hence does not convert the existing
root-smoothness of record OUTPUTS into arbitrary-root smoothness relative
to each PRIME PREDECESSOR. It provides no new multiplicity lower exponent.
The strongest fixed multiplicity range is still `BinomialCompositeGain`.

`Submission/Spec.lean` is unchanged with the original `sorry`, SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The original conjecture remains UNSOLVED. No proof repair or background
build is pending, and no complete proof/disproof is available to submit.

## Record-exponent existence checkpoint

Checked the exact hypotheses of `exists_large_normalized_record_at` against
`eventually_record_has_polylog_large_input_prime`. The first needs an
already attained witness exponent delta and requires s < delta. The second
is a constraint on qualifying records, not an existence theorem for them.
Consequently these results cannot currently be combined with s tending to
one. The strongest completed multiplicity range remains the fixed range
in `BinomialCompositeGain.lean`.

Also reconsidered whether recursive prime-factor covers or higher divisor
moments provide the missing increase. No new unconditional arithmetic
estimate was obtained. In particular, positivity and fixed-modulus
Dirichlet limits do not supply the required uniform all-order moment
coefficient.

No Lean source was changed in this checkpoint. `Submission/Spec.lean`
retains the original conjecture and its `sorry`; the task remains UNSOLVED.
There is no completed proof or disproof to submit.

## Sharp finite-cofactor propagation and near-endpoint growing depth

New completed, freshly built and audited files:

* `Submission/SharpLargeChild.lean` (365 lines; 15 audited lemmas/theorems)
* `Submission/SharpLargeChildCheck.lean`
* `Submission/SharpGrowingDepth.lean` (217 lines; 7 audited lemmas/theorems)
* `Submission/SharpGrowingDepthCheck.lean`

All four source/check compilations succeed. All 22 audited declarations
use only `propext`, `Classical.choice`, and `Quot.sound`. Logs are under
`/tmp/SharpLargeChild{,Check}.log` and
`/tmp/SharpGrowingDepth{,Check}.log`. No sorry/admit/axiom declaration is
present in either new result file.

### Finite cofactor sum removes the extra factor two

`sum_Icc_neg_rpow_le` proves, for 0 <= s < 1,

    sum_{1<=a<=N} a^(-s) <= N^(1-s)/(1-s).

`rough_divisor_weight_sum_sharp` uses the actual finite bound
1 <= a <= q^(k-1), rather than an infinite u-series with u>1, to obtain

    sum_{d in D} d^(-s)
      <= (1/(1-s))*sum_{q in Q} q^(k*(1-s)-1).

Here k>=1 and every positive d in D has a positive divisor q in Q with
d<=q^k. No primality is needed for this finite estimate.

The resulting parent-series update reaches the exact endpoint

    sharpLargeChildExponent(k,b) = 1-(1-b)/k

for 0<=b<1, rather than the previous 1-(1-b)/(2k). In particular, starting
at exponent 1-1/R, `summable_largeChildLayer_reciprocal_sharp` proves
summability of the Lth ancestor layer at

    1-1/(R*k^L).

`setPowerMass_largeChildLayer_sharp_le` keeps the explicit mass bound

    M*(1+R)^L*k^(L^2),

where M is the original mass and zero is outside the original set.

### Growing depths at smaller cutoffs

Define

    sharpDepthScale(k,R,L)  = R*k^L*(L+1)^3,
    sharpDepthCutoff(k,R,L) = 2^sharpDepthScale(k,R,L).

The compensation factor is now 2^((L+1)^3), which dominates the explicit
quadratic-in-L logarithm of the layer mass and every fixed power of the
scale. Consequently `eventually_sharp_growing_largeChildLayer_count_small`
saves every fixed power of sharpDepthScale, uniformly as L tends to
infinity. `eventually_sharp_growing_prime_complement_large` shows that at
least half the primes below the new cutoff are outside the Lth layer.

`negation_forces_sharp_growing_many_avoiding_trees` applies this to the
smooth-prime set supplied by the EXACT NEGATION of the conjecture. It is
still a conditional theorem: some k>=3 and R>=1 would have at least half
the primes below these cutoffs avoiding the smooth set along every
eligible branch for L levels.

### Why this is not a settlement

The exponent gap still tends to zero with increasing depth. The new
result does not show that an eligible branch must reach the smooth set
within L steps at these cutoffs. Existing termination proves eventual
arrival at a depth depending on the prime, not the required uniform
arrival by L. Thus no contradiction with the conditional avoiding-tree
conclusion has been established. These results improve the necessary
consequence of negation, not the unconditional multiplicity exponent.

`Submission/Spec.lean` remains unchanged with its original `sorry`, hash
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The original task is UNSOLVED. No unfinished Lean proof or background
build is pending, and no complete proof/disproof is ready to submit.

## Follow-up: uniform arrival is still missing

Reviewed the sharp growing-depth consequence alongside the variable-cofactor
reciprocal bounds and the existing moment-model audits. No uniform theorem
forcing arrival at the root-smooth prime set within the controlled depth
was obtained. Individual termination is insufficient; the small-cofactor
exclusions do not fill that gap. The finite moment models remain auxiliary
models, not prime models or disproofs, and no new low-to-high arithmetic
moment inference was established.

No Lean source changed during this follow-up. The original conjecture in
`Spec.lean` remains UNSOLVED with its original `sorry`. The two sharp-depth
files from the preceding continuation remain compiled and audited. There
is no pending build or completed proof/disproof to submit.

## Full-input versus squarefree energy follow-up

Checked whether allowing all prime powers in the finite-support generating
function supplies an exponent amplification missing from squarefree energy.
The existing exact upper bound `g_le_sum_gSquarefree_divisors`, together
with the subpower divisor bound and `erdos_821_iff_squarefree_inputs`,
accounts for this passage. It does not itself increase an attained
multiplicity exponent. No new lower bound on the required energy
cross-correlations was obtained. This does not rule out a future proof
using the full-input generating function.

No Lean source was changed. `Spec.lean` retains its original `sorry`.
The task remains UNSOLVED, with no complete proof/disproof to submit.

## Endpoint smooth-predecessor upper bound

New compiled and audited files:

* `Submission/EndpointSmoothUpper.lean` (232 lines)
* `Submission/EndpointSmoothUpperCheck.lean`

Both compile cleanly; the result olean is fresh. All six audited
declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
Logs: `/tmp/EndpointSmoothUpper.log` and
`/tmp/EndpointSmoothUpperCheck.log`.

The sharp finite-cofactor sum now also applies directly to the inverse-
totient support product. For 0<=s<1 it gives rough cost

    (1/(1-s))*sum_{q|n, q prime} q^(k*(1-s)-1).

The small/large prime split was extended from beta>0 to beta>=0, using
logarithmic divergence at the endpoint. Thus the rough exponent may be
zero, not only negative.

`g_le_endpoint_exp_primeFactors` gives, for k>=1 and n>0, under summability
of the root-k predecessor series at s=1-1/k,

    g(n) <= n^(1-1/k)*exp(M+k*omega(n)),

where M is that series sum and omega(n) is the number of distinct prime
factors. `eventually_g_le_rpow_of_summable_smooth_endpoint` absorbs the
error into any positive exponent loss. Conversely,
`not_summable_smooth_endpoint_of_infinite_g_gt` says that an attained
exponent gamma>1-1/k forces divergence of this endpoint series.

`erdos_821_iff_endpoint_smooth_series` proves the exact equivalence of the
original conjecture with endpoint divergence for every k>=2. The reverse
direction uses root 2k to supply the earlier diagonal exponent for root k.
This is a conditional characterization, not an assertion of divergence.

Scope: the new pointwise omega(n) bound retains a sharper explicit error.
The eventual endpoint consequence can also be approached from the previous
strict inequalities by raising exponents slightly. No new unconditional
multiplicity exponent or arbitrary-root prime abundance was obtained.

`Submission/Spec.lean` is unchanged, with its original `sorry` and hash
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The task remains UNSOLVED. No proof repair or background build is pending,
and no complete proof/disproof is available for submission.

## Audit of strongest available theorem statements

Rechecked the declarations concluding multiplicity infinitude and the
original proposition, including `Combined`, `AboveHalfLowerExponent`,
`BinomialCompositeGain`, and the conditional series/moment/distribution
transfers. No overlooked unconditional theorem allowing exponents to
approach one was found. The fixed binomial-composite range is still the
strongest explicit unconditional multiplicity range established here.
No Lean source changed, and the original `Spec.lean` remains UNSOLVED with
its `sorry`. No proof/disproof is ready for submission.

## Finite local smooth-predecessor budgets for individual large fibers

Completed `Submission/LocalSmoothBudget.lean` (264 lines) and its check file.
The source compiles cleanly, and all ten audited lemmas/theorems depend only
on `propext`, `Classical.choice`, and `Quot.sound`. There is no sorry, admit,
or new axiom in this auxiliary source.

Unlike the previous endpoint bound, the new finite estimate makes NO
summability assumption. Define

    localSmoothMass k n s
      = sum_{d|n, d in smoothShiftedPredecessors k} d^(-s).

`shifted_divisor_weight_sum_local` and `g_le_local_smooth_mass` bound the
entire inverse-totient support by this local sum plus the sharp finite
cofactor error. At the endpoint, `g_le_local_endpoint` gives

    g(n) <= n^(1-1/k) * exp(localSmoothMass k n (1-1/k) + k*omega(n)).

`large_g_forces_local_smooth_mass` therefore shows, whenever g(n)>n^gamma,

    (gamma-(1-1/k))*log n
      < localSmoothMass k n (1-1/k) + k*omega(n).

`eventually_large_g_forces_local_smooth_mass` absorbs the support error:
for fixed gamma>1-1/k, large qualifying fibers have local mass exceeding
one quarter of (gamma-(1-1/k))*log n.

The finite cutoff estimates retain a count of the large smooth divisors:

* `localSmoothMass_le_cutoff_card`: for T>0 and 0<=s<1,

      localSmoothMass <= T^(1-s)/(1-s) + #largeSmoothDivisors * T^(-s).

* `localSmoothMass_endpoint_le_cutoff_card`: at T=B^k, the two coefficients
  simplify to k*B and 1/B^(k-1).

* `large_g_forces_large_smooth_divisors`: for n,B>0, g(n)>n^gamma implies

      ((gamma-(1-1/k))*log n - k*omega(n) - k*B) * B^(k-1)
        < #{d|n : d in smoothShiftedPredecessors k, B^k<d}.

* `eventually_large_g_forces_log_pow_many_smooth_divisors`: for each fixed
  k>=1 and gamma>1-1/k there exist c,C>0 such that, eventually in n,

      g(n)>n^gamma
        ==> C*(log n)^k
              < #{d|n : d in smoothShiftedPredecessors k,
                         floor(c*log n)^k<d}.

The last proof takes Delta=gamma-(1-1/k), c=Delta/(8*k), and
C=(Delta/8)*(c/2)^(k-1). It uses the local finite estimate and elementary
floor bounds, not a moving-cutoff prime distribution assumption.

Scope: these are necessary conditions on an already large fiber. They do
not supply large fibers at new exponents or establish arbitrary-root smooth
shifted-prime abundance. No exponent-amplification step was obtained. The
finite partition models were also revisited: they already include their
exact total-size constraints, but are not asymptotic models of primes.

Logs: `/tmp/LocalSmoothBudget.log` and `/tmp/LocalSmoothBudgetCheck.log`.
`Submission/Spec.lean` is unchanged with its original sorry and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The original task remains UNSOLVED; no valid proof/disproof is available
for submission. No unfinished proof or background build is pending.

## Concentration in a subpower divisor window

Completed `Submission/LocalSmoothWindow.lean` (197 lines) and
`Submission/LocalSmoothWindowCheck.lean`. Both compile cleanly with fresh
oleans. All five audited declarations use only the three permitted axioms.
There is no sorry, admit, or new axiom in this auxiliary source.

The previous local count can now be confined to an explicit finite window.
Write tau(n)=n.divisors.card. The new declarations are:

* `localSmoothMass_le_window`: for positive L,U and 0<=s<1,

      localSmoothMass k n s
        <= L^(1-s)/(1-s)
           + #{d|n : root-k smooth predecessor, L<d<=U} * L^(-s)
           + tau(n)*U^(-s).

  No ordering assumption L<=U or summability hypothesis is required.

* `divisor_square_cutoff_cost_le_one`: for n>0 and s>=1/2,

      tau(n)*(tau(n)^2)^(-s) <= 1.

* `localSmoothMass_endpoint_le_window`: for k>=2 and n,B>0,

      localSmoothMass k n (1-1/k)
        <= k*B
           + #{d|n : root-k smooth predecessor, B^k<d<=tau(n)^2}/B^(k-1)
           + 1.

* `eventually_divisor_square_cutoff_le_rpow`: for every epsilon>0,
  tau(n)^2 <= n^epsilon eventually. This follows from the already proved
  divisor-count subpower bound, with epsilon/2.

* `eventually_large_g_forces_many_smooth_divisors_in_window`: for fixed
  k>=2 and gamma>1-1/k, there are c,C>0 such that eventually in n,

      g(n)>n^gamma
        ==> C*(log n)^k
              < #{d|n : root-k smooth predecessor,
                         floor(c*log n)^k<d<=tau(n)^2}.

  The proof uses Delta=gamma-(1-1/k), c=Delta/(16*k), and
  C=(Delta/8)*(c/2)^(k-1). The extra tail cost 1 is absorbed using the
  eventual lower bound c*log n>=2.

Scope: the subpower upper cutoff is relative to n, while the guaranteed
count is polynomial in log n. There is no sufficiently strong relation
between tau(n) and log n here to turn this into near-linear shifted-prime
abundance at that upper cutoff. In particular, these necessary conditions
on an already attained exponent have not supplied an exponent increase.
They do not settle the original conjecture.

Logs: `/tmp/LocalSmoothWindow.log` and `/tmp/LocalSmoothWindowCheck.log`.
`Submission/Spec.lean` remains unchanged with its original sorry and hash
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The task is still UNSOLVED; no valid full proof/disproof is ready for
submission. No unfinished proof or background build is pending.

## Attained exponents survive restriction to smooth-prime cores

Completed `Submission/SmoothPrimeCore.lean` (361 lines),
`Submission/SmoothPrimeCoreGain.lean` (25 lines), and both corresponding check
files. All compile cleanly with fresh oleans; the fourteen general declarations
and the unconditional corollary are audited against the permitted axioms.
No sorry, admit, or new axiom occurs in these sources. `CoreProbe.lean` was
removed and is not a dependency.

Definitions:

    gSquarefreeOn R n
      = #{m : Squarefree m, totient m=n, every p|m satisfies R p}

    gSmoothCore k n
      = gSquarefreeOn (fun p => p-1 in smoothShiftedPredecessors k) n.

This is smoothness of EACH input prime's predecessor relative to that
predecessor, not merely smoothness of the whole output or of the input
relative to the output. The restricted count is at most g(n).

### Finite support separation

`support_sum_le_core_mul_rough` splits each admissible prime support S into
its R and non-R subsets. This pair determines S injectively. The good subset's
predecessor product divides n; the bad subset is bounded by an unrestricted
finite Euler product. `coreSupport_fiber_card_le` and
`core_support_weight_sum_le` then bound the good-support weighted sum by

    sum_{d|n} gSquarefreeOn(R,d) * d^(-s).

`g_weight_le_core_sum_mul_rough` is the resulting general weighted support
bound. It includes the full original fiber, including prime powers, using
the already established injective admissible-support description.

`rough_shifted_weight_sum_le` and its endpoint version bound the bad-prime
Euler product for root-k smoothness. The resulting finite theorem is

    g_le_smooth_core_divisor_sum:
      g(n) <= n^(1-1/k) * exp(k*omega(n)) *
                sum_{d|n} gSmoothCore(k,d) * d^(-(1-1/k)).

There is no summability assumption in this bound.

### Exponent preservation, not improvement

`eventually_core_rough_cost_le_rpow` absorbs
C*tau(n)*exp(k*omega(n)) into n^epsilon, for any fixed epsilon>0.
`g_le_of_global_smooth_core_bound` and
`eventually_g_le_of_smooth_core_bound` consequently transfer a restricted
upper bound gSmoothCore(k,n)<=n^t to g(n)<=n^u eventually, whenever

    1-1/k <= t < u.

The contrapositive, `infinite_gSmoothCore_gt_of_infinite_g_gt`, proves:

    1-1/k <= beta < gamma,
    infinitely many g(n)>n^gamma
      ==> infinitely many gSmoothCore(k,n)>n^beta.

`infinite_gSmoothCore_two_gt_binomial` supplies the unconditional corollary
for every beta in the existing range

    1/2 <= beta < 1/2 + 1/(2400000*Sieve.totientRatioAverageConstant+10).

Thus the best current fixed range survives the stronger input restriction.
No larger multiplicity exponent was proved. Reapplying this transfer at a
fixed k only preserves an existing exponent with loss; moving to a larger
k still requires an attained exponent above its larger endpoint. In
particular this is not an iteration sending the exponent to one.

Logs: `/tmp/SmoothPrimeCore.log`, `/tmp/SmoothPrimeCoreCheck.log`,
`/tmp/SmoothPrimeCoreGain.log`, and `/tmp/SmoothPrimeCoreGainCheck.log`.
`Submission/Spec.lean` remains unchanged with its original sorry and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The original task remains UNSOLVED. No valid final proof/disproof is ready
for submission, and no proof repair or background build is pending.

## Pointwise extraction and size control for smooth-core divisor outputs

Completed `Submission/SmoothCoreExtraction.lean` (195 lines) and its check
file. Both compile cleanly with fresh oleans. All five audited declarations
use only `propext`, `Classical.choice`, and `Quot.sound`. The auxiliary
source contains no sorry, admit, or new axiom.

Let s=1-1/k. The new finite result
`exists_smooth_core_divisor_weight` selects a divisor d|n with

    g(n) <= tau(n)*exp(k*omega(n))*n^s*gSmoothCore(k,d)*d^(-s).

This is obtained by maximizing the normalized restricted count over the
finite divisor set; no infinite series or density hypothesis is used.

`eventually_extract_smooth_core_divisor` is a pointwise version of exponent
preservation. For beta>=s and epsilon>0, every sufficiently large n with

    g(n)>n^(beta+epsilon)

has a divisor d|n satisfying BOTH

    gSmoothCore(k,d) > n^(beta-s)*d^s,
    gSmoothCore(k,d) > d^beta.

The stronger first inequality provides size control. If a>s and the
explicit hypothesis g(m)<=m^a eventually holds, then
`eventually_extract_smooth_core_divisor_of_upper_bound` gives, for beta>s,

    d > n^((beta-s)/(a-s)).

The proof first forces the selected d past the finite exceptional range of
the upper bound. It does not apply an eventual estimate to an uncontrolled
small divisor.

`eventually_extract_polynomially_large_smooth_core` applies the already
proved eventual sublinearity of g, so it is unconditional apart from the
qualifying-large-fiber assumption:

    g(n)>n^(beta+epsilon)
      ==> exists d|n,
            d > n^(k*(beta-(1-1/k))) and gSmoothCore(k,d)>d^beta,

for all sufficiently large n, whenever beta>1-1/k.

`near_upper_exponent_has_large_smooth_core` records a further conditional
consequence. If s<a<=1 and g(m)<=m^a eventually, then for every 0<eta<=1
there is delta>0 such that, eventually,

    g(n)>n^(a-delta)
      ==> exists d|n, d>n^(1-eta) and gSmoothCore(k,d)>d^(a-eta).

Here delta=eta*(a-s)/4. This theorem does NOT assert that those near-upper-
exponent fibers exist or that an upper exponent a<1 exists.

Scope: this gives size-controlled divisor extraction, not an increase of
the multiplicity exponent. The root-k endpoint restriction is unchanged.
The existing record-output bounds were rechecked against this construction:
output smoothness still does not give the required relative smoothness of
each input prime's predecessor. No valid scale conversion or amplification
closing that gap was obtained.

Logs: `/tmp/SmoothCoreExtraction.log` and
`/tmp/SmoothCoreExtractionCheck.log`.
`Submission/Spec.lean` is unchanged with its original sorry and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The task remains UNSOLVED. No valid final proof/disproof is available for
submission, and no unfinished proof or background build is pending.

## Necessary Rankin budget and optimized-envelope audit

Completed `Submission/RankinBudgetAudit.lean`. It compiles cleanly with a
fresh olean. Its three printed axiom audits contain only `propext`,
`Classical.choice`, and `Quot.sound`.

`quadratic_log_necessary_for_rankin_budget` proves that, for k,n>0 and C>=0,

    (2^k)^2 * exp(C) <= n^(1/k)
      ==> 2*log(2)*k^2 <= log(n).

Thus the A^2 factor, by itself, imposes a quadratic threshold when A=2^k
and e=1/k. Sharpening the other constant in the existing budget cannot
turn it into a linear threshold while retaining those parameter choices.
`smooth_rankin_budget_forces_quadratic_log` applies this to the precise
smoothRankinConstant budget in `UniformRankin.lean`.

`eventually_optimized_envelope_gt_fixed_power` proves that the existing
optimized support upper envelope is eventually strictly larger than
n^(1-epsilon), for every fixed epsilon>0. This is an inequality about the
UPPER ENVELOPE, not a lower bound for g. The optimized loss has order
log(log(log n))/log(log n), and tends to zero. It cannot on its own yield
a fixed-power disproof.

The all-order moment and endpoint-series routes were reexamined. No new
lower moment or arbitrary-root divergence was obtained. No exponent
amplification was established. In particular, none of the audit lemmas
settles the original conjecture.

Log: `/tmp/RankinBudgetAudit.log`.
`Submission/Spec.lean` remains unchanged with its original sorry and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The task remains UNSOLVED. No valid final proof/disproof is available for
submission, and no unfinished proof or background build is pending.

## Larger finite half-level partition probes (exploratory, not Lean proofs)

This continuation tested whether the size-12 moment obstruction disappears
at larger finite resolutions. No conjecture proof or disproof was obtained.

New development scripts:

* `Submission/partition_lp_probe.py`: integer partitions, cycle denominators,
  and an exploratory floating-point LP in density-ratio coordinates.
* `Submission/partition_lp_reconstruct.py`: a better-conditioned LP using
  integral binomial-moment coefficients, followed by EXACT rational linear
  algebra and positivity checks in Sage. Run using `sage -python`.

For N=18 and N=24, root=4, exact nonnegative rational distributions were found
on partitions of N with a part strictly exceeding floor(N/4). Each has total
mass one, all single-part means E[C_j]=1/j for 1<=j<=N, and all joint binomial
moments of selected total size <=floor(N/2), INCLUDING that endpoint, equal
to their uniform-permutation-cycle values 1/z(mu).

N=18: 106 equations and 104 positive masses.
N=24: 284 equations and 282 positive masses.
The candidate support came from a numerical LP, but its weights were then
reconstructed with exact rational linear algebra, and all equations and
nonnegativity were checked exactly. The numerical solver alone was NOT used
as a certificate. Initial density-ratio-coordinate runs gave inconclusive
HiGHS statuses. Two slow PPL runs were stopped; their scripts were removed.
There is no pending background solver or Lean build.

Certificates (EXTERNAL exact computations, not Lean theorems):
`/tmp/partition_exact_reconstruction_18_4.json`
`/tmp/partition_exact_reconstruction_24_4.json`
Log for N=24: `/tmp/partition_reconstruct_24_4.log`.

These remain TWO FIXED FINITE MODELS. They are not models of actual primes,
not an arbitrarily fine family, not a limiting point-process construction,
and not a disproof of Erdos 821. In particular, the all-single-part mean
assumptions above half are also extra model assumptions, not an asserted
unconditional prime-distribution theorem. No new Lean theorem was added
and no missing arithmetic estimate was proved in this continuation.

`Submission/Spec.lean` remains unchanged with its original sorry and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The original task remains UNSOLVED; there is no valid completed submission.

## Bounded completion search over the admitted-free auxiliary development

Generated two temporary files importing 39 leaf modules covering 156 built
auxiliary sources. The original Spec module was excluded. Sources with
admissions or explicit axioms were excluded; the source scan found the
original Spec sorry and no other such declarations.

Tried `exact?` on the EXACT original proposition and separately on its
negation. The direct proof search hit its deterministic heartbeat limit
(2,000,000); the negation search reported that it could not close the goal.
Neither result is a mathematical nonexistence result. No completed proof
was found and there was no proof to axiom-audit or inline into Spec.

Logs: `/tmp/CompletionSearchProof.log` and
`/tmp/CompletionSearchDisproof.log`.
The two unsuccessful temporary source files were removed. No new Lean
result was proved and no background search or proof repair is pending.
`Submission/Spec.lean` is unchanged with its original sorry. The task
remains UNSOLVED and no valid final submission is ready.

## Growing polylogarithmic input-prime excision

Completed `GrowingPrimeExcision.lean` (226 lines),
`GrowingPrimeExcisionGain.lean`, and `GrowingPrimeExcisionCheck.lean`.
They compile with fresh oleans. All seven audited declarations use only
`propext`, `Classical.choice`, and `Quot.sound`. No admissions or new axioms
were added. The check file is only an axiom audit.

Define gAboveCutoff(B,n) to count squarefree totient preimages of n whose
prime factors are all strictly greater than B. The general weighted
support split gives, for 0<=s<=u and u>1,

    g(n)*n^(-s)
      <= exp(B^(u-s)*sum_a a^(-u))
         * sum_{d|n} gAboveCutoff(B,d)*d^(-s).

The new finite estimate is uniform in B. It does not substitute a growing
cutoff into an asymptotic proved only for fixed cutoffs. The small-prime
cost follows from the injection p -> p-1 and the existing bounded-multiples
p-series inequality.

`eventually_polylog_prime_excision_cost` proves that, for c>0,
c*(u-s)<1, and any epsilon>0,

    tau(n)*exp(floor((log n)^c)^(u-s)*sum_a a^(-u)) <= n^epsilon

for all sufficiently large n. The logarithmic scale and divisor-count
cost are estimated separately, each using half the epsilon budget.

`eventually_extract_polylog_excluded_fiber` proves: if 0<=s<1, c>0,
c*(1-s)<1, and epsilon>0, then eventually every n with

    g(n)>n^(s+epsilon)

has a positive divisor d|n such that

    gAboveCutoff(floor((log n)^c),d) > n^(epsilon/2)*d^s.

In particular the cutoff is computed from the ORIGINAL output n, not an
uncontrolled smaller divisor. The proof chooses

    u = 1 + (1-c*(1-s))/(2*c),
    c*(u-s) = (1+c*(1-s))/2 < 1.

`infinite_gAbovePolylog_of_infinite_g` transfers infinitude at exponent
s+epsilon to infinitude at exponent s with the cutoff computed from each
new output. The factor n^(epsilon/2) forces the selected divisor past
any finite exceptional range; monotonicity in the cutoff then replaces
log n by log d. This argument needs no record hypothesis.

`infinite_gAbovePolylog_binomial` retains the full existing fixed
binomial-composite exponent range under this restriction whenever
c*(1-s)<1. `infinite_half_power_above_polylog` gives the simple unconditional
corollary for s=1/2 and every 0<c<2.

Scope: this is a growing-cutoff strengthening of exponent preservation,
NOT exponent amplification. A possible sunflower/product follow-up was
considered informally: removal of small input primes improves bounds on
the number of factors in each input, but no resulting supply of distinct
compressed outputs with a higher multiplicity exponent was established.
No new arbitrary-root smooth-prime lower bound follows from these lemmas.

Logs: `/tmp/GrowingPrimeExcision.log`, `/tmp/GrowingPrimeExcisionGain.log`,
and `/tmp/GrowingPrimeExcisionCheck.log`.
`Submission/Spec.lean` is unchanged, with its original sorry and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The original task remains UNSOLVED. No complete proof or disproof is ready
for submission, and no proof repair or background build is pending.

## Source-exponent refinement and the log-square cutoff

Extended the growing prime-excision development, without adding imports to
any of its files or changing `Spec.lean`.

An attempted critical-cost follow-up was checked against the existing
exponent slack before developing a new prime-counting estimate. Mathlib
provides `Chebyshev.eventually_primeCounting_le`, and the finite decreasing
weight rearrangement would bound a shifted-prime mass by
`primeCounting(B)^(1-s)/(1-s)`. However, no such new analytic lemma was
needed or added: for the infinitude conclusion, a slightly larger attained
intermediate exponent already resolves the destination-endpoint cutoff.

New verified declarations:

* `infinite_gAbovePolylog_mono_exponent`: the retained exponent may be
  weakened without changing the growing cutoff. The finite exceptional
  input n=0 is removed explicitly before using monotonicity of real powers.
* `infinite_gAbovePolylog_of_source_exponent`: if 0<=s<gamma<=1,
  c>0, c*(1-gamma)<1, and infinitely many g(n)>n^gamma, then infinitely
  many d have gAboveCutoff(floor((log d)^c),d)>d^s. Thus it is the SOURCE
  exponent gamma, not the weaker retained exponent s, that governs the
  admissible cutoff.
* `infinite_half_power_above_log_square`: infinitely many fibers retain
  more than sqrt(d) squarefree inputs after excluding all primes up to
  floor((log d)^2). It uses the previously established exponent strictly
  above one half; it does not improve that exponent.

The source-exponent proof chooses

    t = (max(s,1-1/c)+gamma)/2,

so s<t<gamma and c*(1-t)<1, applies the preceding strict-cutoff theorem,
and then weakens t to s. All three development/check files build cleanly
with fresh oleans. Nine printed axiom audits now contain only `propext`,
`Classical.choice`, and `Quot.sound`. Logs retain the same paths as above.

This closes only a presentation gap in the growing-cutoff corollaries.
It does not give exponent amplification, a new smooth-shifted-prime lower
bound, or a settlement of the original conjecture. `Submission/Spec.lean`
remains unchanged with its original sorry. No proof repair or background
build is pending, and no valid complete proof/disproof is ready to submit.

## Sharper Selberg weights, quadratic-scale errors, and a larger fixed exponent

This continuation completed a new analytic refinement and propagated it to a
strictly larger unconditional totient-multiplicity exponent. The original
conjecture remains UNSOLVED; Spec.lean has not been changed.

### New files and verification

Six admission-free development files (1,208 lines in total):

* `SharpSelbergWeights.lean` (303 lines)
* `SharpPairSieve.lean` (196 lines)
* `SharpSieveDenominator.lean` (159 lines)
* `SharpPrimePairBound.lean` (125 lines)
* `SharpCompositeSieve.lean` (166 lines)
* `SharpCompositeGain.lean` (259 lines)

Check files:

* `SharpSelbergWeightsCheck.lean`
* `SharpCompositeGainCheck.lean`

All eight files were rebuilt in dependency order with fresh oleans. All 18
printed axiom audits contain only propext, Classical.choice, and Quot.sound.
The final logs `/tmp/<module-name>.log` have no errors or warnings. There are
no unfinished Lean repairs or background jobs.

### Retaining the local Selberg denominator

`downward_upset_product_sum_le` proves the finite combinatorial estimate

    sum_{R in W, S subset R} product_{p in R} u(p)
      <= product_{p in S} u(p) * sum_{R in W} product_{p in R} u(p),

for a downward-closed finite family W and nonnegative u. The injection is
R -> R\S, with image still in W.

The explicit Selberg weight construction then yields
`exists_selberg_weights_local`, with the sharper bound

    |lambda(S)| <= product_{p in S} (1-v(p))^(-1).

The original generic argument used only |lambda(S)|*product(v(p))<=1.
`finite_selberg_bound_local` retains the error as

    (sum_{S: product(S)<=z} product_{p in S} rho(p)/(1-rho(p)/p))^2.

This is a finite, unconditional bound; no asymptotic distribution assumption
or lower sieve is used.

### A uniform z^(2+delta) two-prime sieve error

For p>=3, 2/(1-2/p)<=6. For every epsilon>0, uniformly over all finite sets
of positive distinct integers,

    6^card(S) <= C_epsilon * product(S)^epsilon.

This follows by splitting off the fixed finite range where p^epsilon<6.
The prime-product map is injective, so there are at most z such subsets
with product<=z. Consequently `eventually_pair_local_error_le_rpow` proves
that for every delta>0, eventually in z, UNIFORMLY over P,

    (sum_{S subset P, product(S)<=z}
        product_{p in S} 2/(1-2/p))^2 <= z^(2+delta).

`eventually_prime_pair_sieve_bound` applies this to simultaneous primality
of q and a*q+1, uniformly in both N and a. The old error was z^4.

### A shorter Euler-product truncation

`sum_prime_log_div_le_log_add` proves the elementary finite estimate

    sum_{p<=N} log(p)/p <= log(N)+log(4)   (N>0).

Proof: floor(N/p)<=v_p(N!), N/p<=floor(N/p)+1,
log(N!)<=N log(N), and theta(N)<=N log(4). It requires neither PNT nor an
unproved prime-progression result.

At N=2^L, this is (L+2)*log(2). The existing first-moment truncation thus
retains half the two-dimensional Euler product at z=2^(6L), for L>=4,
instead of z=2^(16L). The logarithmic denominator lower bound is unchanged.

`eventually_prime_pair_explicit_sharp` gives, eventually in L and uniformly
in N,a>0,

    #{q<N: q and a*q+1 prime}
      <= 2*N / ((phi(2a)/(2a))*L*log(2))^2
         + 2^(15L)+2^(6L)+1.

Here delta=1/2 is used in the new error estimate. Taking L=4J and absorbing
2^(60J)+2^(24J)<=2^(64J) gives
`eventually_prime_pair_explicit_gain_sixteen`:

    #{q<N: q and a*q+1 prime}
      <= N / (8*((phi(2a)/(2a))*J*log(2))^2) + 2^(64J)+1.

The main coefficient is sixteen times smaller than the earlier bound at
the SAME old error scale. The threshold in J is absolute: it is independent
of N and a. This uniformity is explicitly preserved through the cofactor
and composite-modulus sums in `SharpCompositeSieve`.

### New strongest unconditional multiplicity exponent

The improved composite-sieve main coefficient is 2*C instead of 32*C,
where C=Sieve.totientRatioAverageConstant>=1. The modulus-distribution
estimates, geometric scales, and error estimates are unchanged.

The retained-weight proof now works for every natural a with

    16642*C <= a.

The coefficient inequality is

    16640*C*(4*a+1) <= (2*a-1)^2.

For such a, `infinite_g_gt_sharp_composite_limit` proves infinitude for
all gamma<1/2+1/(8*a+2). Choosing a=ceil(16642*C) yields

    infinite_g_gt_sharp_composite_uniform (gamma : Real)
      (hgamma : gamma < 1/2 + 1/(133136*C+10)) :
      {n : Nat | (g n : Real) > (n : Real)^gamma}.Infinite.

This is now the strongest explicit unconditional exponent in the auxiliary
development, superseding the 2400000*C+10 denominator in
`BinomialCompositeGain`.

`sharp_composite_gain_gt_eighteen_binomial_gain` verifies exactly that

    18/(2400000*C+10) < 1/(133136*C+10).

The improvement exceeds eighteen times the previous gain above one half.
The additional improvement beyond the factor sixteen comes from tightening
the previous slack in the final natural-parameter coefficient comparison.

`erdos_821_sharp_composite_range` states the corresponding epsilon range.
It is ONLY a partial range of the original quantified assertion.

### Remaining scope

This result is a genuine exponent improvement, but still a fixed exponent
very close to one half. It does not provide exponents tending to one,
arbitrary-root smooth shifted primes, SharpDyadicMomentLower, or stronger
prime-progression distribution. The original conjecture is still UNSOLVED.

Spec.lean is unchanged, retains its original sorry, and has SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof/disproof is ready for submission; submit_proof was not called.

## Exact prime-support harmonic sums and a hyperbolic sieve denominator

This continuation proved another unconditional analytic refinement and
propagated it through the existing composite-modulus construction. It did
NOT settle the original conjecture.

### New files and verification

Six new development files, 898 lines total:

* `PrimeSupportHarmonic.lean` (116 lines)
* `AvoidingHarmonicMoments.lean` (119 lines)
* `HyperbolicSieveDenominator.lean` (106 lines)
* `HyperbolicPrimePairBound.lean` (122 lines)
* `HyperbolicCompositeSieve.lean` (166 lines)
* `HyperbolicCompositeGain.lean` (269 lines)

`HyperbolicCompositeGainCheck.lean` audits 17 principal declarations and the
exact strongest exponent statement. All seven files have been rebuilt in
dependency order with fresh oleans. Logs `/tmp/<module-name>.log` contain no
errors or warnings. All printed axiom lists use only propext,
Classical.choice, and Quot.sound. No admissions or new axioms were added.
The temporary SupportProbe.lean was removed. No proof repair or background
build is pending.

### Exact support and uniform exclusion estimates

`hasSum_prime_power_tau` evaluates the local series for every fixed order:

    sum_{e>=0} tau(k+1,p^e)/p^e = (1-1/p)^(-(k+1)).

`sum_exact_prime_support_tau_le` proves, for any finite set A of positive
integers n<=z having exactly prime support S,

    sum_{n in A} tau(k+1,n)/n
      <= product_{p in S} ((1-1/p)^(-(k+1))-1).

The injection n -> (v_p(n))_{p in S} lands in the finite exponent box
[1,z]^S; the product-of-sums identity and the positive-exponent local
series bound give the inequality. This is a result on INTEGERS, not a
lower moment on shifted primes.

Define avoidingHarmonicMoment(k,z,P) by restricting the harmonic divisor
moment to n avoiding every prime in the finite set P.
`avoidingHarmonicMoment_strip` removes one prime by the exact decomposition
n=p^e*ordCompl[p](n). Induction gives

    product_{p in P}(1-1/p)^(k+1) * harmonicMoment(k+1,z)
      <= avoidingHarmonicMoment(k+1,z,P).

This estimate is uniform in the cutoff and in P. For P=primeFactors(M),
M>0, the product is exactly (phi(M)/M)^(k+1).

### Full logarithmic-simplex denominator

For p>2,

    (1-1/p)^(-2)-1 <= 2/(p-2).

Grouping the avoiding harmonic moment of order two by exact prime support
therefore bounds it above by the two-dimensional Selberg denominator at
the SAME product cutoff z. Combining with the existing factorial harmonic
lower bound gives `pair_denominator_hyperbolic_lower`:

    (phi(M)/M)^2 * log(z+1)^2 / 2
      <= sum_{S subset primesBelow(z+1)\primeFactors(M), product(S)<=z}
           product_{p in S} 2/(p-2),

for z>=1, M>0, and 2|M.

Unlike the earlier first-moment Euler-product argument, this has no loss
from replacing log(z) by log(z)/6 or log(z)/16. It is a finite unconditional
inequality. It does NOT supply the corresponding shifted-prime lower
moment.

### Uniform prime-pair estimate at the original error scale

Use z=2^(30J) and delta=1/10 in the established z^(2+delta) error. The error
is 2^(63J), and the small-prime exceptions cost at most 2^(30J)+1.
Since 2^(63J)+2^(30J)<=2^(64J) for J>=1,
`eventually_prime_pair_explicit_gain_nine_hundred` proves, eventually in J
and uniformly in N,a>0,

    #{q<N: q and a*q+1 are prime}
      <= 2*N/(900*((phi(2a)/(2a))*J*log(2))^2) + 2^(64J)+1.

This is a factor-900 reduction of the INITIAL prime-pair main coefficient
at the same error scale. Relative to the immediately preceding factor-16
bound, the coefficient gain is 900/16.

The uniform J threshold is kept explicit as the predicate
AnalyticSieve.HyperbolicPairAt J and propagated through the cofactor,
progression, and composite-modulus sums. Their error terms remain the old
ones; their main coefficients are reduced accordingly.

### New strongest unconditional exponent

`HyperbolicCompositeGain.lean` uses the same geometric moduli and the same
below-half prime-progression estimates. The new main coefficient is
(8/225)*C instead of 2*C in SharpCompositeGain, where

    C = Sieve.totientRatioAverageConstant >= 1.

The retained-weight proof works whenever a>=298*C. The finite coefficient
inequality used is

    (13312/45)*C*(4*a+1) <= (2*a-1)^2.

`infinite_g_gt_hyperbolic_composite_limit` proves infinitude for every

    gamma < 1/2 + 1/(8*a+2).

Taking a=ceil(298*C) gives the new strongest explicit unconditional theorem:

    infinite_g_gt_hyperbolic_composite_uniform (gamma : Real)
      (hgamma : gamma < 1/2 + 1/(2384*C+10)) :
      {n : Nat | (g n : Real) > (n : Real)^gamma}.Infinite.

`erdos_821_hyperbolic_composite_range` gives the equivalent partial epsilon
range. Exact comparisons verify that the new gain ABOVE ONE HALF exceeds

* 55 times the immediately preceding gain 1/(133136*C+10), and
* 1000 times the earlier binomial gain 1/(2400000*C+10).

These are comparisons of the gains above one half, NOT multiplication of
the whole exponent by 55 or 1000.

### Main task still open

The new range is still fixed and bounded far away from one. It does not
establish arbitrary-root smooth shifted primes, SharpDyadicMomentLower,
or a stronger prime-progression distribution range. In particular, the
new all-order harmonic support/exclusion estimates concern integers and
must not be substituted for the missing shifted-prime lower moments.

Spec.lean is unchanged with its original sorry and SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
The conjecture remains UNSOLVED; there is no complete proof/disproof to
submit, and submit_proof has not been called.


## Mixed one-root/two-root sieve and an explicit fixed exponent

### Completed files and audit

Seven new result files:

* `Submission/MixedHarmonicMoments.lean`
* `Submission/MixedPairSieve.lean`
* `Submission/MixedSieveDenominator.lean`
* `Submission/MixedPrimePairBound.lean`
* `Submission/MixedTotientAverage.lean`
* `Submission/MixedCompositeSieve.lean`
* `Submission/MixedCompositeGain.lean`

All compile with fresh oleans. The 19 declarations audited in
`Submission/MixedCompositeGainCheck.lean` use only `propext`,
`Classical.choice`, and `Quot.sound`. Logs are `/tmp/<module-name>.log`.
The temporary `MixedProbe.lean` was removed. No admission or extra axiom
was introduced in these files.

### Exact local root multiplicities

`pairRootMultiplicity a p = if p | a then 1 else 2` counts the roots of
`q*(a*q+1)` modulo the prime p. For even a, it is positive and strictly
smaller than p. The CRT count and discrepancy are proved using these
actual root multiplicities. No sifting primes have to be discarded.

The generic local error lemmas are uniform in a finite prime pool and
in local weights bounded between zero and a fixed B. For every delta>0,
the squared squarefree-support sum is eventually at most z^(2+delta).
This gives `eventually_mixed_prime_pair_sieve_bound` with denominator
`mixedPairDenominator` and the same error scale as before.

### A single totient-ratio loss

The multiplicative weight

    mixedDivisorWeight(P) = zeta * avoidingZeta(P)

has prime-power value 1 when p is in P and e+1 otherwise. Its harmonic
moment is bounded below by

    product_{p in P}(1-1/p) * harmonicMoment(2,z).

An exact prime-support bound for general nonnegative multiplicative
arithmetic functions embeds this harmonic moment into the mixed sieve
denominator. The result for positive even a is

    (phi(a)/a) * log(z+1)^2/2
      <= mixedPairDenominator(a,z,primes<=z).

The old squared totient-ratio loss has been reduced to one power.
The pending rational identity in `MixedSieveDenominator` was repaired by
providing the explicit nonzero facts for p and p-1 to `field_simp`.

With z=2^(30J), delta=1/10 and the existing dyadic error comparison,
`eventually_prime_pair_mixed_explicit_all` gives, uniformly in positive a
and in N,

    #{q<N: q and a*q+1 prime}
      <= 2N/(900*(phi(a)/a)*(J log2)^2) + 2^(64J)+1.

For odd a, the pair set is contained in {2}, and that exceptional case
is proved separately.

### A small absolute harmonic-average constant

Instead of reusing the very large squared-totient-ratio constant,
`sum_reciprocal_totient_le_three_harmonic` proves

    sum_{1<=n<=K} 1/phi(n) <= 3*H_K.

The proof uses the exact prime-product expansion of n/phi(n), the
existing harmonic prime-product average, and

    sum_{p<=K} 1/(p(p-1)) <= sum_{2<=n<=K+1} 1/(n(n-1)) <= 1.

The latter sum telescopes. The Euler product is at most exp(1)<3.

### Composite moduli and the explicit exponent

Supermultiplicativity phi(d*k)>=phi(d)*phi(k) now directly preserves the
reciprocal-totient progression weight. The family rejected-prime bound is

    sum_{d in M} roughProgressionPrimes(d,Y,X).card
      <= [X*H_K/(75*(J log2)^2)] * sum_{d in M} 1/phi(d)
           + |M|*K*(2^(64J)+2^(16J)+1).

Unlike the earlier family bound, it does not need d<=2*phi(d).
The prime-progression distribution theorem is unchanged.

At the existing structured scales, the required coefficient inequality
is now

    (1664/15)*(4a+1) <= (2a-1)^2.

It is proved for every a>=113. The existing prime-count-to-totient-fiber
transfer then gives every multiplicity exponent

    gamma < 1/2 + 1/(8a+2).

Taking a=113 gives the explicit theorem

    gamma < 227/453 = 1/2 + 1/906.

This threshold is strictly larger than the previous
`1/2 + 1/(2384*totientRatioAverageConstant+10)`; the comparison is also
formalized and audited. The corresponding original-statement range is
`epsilon > 226/453`.

### No settlement of the original conjecture

This is a genuine unconditional fixed-exponent improvement, but it does
not give exponents approaching one. In particular, it remains below the
2/3 threshold needed to transfer an attained multiplicity exponent to
the root-3 endpoint series.

The missing arbitrary-root smooth-shifted-prime estimate or equivalent
sharp all-order shifted-prime moment lower bound has not been proved.
Replacing the original theorem by the fixed-exponent result, or using a
conditional moment theorem without proving its hypothesis, would not
settle the task. Neither was done.

`Submission/Spec.lean` still has SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`
and retains its original import, conjecture statement, and `sorry`.
No complete proof/disproof is available; no `submit_proof()` call has
been made. No unfinished Lean proof repair or background build is pending.

## Cofinal-order geometric-loss moment criterion

### Completed and audited file

`Submission/CofinalMomentCriterion.lean` imports `MomentSmoothTransfer`.
It compiles cleanly with a fresh olean. All six results audited in
`Submission/CofinalMomentCriterionCheck.lean` use only the three permitted
axioms. Logs are `/tmp/CofinalMomentCriterion{,Check}.log`. The scratch
`CofinalMomentProbe.lean` was removed.

This development does not claim or prove a new unconditional moment lower
bound. It weakens the sufficient hypothesis that would settle the original
conjecture.

### Rough bounds at every sufficiently high order

For each t>=2 and theta>1-1/(2t),
`eventually_order_eventually_rough_geometric` proves

    eventually in k, eventually in L,
      roughPrimeMoment(k, X(t,L), Y(L))
        <= theta^k * X(t,L)*log(X(t,L))^(k-2)/(2*k!).

This strengthens the earlier existence of a single order and retains a
geometric coefficient. The proof applies the existing subexponential Euler
cost estimate to rho/theta<1. The scale threshold depends on k; no uniform
order/scale limit is asserted.

`eventually_smooth_count_of_moment_denominator` allows any fixed positive
real denominator D in place of k!: a total lower moment of X log^(k-2)/D
and a rough upper moment of half that size eventually give the same smooth
prime pool count. The proof retains the fixed-order subpower divisor bound.

### Weaker sufficient arithmetic input

The new proposition `CofinalGeometricMomentLower` is

    for every 0<theta<1 and every t>=2, at arbitrarily high orders k>=2,
      at arbitrarily large scales L,
        theta^k * X(t,L)*log(X(t,L))^(k-2)/k!
          <= sum_{p<=X(t,L)} tau(k,p-1).

The order is chosen before the arbitrarily large scales. Unlike the old
`SharpDyadicMomentLower`, the bound need not hold at every order and need
not have coefficient exactly 1/k!. The old hypothesis implies the new one,
as proved in `sharp_moments_imply_cofinal_geometric`.

`erdos_821_of_cofinal_geometric_moments` proves the conditional transfer all
the way to the exact original conjecture. It chooses theta=1-1/(4t), an
order above the rough-bound threshold, and then a scale at which the assumed
total lower bound and the proved rough upper bound both hold.

### Necessary consequence of failure

The formal contrapositive `negation_forces_geometric_moment_upper` says
that failure of the exact conjecture would imply the existence of
0<theta<1, t>=2, and B such that for every k>=max(B,2), eventually in L,

    shiftedPrimeMoment(k,X(t,L))
      < theta^k * X(t,L)*log(X(t,L))^(k-2)/k!.

The original conjecture's negation is an explicit hypothesis; this is not
an assertion or proof of that negation.

### What remains missing

No available lower estimate contradicts this consequence. The fixed-modulus
Dirichlet-series results have the wrong logarithmic order. Merely having an
unbounded coefficient for each fixed k does not allow that coefficient to
be replaced by a growing power of log X. The existing half-level truncated
factorial coefficient also has a fixed geometric loss; increasing k alone
does not remove that loss. No fixed-modulus limit was used with growing
moduli, and no independence of prime-chain branches was assumed.

The strongest unconditional multiplicity exponent remains 227/453 from
`MixedCompositeGain.lean`. The original task is still UNSOLVED.
`Submission/Spec.lean` is unchanged with its original `sorry` and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof/disproof is available and no `submit_proof()` call has
been made. No Lean repair or background build remains pending.

## Unconditional-input recheck after the cofinal moment criterion

Reviewed `VaughanMean`, `CompositeBelowHalfScales`, `StructuredPrimeFactors`,
and the new `CofinalMomentCriterion` for an unconditional way to meet the
weaker lower-moment hypothesis. No new arithmetic lower estimate was obtained.

The active conductor-scale majorant includes Q^2*sqrt(X)/D. For a conductor
block with D comparable to Q, this is Q*sqrt(X); it is power-saving relative
to X only below the square-root modulus scale. The established structured
application retains the explicit condition 2*r+1<=t. It cannot be silently
used in the near-full range of moduli needed by the proposed moment proof.

Mathlib's residue-class L-series lower bound remains a fixed-modulus result.
Its cutoff-dependent constant does not justify choosing a modulus cutoff
exponential in 1/(s-1). Nor does a fixed-order unbounded normalized residue
supply the full logarithmic powers required by the cofinal geometric moment
criterion. No order of limits or lower-bound hypothesis was exchanged.

Also reconsidered weighted parent-chain contraction. A logarithmically
decaying weight can make the full prime series convergent, but contraction
in that finite-mass norm does not imply power sparsity or contradict the
prime count. No such contraction was claimed as an exponent-amplification
argument, and no independence of branches was assumed.

No result file was changed in this check. The strongest unconditional range
is still epsilon>226/453. `Submission/Spec.lean` remains unchanged with its
original `sorry`, and the task is UNSOLVED. No complete proof/disproof is
ready for submission, and no Lean repair or background build is pending.


## Reciprocal-totient constant two and exponent 153/305

### Completed files and verification

* `Submission/ReciprocalTotientTwo.lean`
* `Submission/TwoCompositeSieve.lean`
* `Submission/TwoCompositeGain.lean`
* `Submission/TwoCompositeGainCheck.lean`

All result files compile cleanly with fresh oleans. Ten declarations are
audited in the check file, and each depends only on `propext`,
`Classical.choice`, and `Quot.sound`. Logs are `/tmp/<module-name>.log`.
The scratch `TotientTwoProbe.lean` was removed, and no admission remains in
these result files.

### A finite Euler-product estimate

`sum_reciprocal_successive_tail` proves the uniform telescoping bound

    sum_{a<n<=b} 1/(n(n-1)) <= 1/a,  a>=1.

The local reciprocal-totient Euler product is split at 29. The small-prime
factors are evaluated exactly over {2,3,5,7,11,13,17,19,23,29}. For the
remaining factors, 1+x<=exp(x), the telescoping tail, and
exp(1/29)<=29/28 give

    product_{p<=A}(1+1/(p(p-1)))
      <= product_{p<=29}(1+1/(p(p-1))) * 29/28
      = 11771754662577/5891090022400
      < 2.

This is a rigorous finite rational calculation, not a numerical estimate
of an unproved prime distribution. `reciprocal_totient_euler_product_le_two`
exports the weaker non-strict upper bound 2, uniformly in A.

The harmonic prime-product average then proves

    sum_{1<=n<=A} 1/phi(n) <= 2*H_A.

This replaces the previous absolute constant 3. The mixed local root count
and pair-sieve error estimates are unchanged.

### Propagation to the multiplicity exponent

`TwoCompositeSieve` reuses `MixedPairAt`. The rejected-prime family bound
now has main coefficient 2/225 instead of 1/75:

    [2*X*H_K/(225*(J log2)^2)] * sum_{d in M} 1/phi(d),

with the same finite error as before. No new modulus-distribution theorem
or wider range is assumed.

At the structured scales the required coefficient inequality becomes

    (3328/45)*(4a+1) <= (2a-1)^2.

It is proved for every a>=76. Choosing a=76 in the existing smooth-prime
count transfer yields

    gamma < 1/2 + 1/(8*76+2) = 153/305.

The theorem `infinite_g_gt_two_composite_uniform` gives infinitude of the
original multiplicity inequality for every such gamma, and
`erdos_821_two_composite_range` expresses it as epsilon>152/305. The strict
comparison 227/453<153/305 is also formalized.

### Original task remains incomplete

This is an unconditional fixed-exponent improvement, not an iteration or
an approach to exponents arbitrarily close to one. It does not supply the
cofinal geometric moment lower bound, the missing arbitrary-root smooth
shifted-prime estimate, or an exponent-amplification theorem.

`Submission/Spec.lean` remains unchanged with its original statement and
`sorry`, SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The conjecture is UNSOLVED. No complete proof or disproof is available to
submit. No Lean repair or background build remains pending.

## Common-denominator modulus-family recheck

Investigated whether moduli dividing a common integer could evade the
quadratic-spacing loss in the large-sieve route. Reviewed
`AdditiveLargeSieve`, `MultiplicativeLargeSieve`, `SmoothModulusSpacing`,
and `SmoothModulusSieveMass`.

The existing general constant-mode test already gives B>=sum_{d in D}phi(d)
for a uniform additive coefficient bound with constant B. If every modulus
in a block satisfies phi(d)>=c*D0, then, writing H=sum 1/phi(d), elementary
termwise comparison gives

    B >= c^2*D0^2*H.

Consequently a numerical bilinear majorant of size B*sqrt(X)/D0 cannot
be made small relative to the main weight X*H merely by reducing the
number of moduli when D0 exceeds the corresponding square-root scale.
This concerns the proposed upper majorant, not a lower bound on the actual
progression error. It does not rule out estimates specialized to arithmetic
coefficients, signed cancellation, or dispersion methods.

For the common-denominator proposal, improved spacing is therefore not by
itself a new prime-supply theorem; the sparse-family main term must be
controlled at the same time. No arithmetic-specific cancellation estimate
or exponent amplification was obtained in this recheck. No new Lean result
file was added, and no unproved arithmetic estimate was assumed.

The strongest unconditional result remains `TwoCompositeGain.lean`, giving
all exponents gamma<153/305, equivalently epsilon>152/305 in the original
inequality. `Submission/Spec.lean` remains unchanged with its original
`sorry`. The conjecture is UNSOLVED; no complete proof/disproof is ready to
submit, and no Lean repair or background build is pending.


## Even-cofactor restriction and exponent 103/205

### Completed files and audit

* `Submission/EvenReciprocalTotient.lean` (88 lines)
* `Submission/EvenCompositeSieve.lean` (89 lines)
* `Submission/EvenCompositeGain.lean` (246 lines)
* `Submission/EvenCompositeGainCheck.lean`

The three result files compile cleanly with fresh oleans. All twelve
audited declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. Logs are `/tmp/<module-name>.log`. The scratch probe
`EvenTotientProbe.lean` was removed. No sorry/admit/extra axiom remains
in these result files.

### Exact parity mass bound

Write E(A)=sum_{n<=A, even n}1/phi(n) and
O(A)=sum_{n<=A, odd n}1/phi(n). The identities for phi(2n) give the exact
recurrence

    E(A) = O(floor(A/2)) + E(floor(A/2))/2.

Strong induction and monotonicity of O then prove E(A)<=2*O(A), hence

    E(A) <= (2/3)*(E(A)+O(A)) <= (4/3)*H_A.

This is a uniform finite-prefix inequality, not only an asymptotic one.
It is exported as `even_reciprocal_totient_le_four_thirds_harmonic`.

### Keeping the parity restriction in the prime-pair sum

For odd d, an odd k makes d*k odd; the existing prime-pair lemma shows
that at most one prime q can satisfy both q and d*k*q+1 prime. That one
exception is absorbed by the existing error term, rather than assigned
a reciprocal-totient main term. For even k the mixed-root sieve is used
as before.

The main coefficient in the family bound is therefore 4/675, compared
with 2/225 in `TwoCompositeSieve`. The new family theorem has the explicit
additional hypothesis that each modulus is odd. `primeProductModuli_odd`
proves that hypothesis for the structured moduli at positive block index.
The modulus distribution range and sieve error scales are unchanged.

### Fixed-exponent consequence

The structured main-coefficient inequality is now

    (6656/135)*(4a+1) <= (2a-1)^2,

proved for a>=51. The existing smooth-prime count transfer at a=51 gives

    gamma < 1/2 + 1/(8*51+2) = 103/205.

`infinite_g_gt_even_composite_uniform` is unconditional.
`erdos_821_even_composite_range` states the resulting original-inequality
range epsilon>102/205. The strict comparison 153/305<103/205 is also proved
and audited.

### Remaining gap and possible finite refinement

This is still a fixed exponent, not exponents tending to one. The all-order
moment lower bound and arbitrary-root smooth shifted-prime supply remain
unproved. No exponent-amplification theorem has been obtained.

A possible further constant refinement (NOT yet proved here) is to avoid
the factor two from floor(X/a)+1 <= 2X/a in `eventually_mixed_pair_at`.
Keeping the additive endpoint correction would halve that main term, but
its uniform absorption into the sieve error must be proved at the actual
structured scales. Such a refinement would still not widen the underlying
modulus-distribution range or settle arbitrary epsilon.

`Submission/Spec.lean` remains unchanged, with its original statement,
import, and `sorry`, SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The original task is UNSOLVED. No complete proof/disproof is ready to
submit; no Lean repair or background build is pending.


## Endpoint correction retained and exponent 53/105

### Completed files and verification

* `Submission/EndpointPrimePairBound.lean` (101 lines)
* `Submission/EndpointCompositeSieve.lean` (90 lines)
* `Submission/EndpointCompositeGain.lean` (241 lines)
* `Submission/EndpointCompositeGainCheck.lean`

All three result files compile without errors or warnings and have fresh
oleans. Twelve audited declarations depend only on the three permitted
axioms. The check log is `/tmp/EndpointCompositeGainCheck.log`; result
logs are `/tmp/<module-name>.log`. No admissions remain in these files.
The scratch `EndpointPairProbe.lean` was removed.

An initial build of `EndpointPrimePairBound` produced no olean because an
explicit specialization of a factorial constant caused excessive evaluation.
It was repaired by first proving a generic existential constant bound with
a symbolic parameter, and then specializing the theorem. All builds and
audits above are for the repaired version; there is no pending process.

### Uniform endpoint-error control

`exists_totient_ratio_power_bound` derives, for each positive k, a constant
C>=0 such that

    (a/phi(a))^(k+1) <= C*a,  a>0.

This uses the existing `input_pow_le_totient_pow` theorem. At k=31,
`eventually_totient_ratio_box` gives, eventually in J, uniformly in
positive a<=2^(256J),

    a/phi(a) <= 2^(16J).

The proof keeps the constant symbolic; no enormous factorial is evaluated.

The previous bound floor(X/a)+1<=2X/a doubled the main term.
`EndpointPairAt` instead retains floor(X/a)+1<=X/a+1. Its additive correction
is

    a/(450*phi(a)*(J log2)^2),

which is at most 2^(16J) for sufficiently large J under the coefficient cap.
This fits the already present error budget. The resulting uniform bound is

    primePairCofactorCount(X,a)
      <= X/(450*phi(a)*(J log2)^2) + 2^(64J)+2^(16J)+1,

for positive a<=X with a<=2^(256J). The extra cap is explicit in the
proposition, not omitted or silently assumed.

### Composite families and the cap at structured scales

The even-cofactor argument from `EvenCompositeSieve` is propagated with
the improved pair main term. The family coefficient is now 2/675, with the
same error as before. The family theorem additionally requires
Q*K<=2^(256J), ensuring the coefficient cap for every d*k being summed.

At the strict structured scales, the cap follows from

    2^(64*(2a)*(m+1)) * 2^(64*m)
      <= 2^(256*(2a-1)*m),

proved for a>=1 and m>=max(2,a). Thus no unproved uniformity condition
remains when the family estimate is used.

The required main-coefficient inequality becomes

    (3328/135)*(4a+1) <= (2a-1)^2,

proved for a>=26. Taking a=26 in the existing smooth-prime transfer gives

    gamma < 1/2 + 1/(8*26+2) = 53/105.

`infinite_g_gt_endpoint_composite_uniform` and
`erdos_821_endpoint_composite_range` are unconditional. The latter gives
the original inequality for epsilon>52/105. The strict comparison
103/205<53/105 is formalized and audited.

### The exact original conjecture is still unproved

This removes an avoidable fixed factor; it does not change the
below-square-root progression distribution range. It supplies neither
the cofinal geometric shifted-prime moment lower bound nor an
amplification giving exponents arbitrarily close to one.

`Submission/Spec.lean` still has its original import, statement, and
`sorry`, with SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The task remains UNSOLVED, and no complete proof or disproof is ready
for submission. No Lean repair or background build is pending.


## Independent structured parameters: exponent 2041/4001

### Completed files and audit

The previously proposed separation of the parameters is now complete:

- `Submission/IndependentCompositeScales.lean`
- `Submission/IndependentCompositeGain.lean`
- `Submission/IndependentCompositeBarrier.lean`
- `Submission/IndependentCompositeGainCheck.lean`

All three result files compile successfully with fresh oleans. The check
file checks the exact fixed-exponent type and audits twelve results;
they use only `propext`, `Classical.choice`, and `Quot.sound`.
The corresponding logs are in `/tmp/IndependentComposite*.log`.

### Generic estimates

The parameters `r,t,b,h` are fixed independently, subject to

```
r+b+h=t,
2*r+1 <= t,
2 <= b,
1 <= h,
t+5 <= 5*b,
(8320/675)*t*h <= (17/32)*(b-1)^2.
```

At scale m, use X=2^(64*t*m), Y=2^(64*b*m), K=2^(64*h*m),
and J=(b-1)*m. The block-prime moduli still have r factors. The cap
Q*K<=2^(256J) is checked for m>=r, without weakening the endpoint sieve
hypothesis. The main rejected weight is at most (17/32)*X*W, and the
sieve plus prime-power errors are eventually at most X*W/64. The
progression lower weight is (9/16)*X*W. Hence the retained weight is at
least X*W/64.

The sieve error is at most

```
3*2^(64*r) * 2^((64*t-1)*m).
```

Its logarithm-weighted combination with the prime-power error is at most

```
independentErrorConstant r t * (m+1) * 2^((64*t-1)*m),
independentErrorConstant r t = 64*t*(3*2^(64*r)+2*choose(t-1,r)).
```

The eventual polynomial-versus-exponential bound absorbs this error,
using the existing lower reciprocal mass. The retained prime count is

```
X <= 2*structuredPrimeCountConstant r t * (m+1)^(r+1) * |P|.
```

The count transfer proves every gamma<1-b/t. All constants were kept
symbolic before specializing, avoiding evaluation of huge binomial or
factorial terms.

### Explicit specialization

The values

```
r=2000, t=4001, b=1960, h=41
```

satisfy all six conditions by exact arithmetic. This proves every
multiplicity exponent gamma<2041/4001 (approximately 0.510122), or every
epsilon>1960/4001 in the original assertion. In particular the original
inequality holds for every epsilon>49/100.

### Why parameter tuning here cannot settle the conjecture

The new numerical barrier proves that the conditions

```
r+b+h=t,
2*r+1 <= t,
2 <= b,
(8320/675)*t*h <= (17/32)*(b-1)^2
```

already imply `489*t < 1000*b`, hence `1-b/t < 511/1000`.
Indeed, if b/t<=489/1000, the half-level constraint forces
h/t>=11/1000, and the main coefficient exceeds its allotted budget.
This proof does not need the additional cutoff condition. The barrier
is only to these sufficient parameter inequalities. It is not a lower
bound on the actual rejected count, not a universal sieve impossibility
result, and not an upper bound for g.

Thus this completed refinement cannot supply exponents approaching one,
even with arbitrarily large fixed parameters. The cofinal moment lower
hypothesis and the higher-root endpoint-series divergence remain
unproved. No full settlement has been obtained.

`Submission/Spec.lean` is unchanged with SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
Its original `sorry` remains. No valid complete proof or disproof is ready
to submit. No Lean repair or background build is pending.


## Finite order mixtures and the moving-order quantifier check

### New audited auxiliary files

- `Submission/FiniteOrderMixtures.lean`
- `Submission/MovingOrderMoments.lean`
- `Submission/FiniteOrderMixturesCheck.lean`

Both result files compile with fresh oleans. Eleven results, including the
conditional implication to the original statement, were axiom-audited with
only `propext`, `Classical.choice`, and `Quot.sound`. The check file also
checks the exact finite-mixture equivalence and moving-order proposition.
Logs are `/tmp/FiniteOrderMixtures.log`, `/tmp/MovingOrderMoments.log`, and
`/tmp/FiniteOrderMixturesCheck.log`.

### Fixed finite mixtures do not weaken the missing arithmetic input

`FiniteMixtureMomentLower` allows, for each theta, t, and lower order bound B,
a fixed finite set K of orders at least max(B,2). At arbitrarily large scales
L, nonnegative weights w(k) may be chosen afresh, provided some weight is
positive and the weighted moment sum dominates the weighted factorial targets.

`finite_mixture_iff_cofinal_geometric` proves this equivalent to the earlier
`CofinalGeometricMomentLower`. A finite nonnegative sum inequality yields at
least one component inequality; finite pigeonhole over cofinally many scales
fixes an order. Conversely, singletons give the mixture assertion. Thus this
mixture criterion remains UNPROVED, not an unconditional prime-moment theorem.

The numerical coefficient lemma is uniform over every finite set of
sufficiently high orders and every nonnegative weight function: for fixed
0<=theta<rho, rho>0, and c>0, eventually all such mixtures satisfy

```
sum_k w(k)*(k+1)*theta^k/k!
  <= c*sum_k w(k)*rho^k/(k+1)!.
```

Consequently nonnegative mixing cannot eliminate the geometric loss in the
currently truncated, symmetrized lower coefficients. This is only a comparison
of coefficients, not an upper bound for the actual prime moments.

### Choosing the order after the scale is already trivially true

For every fixed X>=2 and real theta,

```
theta^k * X * log(X)^(k-2) / k! -> 0 as k -> infinity.
```

The term p=2 contributes tau(k,1)=1 to shiftedPrimeMoment(k,X) for every k.
Hence, at every fixed scale, all sufficiently high orders meet the proposed
factorial lower target using that single prime alone.

`moving_order_dyadic_lower` establishes unconditionally

```
forall theta, t>=1, B, M,
  exists L>=M, exists k>=max(B,2),
    theta^k X(t,L) log(X(t,L))^(k-2)/k! <= shiftedPrimeMoment(k,X(t,L)).
```

This is NOT the sufficient hypothesis, whose order k must be fixed before
arbitrarily large scales are taken. The unconditional swapped-quantifier
statement cannot be fed to the fixed-order rough-moment estimates. No such
invalid interchange was used.

### Other checks and remaining status

The exact symmetric hyperbola identity was rechecked: it retains the
uncontrolled all-small-factor remainder and gives only a polynomial order
factor in its controlled term. No new total-moment lower bound was obtained.
An attempted check of current external literature failed because the
environment cannot resolve `www.erdosproblems.com`; no claim about newly
published results is inferred from that failure.

The strongest completed unconditional multiplicity result remains
`infinite_g_gt_independent_uniform`, for gamma<2041/4001. The exact conjecture
remains UNSOLVED. `Submission/Spec.lean` retains its original `sorry` and
SHA-256 `8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof or disproof is ready to submit. No Lean repair or background
build is pending.


## Logarithmic overlap lower bound and compact-pool limitation

### Completed and audited modules

- `Submission/LogarithmicOverlap.lean`
- `Submission/CompactPrimePool.lean`
- `Submission/LogarithmicOverlapCheck.lean`

Both result modules compile cleanly and have fresh oleans. Twelve results
were audited with only `propext`, `Classical.choice`, and `Quot.sound`.
The check file verifies the exact finite lower-pair-count type as well.
Logs: `/tmp/LogarithmicOverlap.log`, `/tmp/CompactPrimePool.log`, and
`/tmp/LogarithmicOverlapCheck.log`.

### A genuine finite lower overlap estimate

For a finite family F of squarefree inputs, all with totient n, contained
in a finite input-prime pool P, let

```
M = |F|,
w(p) = log(p-1),
W = sum_{p in P} w(p),
c(p) = |{a in F : p divides a}|,
O = sum_{a,b in F} log(phi(gcd(a,b))).
```

Exact double counting gives

```
M log n = sum_p w(p)c(p),
O = sum_p w(p)c(p)^2.
```

Weighted Cauchy--Schwarz therefore proves `(M log n)^2 <= W O`.
There is no assumption of independence of the prime incidences. If E is the
number of ordered pairs with phi(gcd)>=n^eta, the finite pointwise logarithmic
bound yields

```
O <= eta*log(n)*M^2 + (1-eta)*log(n)*E,
M^2*(log(n)-eta*W) <= (1-eta)*W*E.
```

If additionally `W<=C log n`, and `0<=eta<=1`, the coefficient form is

```
(1-C*eta)*M^2 <= C*(1-eta)*E.
```

This would give a fixed positive pair proportion for eta<1/C. However,
the compact-pool hypothesis cannot hold for polynomial-size squarefree
families at arbitrarily large scales, as the next theorem shows.

### Compact logarithmic pools support only subpower families

The support map injects F into the powerset of P, so `|F|<=2^|P|`.
For every R>=2, splitting P at R gives

```
|P| <= R+1 + W/log R,
log |F| <= (R+1)log 2 + (log 2/log R)*W
```

when F is nonempty. Choosing R first, then allowing the output scale to grow,
proves uniformly over all F and P:

```
for every C>0 and epsilon>0, eventually in n,
  W<=C log n -> |F|<=n^epsilon.
```

Only squarefreeness and prime-factor containment are needed for this result;
the inputs need not even have a common totient. It follows that for a
polynomial-size family, W/log n eventually exceeds every fixed constant.

`eventually_large_family_cauchy_coefficient_negative` makes the limitation
of this new overlap estimate explicit: at any fixed positive eta and alpha,
eventually every such family with |F|>n^alpha satisfies

```
log n - eta*W < 0.
```

Thus the Cauchy-derived lower pair bound cannot supply the positive-power
overlap threshold required by the existing LCM amplification theorem for
these large families. This is NOT a statement that the actual overlap count
is small, not an impossibility theorem for all LCM arguments, and not a
disproof of Erdős 821.

### Original task status

No new unconditional multiplicity exponent was obtained. The strongest
completed range remains gamma<2041/4001, equivalently epsilon>1960/4001.
The exact original conjecture is UNSOLVED. `Submission/Spec.lean` remains
unchanged with its original `sorry` and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof or disproof is ready to submit. There is no pending Lean
repair or background build.


## Uniform gcd moments and quadratic prime-pool weights at records

### Completed auxiliary modules

- `Submission/RecordGcdMoments.lean`
- `Submission/RecordGcdMomentsApplications.lean`
- `Submission/RecordGcdMomentsCheck.lean`

Both result modules compile cleanly, with fresh oleans. Nine results were
audited using only `propext`, `Classical.choice`, and `Quot.sound`. The check
file also verifies the exact power-moment inequality with its tsum constant.
Logs: `/tmp/RecordGcdMoments.log`, `/tmp/RecordGcdMomentsApplications.log`, and
`/tmp/RecordGcdMomentsCheck.log`.

### Uniform moment estimate

At a normalized record of gAvoiding(K,n)/n^s, the earlier common-core bound
controls the divisibility frequency of every positive integer d by
phi(d)^(-s). Grouping ordered pairs by their exact gcd and squaring those
frequencies now proves

```
sum_{a,b in avoidingFiber(K,n)} phi(gcd(a,b))^t
  <= gAvoiding(K,n)^2 * sum_{d>=0} phi(d)^(-(2*s-t))
```

whenever `1 < 2*s-t`. The series is summable by the existing inverse-totient
first-moment theorem. The constant depends only on s and t, not on K or n.
No independence of divisibility at different primes is required.

Markov's inequality yields the uniform large-overlap upper bound

```
n^(eta*t) * |{(a,b): phi(gcd(a,b))>=n^eta}|
  <= gAvoiding(K,n)^2 * recordGcdConstant(s,t)
```

for t>=0. The exponent range t<2s-1 is weaker than the asymptotic exponent in
the earlier divisor-loss upper bounds when s<1; the new feature is a constant
uniform in both K and n and the full moment estimate. This is an UPPER bound,
not the lower overlap supply needed for LCM amplification.

### Logarithmic overlap and quadratic pool weight

For s>1/2, take a fixed positive t with 2s-t>1. The elementary inequality
log x <= x^t/t proves a uniform bound

```
overlap(avoidingFiber(K,n)) <= C(s)*gAvoiding(K,n)^2.
```

Combining it with the previously proved exact logarithmic incidence identity
and weighted Cauchy--Schwarz gives, for every positive full record fiber and
every finite prime pool P containing all its input-prime factors,

```
(log n)^2 <= C(s)*poolWeight(P).
```

This refines the earlier qualitative W/log n divergence for these record
fibers. It is only a necessary support-weight lower bound, not an existence
or amplification theorem for smaller pools.

### Application of the independent-parameter exponent

`infinite_gAvoiding_independent_range` updates fixed-prime exclusion to the
strongest completed range: every 0<gamma<2041/4001 is attained infinitely
often outside any prescribed fixed prime support.

For every 1/2<alpha<2041/4001, the new application supplies arbitrarily large
full prime-excluded record fibers with size greater than n^alpha, a positive
uniform gcd-totient moment, and the quadratic logarithmic pool-weight bound.
The constants are independent of the fixed exclusion parameter K. This
preserves the source exponent; it does NOT increase it.

### Original task remains incomplete

No proof or disproof of the original conjecture has been obtained. The
strongest unconditional exponent remains gamma<2041/4001, equivalently
epsilon>1960/4001 in the original assertion. `Submission/Spec.lean` is
unchanged and retains its original `sorry`, with SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No valid complete proof is ready for submission, and no Lean repair or
background build is pending.

## Continuation recheck: arithmetic lower bound still missing

Re-ran `IndependentCompositeGainCheck.lean` and
`RecordGcdMomentsCheck.lean`; both exited successfully, and all printed
axiom dependencies are among propext, Classical.choice, and Quot.sound.
Fresh logs are `/tmp/IndependentCompositeGainCheck.current.log` and
`/tmp/RecordGcdMomentsCheck.current.log`.

Reviewed the cofinal fixed-order moment criterion and the record-GCD
bounds. No implication from the latter upper overlap estimates to the
required lower overlap supply was obtained. Further informal consideration
of tensor products, predecessor padding, and prime-support entropy did
not yield a new arithmetic lower bound or an exponent improvement. No new
Lean theorem was added in this continuation.

The exact conjecture remains UNSOLVED. `Submission/Spec.lean` is unchanged,
with SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
Its original sorry remains. No complete proof or disproof is ready for
submission, and no verification submission was made.

## Polynomial logarithmic pool-weight bound, without record hypotheses

### Completed files and audit

New files:

- `Submission/PolynomialPoolWeight.lean` (266 lines)
- `Submission/PolynomialPoolWeightApplications.lean` (48 lines)
- `Submission/PolynomialPoolWeightCheck.lean` (25 lines)

Both result modules compile cleanly with fresh oleans. Eleven declarations
were axiom-audited, all using only propext, Classical.choice, and Quot.sound.
The check file also checks the exact uniform eventual lower bound, with
poolWeight expanded. Logs are `/tmp/PolynomialPoolWeight.log`,
`/tmp/PolynomialPoolWeightApplications.log`, and
`/tmp/PolynomialPoolWeightCheck.log`. The temporary PoolProbe was removed.

### General finite bound

For a finite family F with phi(a)=n>0 for every a in F, and a finite prime
pool P containing every a.primeFactors, the support map is injective even
without squarefreeness. Its weighted count gives

```
|F| * n^(-s) <= product_{p in P} (1+(p-1)^(-s))
log |F| <= s log n + sum_{p in P} (p-1)^(-s),  s>=0, F nonempty.
```

For 0<=s<=t and t>1, a finite positive-integer sum is bounded by splitting
at its cardinality plus one and using the convergent t-series. Combined
with the existing pool cardinality bound at cutoff 2, this proves

```
log |F| <= s log n + poolRankinConstant(s,t)*(poolWeight(P)+1)^(t-s),

poolRankinConstant(s,t) =
  (sum_{d>=0} d^(-t)+1)*(4+1/log 2)^(t-s).
```

### Uniform polynomial logarithmic consequence

For every C>=0, 0<alpha<1, and beta>0 with beta*(1-alpha)<1,
uniformly over all finite fibers and containing prime pools, eventually
in n,

```
|F| > n^alpha  ==>  poolWeight(P) > C*(log n)^beta.
```

This is `eventually_large_fiber_requires_polynomial_pool`. It does NOT
require squarefreeness or a normalized-record hypothesis. The choice of
parameters has s<alpha, t>1, and beta*(t-s)<1, so the logarithmic error
is strictly sublinear in log n.

This strengthens the earlier quadratic record-pool estimate: whenever
alpha>1/2, beta can be taken greater than 2. It is a necessary support
condition, not a lower-bound construction for g.

### Unconditional application preserving the exponent

`exists_large_fiber_with_polynomial_pool_bound` supplies arbitrarily large
restricted fibers for every 0<alpha<2041/4001 and every fixed prime
exclusion K>0, with the above pool bound.

The explicit `exists_large_fiber_with_superquadratic_pool_bound` takes
alpha=51/100 and beta=51/25. Thus, for every C>=0 and fixed K>0, there
are arbitrarily large n with

```
gAvoiding(K,n)>n^(51/100)
```

and every containing prime pool has weight greater than
`C*(log n)^(51/25)`. There is NO increase in the multiplicity exponent.

### Original task status

The missing arithmetic lower bounds are still missing. No implication
from this necessary pool-weight estimate to larger multiplicity exponents
was established. The conjecture is UNSOLVED. `Submission/Spec.lean` remains
unchanged with its original sorry and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof or disproof is ready to submit. No Lean repair or
background build remains pending.


## Chebyshev factorial-ratio arithmetic input and exponent 2064/4001

### Completed files and audit

- `Submission/ChebyshevFactorialLower.lean` (215 lines)
- `Submission/ChebyshevCompositeGain.lean` (200 lines)
- `Submission/ChebyshevCompositeGainCheck.lean` (30 lines)

Both result modules compile cleanly, with fresh oleans. Sixteen main
results were axiom-audited, all with dependencies among propext,
Classical.choice, and Quot.sound. Exact-type examples check the exponent
and epsilon formulations. Logs: `/tmp/ChebyshevFactorialLower.log`,
`/tmp/ChebyshevCompositeGain.log`, and
`/tmp/ChebyshevCompositeGainCheck.log`. The temporary ChebProbe was removed.

### A genuinely stronger arithmetic lower bound

The finite integer inequality

```
j-floor(j/2)-floor(j/3)-floor(j/5)+floor(j/30) <= 1
```

is proved by omega. The exact factorial identity

```
log(N!) = sum_{d=1}^N Lambda(d)*floor(N/d)
```

then proves

```
log(N!)-log(floor(N/2)!)-log(floor(N/3)!)-log(floor(N/5)!)
  +log(floor(N/30)!) <= mangoldtSum N.
```

For N=30m, Mathlib's Stirling limit yields the normalized limit

```
A = log 30 - (1/2)log 15 - (1/3)log 10 - (1/5)log 6
  = (14/30)log 2 + (9/30)log 3 + (5/30)log 5.
```

Elementary logarithm inequalities prove A>9/10. Monotonicity of the
Mangoldt sum transfers the estimate from 30m to every sufficiently large
integer cutoff. The resulting theorem is

```
eventually_mangoldt_nine_tenths :
  eventually N, (9/10)*N <= mangoldtSum N.
```

No prime number theorem or shifted-prime lower hypothesis is assumed.

### Transfer through the structured sieve

The existing product-modulus distribution error is eventually at most
X*W/64, where W is the reciprocal-totient modulus mass. Together with
psi(X)>=0.9X this gives aggregate progression weight at least (7/8)*X*W.
The existing error bound and the rejection sieve are retained unchanged.

The sufficient parameter conditions are now

```
r+b+h=t,
2*r+1 <= t,
2 <= b,
1 <= h,
t+5 <= 5*b,
(8320/675)*t*h <= (27/32)*(b-1)^2.
```

The rejected main weight is at most (27/32)*X*W; the remaining errors are
at most X*W/64. Therefore retained weight is at least X*W/64. As before,
the polynomial-count transfer gives every gamma<1-b/t.

The verified specialization is

```
r=2000, t=4001, b=1937, h=64,
gamma < 2064/4001 ≈ 0.515871.
```

`erdos_821_chebyshev_range` proves the corresponding original inequality
for every epsilon>1937/4001. The old coefficient barrier with 17/32 does
not apply after this new arithmetic lower input. No iteration toward
exponent one is claimed or proved. Older restricted-fiber and record
application modules still state their previous numerical exponent ranges.

### Remaining gap

This is a genuine fixed-exponent improvement, but it does not prove the
required assertion for every epsilon>0. The fixed-order shifted-prime
moment lower bound and the arbitrary-root smooth shifted-prime abundance
criterion remain unproved. Spec.lean is unchanged, with SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
Its original sorry remains. No complete proof or disproof is ready for
submission, and no verification submission was made.

## Weighted factorial-ratio and finite-fiber follow-up (no new theorem)

Investigated whether the new Chebyshev factorial-ratio input extends to
high shifted-prime divisor moments. With weight
w_k(d)=Lambda(d)*tau_k(d-1), the same finite floor-kernel identity involves

```
F_k(X)=sum_{d<=X} w_k(d)*floor(X/d).
```

The transform F_k(X)-F_k(X/2)-F_k(X/3)-F_k(X/5)+F_k(X/30) is at most the
corresponding shifted Mangoldt moment. For k=1 the convolution reduces
to log(X!), but that factorial identity does not hold at higher orders.
No sufficiently precise lower estimate for the higher-order F_k was
obtained. Thus the completed Stirling argument cannot simply be cited
as a proof of the missing high moments. This follow-up was informal;
no new Lean theorem or source file was added.

Also revisited finite-support collision energy, large-prime grouping,
and output-prime stripping. No exponent-increasing construction was
obtained; these reviews do not change the existing conditional criteria.
A fresh attempt to access https://www.erdosproblems.com/821 failed with
curl error 6 (DNS resolution failure), so no newer literature was verified.

The strongest completed unconditional range remains gamma<2064/4001,
or epsilon>1937/4001 in the original assertion. The original conjecture
is still UNSOLVED. Spec.lean is unchanged with its original sorry and
SHA-256 8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof or disproof was submitted, and no auxiliary Lean proof
repair or background build is pending.

## Exact endpoint-series recheck and wide-modulus-pool idea

Reviewed the weaker exact endpoint-series criterion rather than requiring
the sharper cofinal moment hypothesis. The first unresolved integer root
is still k=3, requiring nonsummability of d^(-2/3) over prime predecessors
d whose every prime divisor q satisfies q^3<=d. The attained exponent
2064/4001 is less than 2/3, so the proved implication from an attained
multiplicity exponent cannot establish this case.

Considered replacing thin geometric block pools by products of primes in
fixed positive logarithmic-width intervals. Analytically, such a change
could remove polynomial logarithmic losses in the prime count, provided
the conductor and incidence estimates were generalized. It would not by
itself change the smoothness-exponent limitation or prove the cube-root
endpoint case. No new density theorem was assumed or formalized.

No new Lean theorem or source-file change was made in this continuation.
The exact conjecture remains UNSOLVED; the strongest verified range is
still gamma<2064/4001, equivalently epsilon>1937/4001. Spec.lean retains
its original sorry, unchanged. No complete proof/disproof is ready to
submit and no pending auxiliary proof repair or background build exists.

## Wide logarithmic modulus pools: completed reciprocal-density theorem

### New modules and audit

```
Submission/WidePrimeProducts.lean
Submission/WideConductorScales.lean
Submission/WidePrimePools.lean
Submission/WideDistribution.lean
Submission/WideIncidences.lean
Submission/WideSecondSieve.lean
Submission/WideReciprocalDensity.lean
Submission/WideProofCheck.lean
```

The seven result modules compile cleanly with fresh oleans. The check file
has an exact-type example for the final reciprocal-divergence theorem and
fifteen `#print axioms` checks, all using only propext, Classical.choice,
and Quot.sound. Logs are `/tmp/Wide*.log` (in particular
`/tmp/WideProofCheck.log`). No source imports Spec.lean or assumes its sorry.

### Completed construction

With progressionScaleN(s)=2^(64*s), use disjoint prime pools

```
P_m: progressionScaleN(10000*m) <= p <= progressionScaleN(10001*m)
Q_m: progressionScaleN(10001*m) <= q <= progressionScaleN(10002*m)
M_m = {p*q : p in P_m, q in Q_m}.
```

The common interval endpoint is never prime, so the pools are disjoint.
Multiplication on P_m x Q_m is injective. The reciprocal-totient mass
factors exactly, and is at least

```
1 / ((2048*10001)*(2048*10002))
```

for m>=1. The conductor majorant is at most

```
W(Q_m)*primitivePoolMean(P_m,N)
+ W(P_m)*primitivePoolMean(Q_m,N)
+ primitivePoolMean(M_m,N).
```

A generic finite-pool primitive-character mean theorem is proved, and
`wide_primitive_mean_bound` controls pools in logarithmic intervals under
explicit power-saving conditions. At N=2^(64*40020*m), it applies to both
the one-factor range [2^(64*10000*m),2^(64*10002*m)] and the two-factor
range [2^(64*20000*m),2^(64*20004*m)]. The total conductor plus lifting
error is bounded by C*(m+1)^6*2^(2561279*m), with explicit fixed natural C.
Consequently, the aggregate progression weight is eventually at least
(7/8)*N*W(M_m).

The second sieve uses

```
D = 2^(64*20000*m)
Q = 2^(64*20004*m)
Y = 2^(64*19400*m)
K = 2^(64*620*m)
J = 19395*m.
```

The exact scale inequalities and the endpoint coefficient calculation are
verified. The rejected main weight is at most (27/32)*N*W(M_m). The sieve
error and proper prime-power error together are eventually at most
N*W(M_m)/64. Every n with 0<n<N has at most four prime divisors in P_m union
Q_m, so at most sixteen incident moduli. This uniform incidence bound is
used for both ordinary primes and proper prime powers.

`eventually_wide_smooth_prime_count` proves

```
N <= wideCountConstant*m*|smoothPrimePool(N,Y)|
wideCountConstant = 64*16*(64*40020)*wideMassDenominator.
```

After discarding primes at most 2^(64*40019*m), the retained primes satisfy
q^40019 <= (p-1)^19400 for every prime divisor q of p-1. The one-logarithm
count and `not_summable_reciprocal_of_eventual_dyadic_count` give

```lean
theorem wide_prime_reciprocal_divergence :
    ¬Summable ((rationalSmoothShiftedPrimes 40019 19400).indicator
      (fun p : Nat => 1/(p : Real)))
```

All names are in namespace Erdos821; smoothPrimePool is in
Erdos821.HigherDivisors.

### Scope and remaining gap

This implements the wide-pool plan from the preceding section and removes
the high logarithmic loss. It does not reach cube-root smoothness, and no
iteration to arbitrary-root smoothness has been proved. It also does not
improve the strongest multiplicity exponent gamma<2064/4001.

The original task is still UNSOLVED. Spec.lean has not been modified and
retains its original sorry, with SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof or disproof is ready, and no verification submission
has been made. There is no pending build or auxiliary proof error.

## The improved sieve budget cannot be iterated at the same modulus level

The continuation rechecked the endpoint criterion and possible iterations of
the new wide-pool reciprocal-divergence theorem. No new sufficient arithmetic
lower bound was found. In particular, predecessor-product iteration still
requires a lower count of pairs whose product plus one is prime; the existing
finite image and divisor-collision lemmas do not supply that count.

New verified modules:

```
Submission/SieveIterationBudget.lean
Submission/SieveIterationBudgetCheck.lean
```

They compile cleanly. Nine axiom checks use only propext, Classical.choice,
and Quot.sound; exact-type examples check the numerical consequences.
Logs: `/tmp/SieveIterationBudget.log` and
`/tmp/SieveIterationBudgetCheck.log`.

Define RetentionBudget(delta,beta,kappa,j) by beta>=0, j>=0, j<=beta,
delta+beta+kappa=1, and

```
(8320/675)*kappa <= (27/32)*j^2.
```

These are the normalized sufficient conditions of the current improved
second sieve. The file proves

```
kappa <= (3645/53248)*beta^2,
delta >= 1-beta-(3645/53248)*beta^2.
```

Consequently beta<=1/3 requires

```
delta >= 105281/159744 > 0.659,
```

so it cannot occur at delta<=1/2. More sharply, delta<=1/2 forces
beta>4839/10000. Specializing to the actual Chebyshev parameter conditions
proves

```
1-b/t < 5161/10000.
```

This is a bound on thresholds produced by those precise sufficient
conditions, NOT an upper bound on actual multiplicities and NOT a disproof
of the conjecture. Unlike IndependentCompositeBarrier.lean, it applies to
the improved coefficient 27/32 rather than the older 17/32 coefficient.

A final squeeze-theorem result proves that any sequence satisfying these
budgets with beta tending to zero and delta<=1 must have delta tending to
one. Thus merely repeating the current below-half distribution estimate,
even with fixed reciprocal mass, does not give a cofinal iteration.

The original conjecture remains UNSOLVED. The best completed multiplicity
range remains gamma<2064/4001, and the new wide reciprocal-divergence theorem
remains valid at ratio 19400/40019. Spec.lean is unchanged with its original
sorry and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof or disproof was submitted. No build or auxiliary proof
repair is pending.

## Quantitative shifted-prime divisor moments from a growing modulus mass

### New modules and verification

```
Submission/LogarithmicPrimeModuli.lean
Submission/ShiftedPrimeFactorMean.lean
Submission/QuantitativeShiftedMoments.lean
Submission/QuantitativeShiftedMomentsCheck.lean
```

The three result modules compile cleanly, with fresh oleans. Fifteen
printed axiom lists contain only propext, Classical.choice, and Quot.sound.
The check file includes the exact theorem type with the scale written
literally as 2^(2^(2*m+16)), not just through an auxiliary definition.
Logs are `/tmp/LogarithmicPrimeModuli.log`,
`/tmp/ShiftedPrimeFactorMean.log`, `/tmp/QuantitativeShiftedMoments.log`,
and `/tmp/QuantitativeShiftedMomentsCheck.log`.

### Growing reciprocal mass

Put E=2^(m+5), B=2^(m+3), and N=2^(64*E^2). The modulus pool is the
pairwise disjoint union, for 1<=a<B, of

```
widePrimePool a (a+1) E.
```

These are prime moduli between 2^(64*a*E) and 2^(64*(a+1)*E).
Their total reciprocal-totient mass is at least m/4096. This follows
from the previously proved interval mass lower bound and the elementary
harmonic lower bound; it does not require the prime number theorem.

`wide_primitive_mean_bound` applies separately to each interval with
parameters a, a+1, t=E, scale E. Summing gives

```
primitivePoolMean(M,N)
  <= 4000000000000*(E+1)^11*2^((64*E-1)*E).
```

All conductors are prime here, so the generic composite progression error
has only one nontrivial conductor per modulus. The character-lifting error
and proper-prime-power error are included in a bound with constant
5000000000000 and the same power-saving factor. The pool cardinality is
at most 2^(16*E^2), so using it to bound the proper-prime-power overcount
is harmless in this construction. The combined error is eventually
at most N/16, since a fixed polynomial in E is dominated by 2^E.

With the established psi(N)>=0.9*N estimate, this proves

```
N*m/8192 <= sum_{p<=N, p prime} log(p)*omega(p-1)
```

at all sufficiently large m. The exported theorem is
`Erdos821.eventually_shiftedPrimeFactorMangoldt_lower`.

### Divisor-moment consequence

The elementary pointwise inequality

```
k^omega(n) <= tau_k(n),  n>0,
```

is proved from the prime-power factorization formula for tau_k.
The tangent-line bound exp(u)*(x-u)<=exp(x), summed with log(p) weights,
combines the first-moment lower bound with the Chebyshev upper bound
sum_{p<=N} log(p)<=2*N. Uniformly for every k>=2, it yields

```
N*exp(log(k)*m/32768) <= sum_{p<=N} log(p)*tau_k(p-1),
```

eventually in m. Since log(log N)<=4*m, this gives

```lean
Erdos821.HigherDivisors.eventually_shiftedPrimeMoment_log_power_lower :
  eventually m -> infinity, for every k>=2,
    (logMomentX m : Real) *
      (log(logMomentX m))^(log(k)/131072-1)
      <= shiftedPrimeMoment k (logMomentX m)
```

`logMomentX_eq_tower` identifies logMomentX(m) with 2^(2^(2*m+16)).
The order-two specialization has logarithmic exponent 1/262144-1.
It is stronger than the earlier result that exceeded every fixed multiple
of X/log X without supplying any rate.

### Remaining gap

This is a new unconditional arithmetic lower estimate, not merely a
conditional reduction. Nevertheless its logarithmic exponent grows like
log(k), whereas the cofinal moment criterion requires k-2, with suitable
geometric-in-k constants. For fixed k>=2 the present lower exponent is
strictly smaller, so it cannot dominate the available rough-moment upper
bound as the scale tends to infinity. No limit orders or quantifiers have
been interchanged to claim otherwise.

The strongest multiplicity range remains gamma<2064/4001. The exact
conjecture remains UNSOLVED; Spec.lean is unchanged with its original
sorry and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
There is no complete proof or disproof to submit, no background build,
and no pending auxiliary proof error.

## Higher-factorial-moment follow-up (no new sufficient lower estimate)

Rechecked whether the new uniform-in-k logarithmic-power lower bound could
be fed into the cofinal moment criterion by changing the order with the
scale. For every fixed k>=2, log(k)/131072-1 is strictly less than k-2
(already log(k)<=k-1), so the new lower expression is asymptotically smaller
than the required one. Uniformity in k does not license the fixed-order /
arbitrarily-large-scale quantifier exchange ruled out in the earlier audit.

Also examined replacing the first prime-factor moment by higher factorial
moments, or applying the first-moment argument after inserting a cofactor
divisor weight. The exact identity in CofactorMomentSwitching.lean changes
the modulus from d to d*e, with e ranging up to X/d. It does not provide a
lower estimate for these weighted correlations in the new range. Extending
small-prime support alone would not establish that missing estimate.

No applicable Mertens or higher shifted-prime lower-moment theorem was found
in the local Mathlib number-theory library. No generalized Titchmarsh
asymptotic or large-modulus lower distribution claim was assumed. No new
Lean source or sufficient arithmetic estimate was produced in this check.

Spec.lean remains unchanged with its original sorry. The exact conjecture
is UNSOLVED, no complete proof/disproof has been submitted, and there is no
pending auxiliary Lean proof repair or background build.

## Direct-fiber amplification recheck (no new theorem)

Revisited FiberProducts.lean, CoprimeRecordProducts.lean,
PrimitiveTotientCollisions.lean, and the LCM/record-fiber reductions.
Coprime multiplication increases the output from n to n^2; the resulting
squared family size preserves, rather than doubles, the multiplicity
exponent. The proved collision estimates do not remove that accounting.

For LCM amplification, the missing input is still a lower supply of pairs
with sufficiently large phi(gcd), after accounting for both the rarity of
the overlaps and collisions of the LCM map. A popular common input prime
need not be a fixed positive power of the output, and excluding any fixed
set of small input primes does not provide such a growing lower bound.
No exponent-increasing pair supply or size-controlled stripping argument
was obtained. No new arithmetic or Lean theorem resulted in this recheck.

The exact conjecture is still UNSOLVED. Spec.lean is unchanged with its
original sorry. No complete proof/disproof has been submitted and no build
or auxiliary proof repair is pending.

## Continuation: product-of-small-factors moment recheck

Rechecked the latest quantitative moment lower bound against the fixed-order
cofinal criterion and the existing product-modulus moment identities. For
fixed k>=2, the known exponent log(k)/131072-1 is strictly smaller than k-2:
this follows already from log(k)<=k-1. Thus its ratio to every positive
constant times X*(log X)^(k-2) tends to zero as X tends to infinity.
Uniformity of the known bound in k does not change this fixed-order fact.

Averaging several small-prime divisibility conditions requires progression
information at the product modulus. The existing identities do not supply
an additional lower estimate beyond the range of the available progression
bounds. No new sufficient arithmetic lower bound, exponent amplification,
or Lean result was obtained in this recheck.

The exact conjecture remains UNSOLVED. Spec.lean is unchanged and still
contains its original sorry. No complete proof or disproof is available.


## Growing-subset factorial moments: completed linear-in-order lower power

### Files and verification

Five new result modules compile cleanly with fresh oleans:

```
Submission/RoughModulusMean.lean
Submission/SubsetProductMass.lean
Submission/PrimeSubsetModuli.lean
Submission/GrowingSubsetScales.lean
Submission/GrowingSubsetMoments.lean
```

The result modules total 938 lines. `GrowingSubsetMomentsCheck.lean`
checks the exact literal-scale statement and the all-orders cofinal
statement and audits 24 declarations. Every audit lists only the allowed
axioms propext, Classical.choice, and Quot.sound. No new module imports
Spec or contains sorry, axioms, unsafe declarations, or native_decide.

Logs are /tmp/<module-name>.log, including
`/tmp/GrowingSubsetMomentsCheck.log`. All final logs are clean; the check
log contains only the permitted-axiom reports. Probe.lean is scratch API
exploration, not part of a result dependency or the intended submission.

### New generic conductor estimate

For a finite positive modulus pool D bounded by Q, suppose every nontrivial
divisor of every d in D is at least L>=2. The new theorem
`rough_conductor_majorant_le` gives

```
sum_{d in D} primitiveConductorMangoldtMajorant(d,N)/phi(d)
  <= 2*harmonic(Q)*primitivePoolMean(Icc L Q,N).
```

All nontrivial conductors are included. The key completion estimate is

```
sum_{d in D, c|d} 1/phi(d) <= (1/phi(c))*2*harmonic(Q).
```

It uses phi(c)*phi(d/c)<=phi(d), injectivity of d->d/c for multiples,
and the already proved reciprocal-totient harmonic bound. There is no
factor-count restriction in this conductor estimate.

`rough_composite_error_le` adds the lifting error bounded by

```
2*(Q+1)*harmonic(Q)*Nat.log(2,N)*log(Q).
```

### Weighted subset mass and the divisor moment

`elementaryMass P w r` is the sum of products of the weights over r-element
subsets. `elementaryMass_succ_identity` is an exact double-counting identity.
`elementaryMass_factorial_lower` proves

```
mu^r/r! <= elementaryMass P w r
```

whenever all weights lie in [0,b] and `mu+r*b <= sum_P w`. It is uniform in
r; r may grow with the pool parameter.

`primeSubsetModuli P r` consists of products of r distinct primes from P.
Their reciprocal-totient mass is exactly elementaryMass with weights 1/phi(p).
Their divisor incidence count is exactly a binomial coefficient, and

```
a^r * #{d in primeSubsetModuli P r : d|n} <= tau_(a+1)(n)
```

for n>0. `primeSubsetModuli_progression_le_moment` transfers this inequality
to a log-weighted shifted-prime divisor moment, explicitly retaining the
proper-prime-power error.

### Growing factor count with fixed divisor order

Fix k>=1, let m tend to infinity, and put

```
E = logMomentScale(m) = 2^(m+5)
B = logMomentTop(m) = E/4
r = k*m
P = logMomentModuli(m)
M = primeSubsetModuli(P,r)
L = progressionScaleN(E)
Q = subsetMomentQ(k,m) = progressionScaleN(r*B*E)
N = subsetMomentX(k,m) = progressionScaleN(64*r*E*E).
```

The divisor order is the FIXED number 32768*k+1; only the subset size r grows.
The pool P already has reciprocal-totient mass at least m/4096, and each
weight is at most 2/L. Once L>=16384*k, the factorial mass theorem gives

```
(m/8192)^r/r! <= poolTotientMass M.
```

Since r!<=r^r,

```
4^r <= (32768*k)^r * poolTotientMass M.
```

Every nontrivial conductor lies between L and Q. At the general scale
N=progressionScaleN(t*E), Q=progressionScaleN(b*E), with 32*b<=t, the new
`small_rough_pool_combined_error` bounds the combined character and
proper-prime-power remainders by

```
10^15 * ((t+1)*(E+1))^6 * 2^((64*t-1)*E).
```

For t=64*r*E and b=r*B, this is at most

```
10^15*(64*k+1)^6*(E+1)^18 * 2^((64*t-1)*E).
```

The factor `(32768*k)^r` is at most `E^(32768*k*k)`.
Thus for each FIXED k the weighted combined error is eventually at most
N/16, by polynomial domination by 2^E. This estimate is not uniform in k.

Even the earlier elementary Mangoldt lower bound psi(N)>=N/8 is enough.
For r>=4 the retained main term gives the completed theorem

```
eventually_primeLogDivisorMoment_linear_lower (k) (1<=k):
  eventually m, N*2^(k*m) <= primeLogDivisorMoment(32768*k+1,N).
```

No PNT or new distribution hypothesis was assumed.

### Final logarithmic powers and exact scale

`subsetMomentX_eq_tower` identifies the scale exactly:

```
subsetMomentX(k,m) = 2^((k*m)*2^(2*m+22)).
```

For m>=4096*k+8, log(log N)<=4*m. Consequently

```
eventually_shiftedPrimeMoment_linear_log_power (k) (1<=k):
  eventually m,
    N*(log N)^(k/8-1) <= shiftedPrimeMoment(32768*k+1,N).
```

`subsetMomentX_tendsto` proves this scale tends to infinity with k fixed.
There is a corresponding frequently-atTop theorem.

Monotonicity of tau in its order is proved directly from its divisor-sum
recurrence. With k=floor((K-1)/32768), this yields, for EVERY K>=32769,

```
eventually_shiftedPrimeMoment_all_orders_linear:
  eventually m,
    N*(log N)^((K-1)/524288-1) <= shiftedPrimeMoment(K,N)

frequently_shiftedPrimeMoment_all_orders_linear:
  frequently X atTop,
    X*(log X)^((K-1)/524288-1) <= shiftedPrimeMoment(K,X).
```

### Remaining gap and original task status

The new logarithmic exponent is linear in the fixed divisor order, not
merely logarithmic as in the preceding theorem. Nevertheless its coefficient
is small: `(K-1)/524288-1 < K-2` for every K>=2. It cannot replace the
unproved cofinal geometric moment hypothesis. Growing the subset size does
not supply the missing near-full-modulus distribution or arbitrary-root
smooth prime input.

The strongest verified multiplicity range is still gamma<2064/4001, i.e.
epsilon>1937/4001. The full conjecture is neither proved nor disproved.
Spec.lean is unchanged, contains its original sorry, and has SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
No complete proof/disproof was submitted; there is no pending source repair
or background build.


## Every subcritical logarithmic moment power: completed arithmetic result

### Files and audit

The following five new result modules, totalling 837 lines, compile cleanly
with fresh oleans:

```
Submission/PrimeMassLogBounds.lean
Submission/TruncatedPrimeMass.lean
Submission/NearMomentScales.lean
Submission/NearMomentMass.lean
Submission/NearSharpMomentPowers.lean
```

`Submission/NearSharpMomentPowersCheck.lean` verifies both the exact
frequently-atTop type and the cofinal type with the scale written literally
as `2^(128*t*L)`. Its 29 axiom checks list only propext, Classical.choice,
and Quot.sound. No new result module contains sorry/axiom/unsafe/native_decide
or imports Spec. The logs are /tmp/<module-name>.log and
`/tmp/NearSharpMomentPowersCheck.log`. The final result logs are empty; the
check log contains only the permitted-axiom reports. There is no pending
Lean repair or background build.

### Sharp leading lower coefficient for prime reciprocal mass

Define `primeTotientMass H = sum_{p<=H prime} 1/phi(p)`.
`harmonic_le_exp_primeTotientMass` follows from the previously proved finite
Euler-product bound for the harmonic sum. It gives

```
primeTotientMass_scale_power_lower:
  A*log E <= primeTotientMass(progressionScaleN(E^A)), E>=1.
```

This has leading coefficient one and does not use a PNT.
A separate Chebyshev dyadic bound gives

```
primeTotientMass_scale_upper:
  primeTotientMass(progressionScaleN E) <= 1024+8*log E, E>=1.
```

For `powerPrimePool A E`, the primes between progressionScaleN(E) and
progressionScaleN(E^A), inclusive, this yields

```
poolTotientMass(powerPrimePool A E) >= (A-8)*log E-1024.
```

The upper coefficient 8 is deliberately coarse. It can be absorbed by
choosing the fixed parameter A sufficiently large.

### Cardinality truncation of a finite Euler product

The existing exact weighted-subset first-moment identity is used with
constant observable 1. `half_euler_product_card_truncated` retains at least
half of the full Euler product among subsets of size at most R whenever
`2*sum weights <= R` and R>=1.

`card_truncated_mass_eq_sum` groups these subsets by their sizes.
`exists_large_primeSubset_mass` then selects an r<=R satisfying

```
a^r*poolTotientMass(primeSubsetModuli P r)
  >= product_{p in P}(1+a/phi(p)) / (2*(R+1)).
```

This selection is pointwise in the scale and does not change the fixed
divisor-function order a+1.

`log_one_add_small_lower` proves

```
(A/(A+1))*x <= log(1+x), if A>0, x>=0, A*x<=1.
```

Consequently `powerPrimePool_euler_lower` gives the lower bound
`E^(w*(A-10))` for the weighted Euler product when A>=10, log E>=1024,
and progressionScaleN(E)>=2*w*A. This avoids a fixed geometric loss from
using the crude r!<=r^r estimate at a single prescribed subset size.

### Parameters and error control

Fix w>=1 and A>=0 BEFORE letting m tend to infinity. The divisor order is
K=w+1. Set

```
E = logMomentScale m = 2^(m+5)
C = nearMomentC w A = 4096*w*(A+20)
R = nearMomentR w A m = C*(m+5)
P = nearMomentP A m = powerPrimePool(A+20,E)
b = nearMomentB w A m = R*E^(A+19)
t = nearMomentT w A m = 64*R*E^(A+20)
Q = nearMomentQ w A m = progressionScaleN(b*E)
N = nearMomentX w A m = progressionScaleN(t*E).
```

For every r<=R the r-subset modulus pool is bounded by Q and all its
nontrivial conductors are at least progressionScaleN(E). The condition
32*b<=t holds. The new generic rough-pool estimate therefore applies
uniformly to every possible selected r. After simplifying the parameters,
the combined character and prime-power error is at most

```
10^15*(64*C+1)^6*(E+1)^(6*(A+22))*2^((64*t-1)*E).
```

Also `w^r <= E^(w*C)`. Hence, for fixed w and A, every weighted combined
error is eventually at most N/16 by polynomial domination by 2^E.
No progression information at a large relative modulus level is used.
In fact log Q/log N = 1/(64*E).

The mean bound ensures the cutoff R retains half of the Euler product.
Moreover R+1<=E eventually. Choosing a subset size r by the mass lemma gives

```
w^r*poolTotientMass(nearMomentPool A m r) >= E^(w*(A+9))/2.
```

The elementary psi(N)>=N/8 bound and the weighted error bound imply the
completed unconditional theorem

```
eventually_nearMoment_primeLog_lower:
  eventually m,
    N*E^(w*(A+8)) <= primeLogDivisorMoment(w+1,N).
```

### Subcritical logarithmic powers

The logarithm of N is eventually at most E^(A+23). Thus

```
nearMomentExponent(w,A) = w*(A+8)/(A+23)-1
                       = w-1-15*w/(A+23)
```

and

```
eventually_nearMoment_log_power:
  eventually m,
    N*(log N)^(nearMomentExponent w A) <= shiftedPrimeMoment(w+1,N).
```

`nearMomentX_tendsto` proves N tends to infinity at each fixed w,A.
Since the displayed exponent tends to w-1 as A tends to infinity,

```
frequently_shiftedPrimeMoment_subcritical_power (K) (2<=K) (alpha) (alpha<K-2):
  frequently X atTop,
    X*(log X)^alpha <= shiftedPrimeMoment(K,X).

frequently_shiftedPrimeMoment_almost_critical (K) (2<=K) (delta) (delta>0):
  frequently X atTop,
    X*(log X)^(K-2-delta) <= shiftedPrimeMoment(K,X).
```

All these declarations are in namespace Erdos821; shiftedPrimeMoment and
tau remain in Erdos821.HigherDivisors.

### Exact prescribed dyadic scales

The final theorems do not merely give unrelated sparse cutoffs.
`cofinal_nearMoment_dyadic_power` fixes the scale parameter t and chooses
m with t dividing m+5, using

```
j = max B M+5, m=t*j-5,
L = 131072*w*(A+20)*j*E^(A+21).
```

Then `nearMomentX(w,A,m)=2^(128*t*L)` and L>=B. In particular,

```
cofinal_shiftedPrimeMoment_subcritical (K t) (2<=K) (2<=t)
    (alpha) (alpha<K-2):
  for every B, there exists L>=B with
    X*(log X)^alpha <= shiftedPrimeMoment(K,X),
  where X=momentScaleX(t,L)=2^(128*t*L).
```

The exact-scale check states alpha=K-2-delta for arbitrary delta>0.

### Precise remaining gap

The original cofinal criterion requires the CRITICAL logarithmic power
K-2, with a suitable positive coefficient theta^K/K!. The new theorems
supply every STRICTLY SMALLER power, but do not give any positive critical
coefficient. Even knowing all strict powers is compatible with a normalized
critical moment tending to zero. Neither the auxiliary parameter A nor the
positive loss delta was chosen after the witness scale.

No proof or disproof of the original conjecture has been obtained, and
Spec.lean was not modified. Its SHA-256 remains
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The strongest verified multiplicity range remains gamma<2064/4001
(epsilon>1937/4001). No complete proof/disproof was submitted.


## Growing auxiliary parameter: critical power with polynomial log-log loss

### Completed files and audit

Three new result modules, totalling 570 lines, compile cleanly with fresh
oleans:

```
Submission/FiniteNearMoment.lean
Submission/LogLogMomentScales.lean
Submission/LogLogMomentLower.lean
```

`Submission/LogLogMomentLowerCheck.lean` checks the exact frequently-atTop
statement and the cofinal statement with the scale written literally as
`2^(128*t*L)`. Its 25 axiom reports contain only propext, Classical.choice,
and Quot.sound (some declarations use fewer). No new result module contains
sorry, axiom declarations, unsafe, native_decide, or an import of Spec.

Logs: /tmp/FiniteNearMoment.log, /tmp/LogLogMomentScales.log,
/tmp/LogLogMomentLower.log, and /tmp/LogLogMomentLowerCheck.log.
The final result logs are empty; the check log has only permitted-axiom
reports. There is no pending source repair or background build.

### Finite conditions, not a quantifier exchange

The previous near-critical moment theorems fixed w and A before taking
m to infinity. They could not simply be applied with a growing A.
`FiniteNearMoment.lean` extracts finite sufficient conditions from their
proofs. In particular, define the natural-number budget

```
nearMomentBudget(w,A,n) =
  16*10^15*(64*nearMomentC(w,A)+1)^6 *
  (logMomentScale(n)+1)^(w*nearMomentC(w,A)+6*(A+22)).
```

The finite lemmas give the weighted error bound and prime-log moment lower
bound if this budget is at most `2^(logMomentScale(n))`, the cutoff R+1 is
at most logMomentScale(n), the lower-conductor condition holds, and n>=2048.
These are pointwise statements and genuinely allow A to vary with n.

### Explicit joint choice and uniform budget

Keep the divisor order K=w+1 FIXED, with w>=1. Put

```
a = loglogMomentA(m) = 2^m
n = loglogMomentIndex(m) = 2*m+5
E = loglogMomentE(m) = logMomentScale(n) = 2^(2*m+10)
N = loglogMomentX(w,m) = nearMomentX(w,a,n)
D(w) = loglogBudgetConstant(w) = 2^24*(w+1)^2.
```

The new purely finite natural-number inequalities include

```
nearMomentC(w,a) <= 2^17*(w+1)*a
64*nearMomentC(w,a)+1 <= 2^(m+w+25)
w*nearMomentC(w,a)+6*(a+22) <= 2^18*(w+1)^2*a
nearMomentBudget(w,a,n) <= 2^(D(w)*(m+1)*a)
nearMomentR(w,a,n)+1 <= D(w)*(m+1)*a.
```

For each fixed w, eventually `D(w)*(m+1)<=2^m=a`, so the right-hand
exponent is at most a^2<=E. Hence both the error budget and the cardinality
cutoff conditions hold along this joint growing-parameter sequence.
The lower-conductor condition follows from the R bound. No fixed-parameter
eventual theorem was used as if uniform in A or w.

This establishes

```
eventually_loglog_primeLog_lower (w) (1<=w):
  eventually m,
    N*E^(w*(a+8)) <= primeLogDivisorMoment(w+1,N).
```

### Converting the loss to a power of log log

The previous finite log estimate gives `log N <= E^(a+23)` once the
cutoff and E>=4096 conditions hold. The new lower estimate gives, for m>=32,

```
32*a <= log(log N).
```

Since `E=(32*a)^2` exactly, it follows that `E <= (log(log N))^2`.
Therefore

```
(log N)^w <= E^(w*(a+8)) * E^(15*w)
          <= E^(w*(a+8)) * (log(log N))^(30*w).
```

Combining this with the prime-log moment estimate and dividing by log N
proves the result

```
eventually_loglog_shiftedPrimeMoment_lower (w) (1<=w):
  eventually m,
    N*(log N)^(w-1)/(log(log N))^(30*w)
      <= shiftedPrimeMoment(w+1,N).
```

The logarithms used in the denominators are proved positive at these
scales. The powers in this statement are natural-number powers.
`loglogMomentX_tendsto` proves the new scale tends to infinity with w fixed,
without assuming the auxiliary parameter is fixed.

### Final cofinal results

For every K>=2:

```
frequently_shiftedPrimeMoment_loglog_loss:
  frequently X atTop,
    X*(log X)^(K-2)/(log(log X))^(30*(K-1))
      <= shiftedPrimeMoment(K,X).
```

For every fixed t>=2 as well:

```
cofinal_shiftedPrimeMoment_loglog_loss:
  for every B there exists L>=B with the same inequality at
    X=momentScaleX(t,L)=2^(128*t*L).
```

The prescribed-scale proof chooses j=max(B,M)+5 and m=t*j-5, so
loglogMomentIndex(m)+5=2*t*j. It then takes

```
L = 262144*w*(a+20)*j*E^(a+21),
```

giving the exact identity `loglogMomentX(w,m)=2^(128*t*L)`.
All new declarations are in namespace Erdos821.

### Remaining gap

This retains the critical logarithmic POWER but still has a coefficient
`(log(log X))^(-30*(K-1))` tending to zero at every fixed K>=2. The sufficient
criterion needs a suitable POSITIVE coefficient `theta^K/K!` at that power.
The new result does not establish that input. Nor is the eventual estimate
uniform in K: the explicit condition D(w)*(m+1)<=2^m depends on w.

The full conjecture remains UNSOLVED and Spec.lean is unchanged, retaining
its original sorry and SHA-256
`8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7`.
The strongest verified multiplicity range is still gamma<2064/4001, or
epsilon>1937/4001. No complete proof or disproof was submitted.

### Lean debugging note

When large scale expressions occur inside local lets, `dsimp [Z]; positivity`
can trigger enormous reduction at whnf. An explicit
`show 0<=Z from pow_nonneg hE0 _` avoided a 5-million-heartbeat timeout.
For powers with large literal factors in their exponents, use
`congrArg (fun e : Nat => 2^e)` rather than `congr 1`. Also specify the
exponent in `pow_succ _ n` or `pow_add _ n k`: unrestricted rewriting may
expand the wrong earlier power because Nat additions are definitionally
successors.


## Finite moving-order coefficient comparison (no settlement)

### Completed files and audit

- `Submission/NearMomentCoefficientGap.lean` (135 lines).
- `Submission/NearMomentCoefficientGapCheck.lean`.

The result module has a fresh olean and a clean build. The check module
verifies the exact two coefficient statements and audits all six declarations;
only propext, Classical.choice, and Quot.sound occur. Logs are
`/tmp/NearMomentCoefficientGap.log` and
`/tmp/NearMomentCoefficientGapCheck.log`.

### Uniform comparisons

Write E=logMomentScale(m), B=log(nearMomentX(w,A,m)), K=w+1.
For w>=1 and nearMomentR(w,A,m)+1<=E, the raw lower certificate satisfies

```
E^(w*(A+8))/B^w < (1/2)^(w+1)/(w+1)!.
```

This is `nearMoment_raw_coefficient_gap`. It uses the finite consequences
K<=E and B>=E^(A+20), not any fixed-order eventual statement. In particular
it applies pointwise if the order and auxiliary parameter both vary.

For the log-log scales, put H=log(log(loglogMomentX(w,m))). If m>=32 and
the finite R condition holds, then

```
1/H^(30*w) < (1/2)^(w+1)/(w+1)!.
```

This is `loglogMoment_coefficient_gap`. Here K<=E<=H^2 and H>=2. The
generic factorial comparison is

```
2^(w+1)*(w+1)! < H^(8*w), if w>=1, H>=2, and w+1<=H^2.
```

It follows from K!<=K^K<=H^(2K) and 3K<=6w<8w.

### Scope

Both inequalities concern the explicit values certified as lower bounds.
They DO NOT upper-bound shiftedPrimeMoment, do not contradict the desired
critical lower bound, and do not disprove the original conjecture. They do
show that the proposed moving-order use of these particular certificates
cannot reach the sufficient coefficient for theta>=1/2. The existing
rough-moment transfer needs theta greater than 1-1/(2*t), which is at least
3/4 when t>=2.

No new sufficient arithmetic input or improved multiplicity exponent was
proved. The original statement remains unresolved and Spec.lean retains
its original sorry. Its SHA-256 remains
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.

## Further arithmetic-input review after the coefficient-gap audit

Rechecked the endpoint smooth-series equivalence, cofactor moment switching,
symmetric divisor hyperbola, one-sided smooth-modulus criterion, and the
LCM-pair criterion against the available unconditional inputs. No new
sufficient estimate was established in this continuation.

The cofactor expansion has product moduli d*e reaching the full scale X.
The symmetric hyperbola leaves a genuine all-small-factor remainder, or
weights on both sides in its balanced form. Neither identity supplies a
lower bound for the missing prime-weighted correlations. Fixed-modulus
Dirichlet-series poles still lack a uniform growing-modulus rate. The
LCM route still needs a lower supply of large-overlap pairs; its existing
moment bounds are upper bounds and cannot supply that hypothesis.

No new Lean result is claimed for this review. All previously completed
modules are unchanged. Spec.lean is still unchanged with its original sorry;
there is no complete proof/disproof, no submission, and no pending build or
source repair. The conjecture remains unresolved in this development.


## Flexible Chebyshev weights: exponent 2070643/4000001

### Completed modules and verification

- `Submission/FlexibleChebyshevWeight.lean` (183 lines)
- `Submission/FlexibleChebyshevGain.lean` (158 lines)
- `Submission/FlexibleChebyshevSpecialization.lean` (60 lines)
- `Submission/FlexibleChebyshevCheck.lean` (exact-type checks and audit)

All result builds and the check build exit zero. The three result logs
are empty; the check log contains twenty permitted-axiom reports only.
Logs are `/tmp/FlexibleChebyshevWeight.log`,
`/tmp/FlexibleChebyshevGain.log`,
`/tmp/FlexibleChebyshevSpecialization.log`, and
`/tmp/FlexibleChebyshevCheck.log`. Fresh result oleans were generated.
Only propext, Classical.choice, and Quot.sound occur in audited dependencies.

### Full lower constant and arbitrary fixed margins

Let

```
c0 = chebyshevRatioConstant
   = (14*log 2+9*log 3+5*log 5)/30.
```

For every fixed 0<=c<c0, `eventually_mangoldt_lower_constant` proves
psi(N)>=c*N eventually at every natural cutoff. It reuses the proved
Stirling limit of the factorial ratio, but no longer rounds to 9/10.
The progression-scale and primeProductModuli-weighted versions retain any
such c, with all integer parameters fixed before the scale tends to infinity.

`eventually_independent_total_error_divisor` replaces the fixed relative
error 1/64 by 1/D for any fixed positive natural D. The underlying
power-saving estimate is unchanged. `flexible_independent_count_of_weight`
converts retained N*mass/D into a polynomially weakened smooth-prime count,
using explicit natural constant

```
flexibleStructuredCountConstant(r,t,D)
  = 64*D*primeProductMassConstant(r)*t*choose(t-1,r).
```

### Limiting sieve coefficient

The finite upper bound is

```
log(N)*independentSieveMain(t,b,h,m)
  <= [A + B/m]*N,
A = (8192/675)*t*h/(b-1)^2,
B = (128/675)*t/((b-1)^2*log 2).
```

It follows from H_K<=1+log K, removing the previous 65 in place of 64.
Thus every fixed a>A is an eventual main-term upper coefficient.

If A<c0, choose a FIXED positive natural D with A+3/D<c0. At large
scales the total progression weight is at least (A+3/D)*N*mass, the
rejected main term at most (A+1/D)*N*mass, and the combined error at most
N*mass/D. At least N*mass/D remains. No growing parameter or exchange of
quantifiers is used.

### New generic sufficient conditions

`infinite_g_gt_flexible_chebyshev_parameters` proves the fixed-exponent
conclusion for gamma<1-b/t under

```
r+b+h=t,
2*r+1<=t,
2<=b,
1<=h,
t+5<=5*b,
(8192/675)*t*h < c0*(b-1)^2.
```

The last inequality is STRICT; D depends on its positive margin.
These replace the older sufficient condition with 8320/675 and 27/32.
Consequently the earlier formal bound below 0.5161 for THAT older
condition is not a bound on these new parameter choices.

### Explicit specialization

`chebyshevRatioConstant_gt_decimal` proves c0>92129/100000 using
Mathlib's logarithm-series lower bounds (three terms at x=1/11 and x=1/9)
and its certified lower bound for log 2. It does not rely on floating-point
numerics.

The exact rational parameter check uses

```
r=2000000, t=4000001, b=1929358, h=70643.
```

The resulting main coefficient is less than 92129/100000. The new theorem
`infinite_g_gt_flexible_chebyshev_uniform` gives every

```
gamma < 2070643/4000001 ~= 0.5176606205848449.
```

Also proved:
- `infinite_g_gt_point_five_one_seven_six_six`: every gamma<0.51766;
- `erdos_821_flexible_chebyshev_range`: epsilon>1929358/4000001;
- `erdos_821_point_four_eight_two_three_four`: epsilon>0.48234;
- `flexible_chebyshev_strict_improvement`: exact comparison with 2064/4001.

### Scope and original task status

This is a genuine improvement of the unconditional multiplicity exponent,
not merely a coefficient comparison. It is still bounded away from one.
No arbitrary-root smooth-series divergence or sufficient all-order critical
moment bound has been established. The exact original conjecture remains
UNSOLVED. Spec.lean is unchanged and retains its original sorry and SHA-256
8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
No complete proof/disproof has been submitted. There is no unfinished source
proof or pending build.


## The flexible budget does not provide an exponent-increasing iteration

Completed `Submission/FlexibleSieveBudget.lean` (114 lines) and
`Submission/FlexibleSieveBudgetCheck.lean`. Both compile cleanly; the
result olean is fresh. Nine declarations have an audit containing only
propext, Classical.choice, and Quot.sound. Logs:
`/tmp/FlexibleSieveBudget.log` and `/tmp/FlexibleSieveBudgetCheck.log`.

The certified upper logarithm-series bounds show

```
chebyshevRatioConstant < 9213/10000.
```

The normalized NEW budget is

```
0<=beta, 0<=j<=beta, delta+beta+kappa=1,
(8192/675)*kappa <= chebyshevRatioConstant*j^2.
```

It implies

```
kappa <= (248751/3276800)*beta^2,
delta >= 1-beta-(248751/3276800)*beta^2.
```

Consequences proved:
- If beta<=1/3, then delta>=6470683/9830400 (greater than 0.658).
- If delta<=1/2, then beta>48233/100000.
- Hence every exponent threshold 1-b/t supplied by the actual flexible
  integer parameter conditions is STRICTLY below 51767/100000.
- For a sequence of such normalized budgets with delta<=1 and beta->0,
  one must have delta->1.

This closes the proposed iteration using the same below-half distribution
and retention conditions. It does NOT upper-bound actual g(n), does not
rule out other methods or stronger arithmetic inputs, and does not disprove
Erdos 821. The attained exponent remains 2070643/4000001. The original task
is still UNSOLVED: Spec.lean is unchanged and retains its original sorry
and SHA-256 8624f9ce0d5638ea7f02b6b091ff76d499a46bafb925630a4a63823dad6fe2e7.
There is no complete proof/disproof, no submission, and no pending source
repair or build.

## Padding and output-capacity follow-up after the flexible-budget check

Rechecked ClosedSmoothFibers, ClosedSupportPadding, and
DensePredecessorSupport. The closed small-radical output theorem is genuine,
but its multiplicity exponent comes from an already supplied smooth-prime
family and is preserved rather than increased. The full-pool radical bound
is relative to the full predecessor product; it is not automatically a bound
at a sparse selected output's scale.

Considered reducing output prime-power capacities to gain subset entropy.
No uniform lower count surviving that reduction was obtained. A fixed-root
radical bound alone does not justify a reduction parameter growing as a power
of the input-prime cutoff. No new compression or exponent-amplification
lemma is claimed.

No Lean source was changed in this continuation. The strongest verified
exponent remains 2070643/4000001. Spec.lean still has its original sorry;
there is no complete proof/disproof, no submission, and no pending build.
