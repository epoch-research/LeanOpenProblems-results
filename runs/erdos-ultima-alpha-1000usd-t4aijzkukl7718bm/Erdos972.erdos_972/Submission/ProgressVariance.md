# Checkpoint: variance route tested against the actual remainder

The conjecture is STILL UNSOLVED. `Spec.lean` is unchanged with its original
`sorry`. No irrational counterexample or sufficient centered four-factor
lower bound has been proved. Do not submit an incomplete proof.

The previous complete reduction is in `ProgressFourFactor.md`. All three
Type-I covariance errors are already controlled at common scales. The only
missing mathematical step there is a strict lower gap for the centered
four-factor remainder. This phase tested a specific potential route to that
gap rather than adding another Type-I reduction.

## New compiled, axiom-audited files

### RemainderSemiprimes.lean
Namespace `Erdos972RemainderSemiprimes`.

- `small_divisor_semiprime`: if p,q are primes larger than U, any divisor
  d of pq with d≤U is 1.
- `cutoff_mangoldt_semiprime_divisor`: Λ_≤V vanishes at every divisor of pq
  if p,q>V.
- `typeIPart_rough_semiprime`: for p,q>U,V and U>0,
  `typeIPart U V (p*q) = log(p*q)`.
- `typeIIPart_rough_semiprime`: if p≠q as well,
  `typeIIPart U V (p*q) = -log(p*q)`.
  This is a general identity for the actual remainder, not a numerical test.
- `covariance_self_two_clusters`: if f=0 on P and f≤-L on S, both subsets
  of Ioc 0 N with at least m elements, then
  `m*L²/4≤Cov_N(f,f)`. The proof works for any actual mean; it splits
  according as that mean is ≤-L/2 or >-L/2.

### PrimeIntervalCounts.lean
Namespace `Erdos972PrimeIntervalCounts`.

- `primesBetween a b = {p∈Ioc a b : p.Prime}`.
- `mem_primesBetween`, `theta_interval_sum`, `theta_interval_le_card_log`.
- `eventually_prime_interval_counts`: for every sufficiently large natural x,
  x>1 and
  ```
  x/(2 log x) ≤ #primesBetween 0 x,
  x/(2 log(2x)) ≤ #primesBetween x (2x).
  ```
  These follow from the previously verified qualitative Chebyshev PNT.

### RemainderVariance.lean
Namespace `Erdos972RemainderVariance`.

- `semiprime_rectangle_injective`: when 2W<Q, multiplication is injective
  on primesBetween W (2W) × primesBetween Q (2Q).
- `remainder_variance_lower`: under W,N>0,
  2W<Q, 4WQ≤N≤8WQ, log(2W)≥1, log N≥2log 8, and the preceding prime
  count bounds at W,Q,N,

  ```
  N*log N/(512*log(2W))
    ≤ Cov_N(typeIIPart W W, typeIIPart W W).
  ```

  The two clusters are primes (where R=0) and a rectangular family of rough
  semiprimes pq (where R=-log(pq)≤-(log N)/2). There are at least
  `N/(32 log(2W) log N)` semiprimes in the latter family. The argument never
  assumes anything about primality of floor αn.

### RemainderVarianceScales.lean
Namespace `Erdos972RemainderVarianceScales`.

- `growingCutoff_power`: W^128≤u for W=growingCutoff u.
- `growingCutoff_main_power`: W^640≤N for N=scaleCutoff α u, α≥1,
  u>0 and 2α≤u. This follows from u^6≤2αN and 2α≤u.
- `cofactorCutoff α u = N/(4W)`.
- `cofactor_ge_square`: W≥4 and W^640≤N imply W²≤N/(4W).
- `cofactorCutoff_tendsto`: cofactorCutoff α u→∞ for α≥1.
- `logarithmic_separation`: W≥512 and W^640≤N imply
  `576 log(2W)≤log N`.

**Main actual-remainder bounds:**

- `eventually_remainder_variance_lower`: for any fixed α≥1, eventually in u,

  ```
  (9/8)*N ≤ Cov_N(R_WW,R_WW),
  N=scaleCutoff α u, W=growingCutoff u.
  ```

- `eventually_remainder_variance_gt_main`: that variance is eventually >N.
- `not_tendsto_remainder_variance_zero`: its quotient by N does NOT tend to 0.

These theorems require no irrationality and hold at all sufficiently large
numeric scales, so in particular they apply at the good irrational scales.
They depend only on propext, Classical.choice, Quot.sound.

## What this does and does not establish

It rules out a proof route that tries to show that the actual remainder has
o(N) variance and then applies Cauchy–Schwarz to get the required cross-
covariance bound. Such a variance estimate is FALSE, as now formally proved.

It does NOT rule out a more refined cross-correlation argument, negative-part
estimate, or a different decomposition. In particular, a large input variance
alone does not logically refute every possible use of Cauchy–Schwarz. The
missing cross-covariance lower gap remains untouched.

## Further mathematical considerations (not formal claims)

- A generic arbitrary-coefficient four-factor decorrelation estimate is not
  available: multiplicative phases n^(it) can align on kl≈αmn, even for
  large t. Any applicable inverse/spectral argument must control the actual
  Möbius and Mangoldt coefficients, not merely their absolute values.
- Nonnegative Selberg-majorant residuals offer another possible route, but
  mean-2 majorants sit at the parity boundary. Simultaneous rough-composite
  mass sufficient to create a strict gap has not been established.
- Merely producing prime ratios, a.e./comeagre success, or many semiprimes in
  one coordinate does not give prime pairs at a prescribed irrational α.
- No external theorem settling the full statement has been independently
  identified. Do not claim a known result applies without verifying it.

Audit: `Submission/AuditVariance.lean`.
Scratch `CheckVariance.lean` contains only check commands.
