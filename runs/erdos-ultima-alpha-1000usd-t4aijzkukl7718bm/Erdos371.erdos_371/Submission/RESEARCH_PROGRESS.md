# Continuation checkpoint: reflection boundary and rational smoothing

The target `Spec.lean` is still unchanged and contains its original `sorry`.
No proof or disproof of Erdős 371 has been obtained. Do not submit as solved.

## New verified files in this continuation

All have saved `.olean` files. Main theorems use exactly propext,
Classical.choice, and Quot.sound; no admissions are present in these files.

- `SeparatedReflectionObstruction.lean` (imports PrimeReflection):
  `primeReflection_twice_eq_iff`: R(R(n))=n iff n<pairPrimeProduct n and
  reflection preserves that product.
  `separated_primeReflection_not_involutive C`: exists n>1 with
  C*P(n)<P(n+1) and R(R(n)) != n.
  Construction n=(2^((2*C)!))^3. Fermat gives all prime divisors of n+1>2C;
  the factorization x^3+1=(x+1)(x²-x+1) gives P(n+1)<=x² and product<=n.
  This is pointwise, NOT a positive-density non-involutivity claim.

- `SmoothedComparison.lean` (imports RatioNearTieDensity):
  `bounded_multiplicative_perturbation_density_iff` for multipliers a(n),b(n)
  in [1,C].
  `rationalFactorSign n = (P(n+1)-P(n))/(P(n+1)+P(n))` (real arithmetic).
  `rationalFactorSign_error_eq`: error from factorSign equals
  2*min(P(n),P(n+1))/(P(n)+P(n+1)).
  `rationalFactorSign_mean_error_tendsto_zero`: mean absolute error tends 0.
  `density_iff_rationalFactorSign_average`: original target iff mean of
  rationalFactorSign tends 0. This SIGNED LIMIT REMAINS UNPROVED.

- `PrimeDivisorMoments.lean` (imports SieveFactorMean):
  `prime_divisor_sum_sq_mean_le`: for nonnegative weights on finite primes,
  sum_{n<N}(sum_{p|n+1}w(p))² <= N*((sum w(p)/p)²+sum w(p)²/p).
  `squarefreeSmallPrimeLog B n = sum_{p<B,p|n} log p`.
  `squarefreeSmallPrimeLog_second_moment`: <=20*N*(log B)².

- `QuadraticSmoothBound.lean` (imports PrimeDivisorMoments, RoughPartGoodPairs):
  `smooth_count_quadratic_bound R B N`: smooth count up to N <=
  smallRoughPartCount R N + largePrimeSquareCount R N +
  80*N*(log(B+1)/logN)².
  `smooth_power_count_eventually_le u hu epsilon hepsilon`: for u>=0,
  proportion of P(n+1)<=N^u for n<N eventually <=80*u²+epsilon.
  Uses R=subpowerCutoff, whose bad rough part and large-square counts vanish.

- `WeightedPrimeHarmonic.lean` (imports QuadraticSmoothBound):
  `primeLogHarmonic N = sum_{p<=N} logp/p`.
  `primePowerErrorConstant = 4*sum' n, (n:Real)^(-3/2)`.
  For N>0:
  `primeLogHarmonic_upper`: H(N)<=logN+log4.
  `primeLogHarmonic_lower`: logN-1-primePowerErrorConstant<=H(N).
  Elementary proof from factorial factorization and Mathlib Chebyshev theta
  bound; no PNT. The prime-power correction is bounded by 4*p^(-3/2).

- `LargePrimeDensityLower.lean` (imports WeightedPrimeHarmonic):
  `largePrimeSet B N`: primes B<p<=N.
  `largePrimeDivisorSet B N`: n<N with some such p dividing n+1.
  If B²>=N these events are disjoint and count is sum floor(N/p).
  `largePrimeDivisorSet_ratio_lower`:
  count/N >=1-logB/logN-(1+errorConstant+log4)/logN-log4/logB.
  `largePrime_power_count_eventually_ge v hv hv1 epsilon hepsilon`:
  for 1/2<v<1, proportion of P(n+1)>N^v eventually >=1-v-epsilon.
  Uses B=ceil(N^v), not a prime number theorem.

- `PrimeReflectionBoundary.lean` (imports LargePrimeDensityLower, PrimeReflection):
  `filter_count_le_shifted_add_one`: generic finite shift count bound.
  `primeReflection_ge_of_product_ge`: n<N and 2N<=P(n)P(n+1) imply R(n)>=N.
  `reflection_boundary_cover_eventually`: if P(n+1)>N^(1999/2000), then
  either R(n)>=N or P(n)<=N^(1/1000), eventually uniformly n<N.
  `primeReflection_boundary_positive_proportion`:
  eventually #{n<N:R(n)>=N}/N >=1/10000.
  `primeReflection_boundary_not_negligible`: that ratio does NOT tend to 0.
  This blocks pairing almost all n WITHIN THE SAME INTERVAL. It is NOT a
  disproof of the density conjecture, nor does it control signed boundary mass.

## Strategy status

Fixed-ratio near-tie rarity does not fix the reflection map. There are both
arbitrarily separated pointwise non-involutive examples and a positive
proportion of endpoint-crossing inputs. The rational smoothing theorem is a
new equivalent bounded-kernel target, not cancellation.

The strongest previous signed modular-inverse kernel reduction remains in
BalancedKernel.lean, with its triangle-inequality obstruction in
AbsoluteKernelObstruction.lean. No new signed cancellation has been proved.
The next meaningful task is arithmetic signed cancellation; further orbit or
boundary SIZE estimates alone cannot settle the target.

`Check.lean` has been removed. The recent files have a few harmless <;> linter
warnings. `RatioNearTieDensity.olean` was rebuilt and saved this continuation.

# Further checkpoint: full-log Selberg sieve and positive comparison proportions

The target is STILL UNRESOLVED; Spec.lean remains unchanged. No submission.

The latest continuation reviewed whether weighted prime-harmonic information
could enforce joint symmetry. No such deduction was found. Instead it proved
a weaker arithmetic orientation result: BOTH rises and falls have positive
lower natural proportions.

## Latest verified files (saved .olean files)

All main theorems use only propext, Classical.choice, Quot.sound. No admissions.

1. `CrtProductAverages.lean` imports CoprimeResidueSieve.
   - `sum_prod_residues_eq_prod_sum`: CRT factors sums of products of arbitrary
     real residue functions, using a bijection to a finite pi space.
   - `periodic_zero_sum_bound`: period Q, zero mean, |f|<=C gives sum bound Q*C.
   - `periodic_mean_error_bound`: |sum_{n<N}f - (N/Q)sum_{n<Q}f|<=2*Q*C.

2. `SelbergBasis.lean` imports CrtProductAverages.
   - `residueBasisAt q R r = if r in R then 1-q/card R else 1`.
     Mean zero, sum of squares q*(q-cardR)/cardR, abs bounded by q.
   - `sieveBasis s R T n` is the product of these functions over T.
   - `sieveBasisNorm s R T = product (s_i-cardR_i)/cardR_i`.
   - `sieveBasis_covariance_period`: over period product_{T union U}s_i,
     covariance equals that period times [T=U]*sieveBasisNorm(T).
   - `sieveBasis_covariance_error`: if both divisor products <=Z, covariance
     count discrepancy from N*[T=U]*norm(T) is <=2*Z^4.

3. `QuadraticResidueSieve.lean` imports SelbergBasis.
   - `selbergWeight s R T = product cardR_i/(s_i-cardR_i)`.
   - `selbergMass s R D = sum_{T in D} selbergWeight(T)`.
   - `quadratic_residue_sieve`: for a finite family D of subsets of S,
     including empty and with divisor products<=Z,
       avoidanceCount <= N/selbergMass + 2*Z^4.
   - Assumes 0<cardR_i<s_i and pairwise coprime moduli.
   - Proof uses F(n)=sum_D weight(T)*basis_T(n), which equals G on avoided
     residues; its square has diagonal main term N*G by CRT orthogonality.
     No Möbius inversion for optimal Selberg weights was needed.

4. `TruncatedEulerMass.lean` imports QuadraticResidueSieve.
   - `weightedSubsetMoment_eq`: weighted cost of random subsets equals
     product(1+h_i)*sum c_i*h_i/(1+h_i).
   - `truncated_subset_mass_lower`: if mean cost<=L/2, truncating subsets to
     total cost<=L retains at least half the full Euler-product mass.

5. `ProductCutoffSelberg.lean` imports TruncatedEulerMass.
   - `productSieveFamily S s Z`: subsets with product moduli<=Z.
   - `selbergMass_reciprocal_le_exp`: if
       sum log(s_i)*cardR_i/s_i <=log Z/2,
     then 1/G <=2*exp(-sum cardR_i/s_i).
   - `residue_selberg_upper_bound`: avoidance <=2*N*exp(-local mass)+2*Z^4.

6. `TwoLinearSelberg.lean` imports ProductCutoffSelberg, ComparableSlopeMean.
   - Uses primes 2<p<=z coprime to slopes, and Z=(z+1)^16.
     The old elementary bound sum logp/p<=4log(z+1) suffices for the cost.
   - `twoLinear_prime_count_selberg_bound`: determinant +/-1, positive slopes,
       #{t<N: at+b,ct+d prime and both>z}
       <=2*exp2*slopeSieveFactor(2*a*c)*N/log²(z+1)+2*(z+1)^64.
   - This retains the full squared-logarithmic denominator at a fixed-power
     sieve cutoff. It improves the earlier degree-truncated Brun bound.

7. `SelbergCofactorPairs.lean` imports TwoLinearSelberg, LargePrimeNearTies.
   - `cofactorPrimePairSet_selberg_bound_of_product_le`: for ab<=N,
       card <=[4*exp3*N/log²(z+1)]*sigma(ab)/(ab)+2*(z+1)^64.
   - `unrestrictedSlopeSum_bound`: sum_{a,b<=X}sigma(ab)/(ab)
       <=exp16*(1+logX)^2.
     Uses 2xy<=x²+y² and the existing weighted second moment of sigma.
   - `allCofactorPrimeSet` union over all 1<=a,b<=X (no comparability condition).
   - `allCofactorPrimeSet_bound`, if X²<=N:
       card <=4*exp19*N*(1+logX)^2/log²(z+1)+2*X²*(z+1)^64.

8. `BothLargePrimeBound.lean` imports SelbergCofactorPairs.
   - `bothLargePrimeSet N u`: n<N with P(n),P(n+1)>N^(1-u).
   - `largePairConstant =4*exp19*256²`.
   - `bothLargePrimeSet_ratio_bound`, N>1 and 0<=u<=1/8:
       card/N <=largePairConstant*(u+1/logN)^2+2^65*N^(-1/2).
     Chooses X=floor N^u and z=floor N^(1/256).
   - `bothLargePrimeSet_eventually_ratio_le`:
       eventually card/N <=largePairConstant*u²+epsilon.

9. `PositiveComparison.lean` imports BothLargePrimeBound, LargePrimeDensityLower.
   - `rising_falling_positive_lower_proportions`:
       exists delta>0, eventually
         delta<=risingCount(N)/N and delta<=fallingCount(N)/N.
   - Takes u=1/[8*(largePairConstant+1)] and delta=u/4.
   - Single-large-factor count >=u-epsilon; both-large count <=K*u²+epsilon.
     Exact finite shift counts differ by at most 1, so both orientations follow.
   - `rising_comparison_not_density_zero` and
     `falling_comparison_not_density_zero`.
   - These are NOT disproofs of the original conjecture. They only exclude
     density zero (and, by complementation, density one). They do not prove
     that densities exist or equal one half.

## Technical lessons from this batch

- The finite product basis gives a compact Selberg proof with polynomial
  error, avoiding a large optimal-weight Möbius-inversion development.
- Some generic `Finset.prod_attach` / `Finset.mem_sdiff` rewrites required
  explicit namespace/arguments despite `open Finset`.
- Finset filter decidability differences sometimes require equality by
  `ext n; simp only [mem_filter]`; `filter_congr` itself can fail instance
  synthesis when the old predicate used Classical.propDecidable.
- With sums of a sum, parenthesize the entire summand `(f a b+g a b)`;
  otherwise the second term can escape the binder scope.
- `rw [← Real.rpow_natCast]` rewrites the first natural power, which might
  be a constant 2^64 instead of the intended (N^eta)^64. Strip the common
  coefficient using `congr 1` first.
- Many harmless linter warnings remain; no incomplete proofs.

## Remaining problem and possible next steps

The new sieve gives nontrivial lower proportions, but NO signed mean
cancellation or density existence. The previously established exact modular-
inverse kernel and rationalFactorSign reductions are still unresolved.

Potential use of the full-log sieve: improve comparable cofactor harmonic
rows from the old C² bound to O(1+log C). This could extend fixed-ratio near-tie
rarity to a shrinking band for normalized logarithmic prime factors. That
would still be an auxiliary regularity result, not joint symmetry.

Alternatively seek a genuine signed estimate beyond the current triangle-
inequality obstruction. Do not infer independence or symmetry merely from
single-variable prime harmonic laws or from these upper sieve bounds.

## Latest batch: normalized-logarithmic near-tie rarity

The original theorem in Spec.lean is STILL UNRESOLVED and still has its sorry.
None of the following is a proof or disproof of density one half.

All files below have compiled .olean files, and the principal theorem axioms
were checked to be only propext, Classical.choice, Quot.sound.

1. `LogComparableCofactors.lean` (completed in the preceding batch):
   comparable slope sum <= (1+2 log C)*exp16*(1+log X), giving the
   full-log Selberg cofactor estimate with logarithmic dependence on C.

2. `PowerComparableCofactors.lean` (pending file repaired and verified):
   - `comparableCofactorPrimeSet_power_ratio_bound` with C=ceil N^delta,
     X=floor N^alpha, z=floor N^eta, 2*alpha+64*eta<1:
       card/N <= (4 exp19/eta^2)
         *(2delta+(1+2log2)/logN)*(alpha+1/logN)
         +2^65*N^(-(1-2alpha-64eta)).
   - `comparableCofactorPrimeSet_power_eventually_le`:
       eventually card/N <=(8 exp19 alpha/eta^2)*delta+epsilon.

3. `LogNearTieRanges.lean` imports PowerComparableCofactors,
   BothLargePrimeBound, SmallNearTieDensity.
   - `logRatioEvent N delta n`: P(n)<=N^delta*P(n+1) and converse,
     expressed as inequalities in the reals.
   - `logRatioSet N delta`: this event in range N.
   - `lowLogRatioSet N alpha delta`: additionally n>1 and both factors<=N^alpha.
   - `highLogRatioSet N beta delta`: additionally n>1 and both factors>=N^beta.
   - `highLogRatioSet_eventually_le`: high count/N <=
       (8 exp19*(1-beta)/eta^2)*delta+epsilon,
     assuming beta<=1, delta>=0, eta>0, 2*(1-beta)+64eta<1.
   - `lowLogRatioSet_card_bound`: finite CRT bound plus exception
       P(n+1)<=(ceil N^delta+1)*2^A.
     Using the n+1 factor avoids any shifted-count error.

4. `LowLogNearTieBound.lean` imports LogNearTieRanges, QuadraticSmoothBound.
   - `logPowerIndex N a = floor(a*logN/log2)+1`.
   - `logPowerIndex_power_bound`: 2^index<=2N^a.
   - `comparablePrimeMass_power_width_bound`:
       mass(ceilN^delta,index,D)<=64delta/a+192/(a*logN/log2).
     Uniform in D; a>0, delta>=0, N>1.
   - `logRatio_smooth_cutoff_bound`: the exceptional cutoff is<=N^(2a)
     if delta<=a/2 and 6<=N^(a/2).
   - `lowLogRatioSet_eventually_le` for alpha<1/2, a>0, 0<=delta<=a/2:
       eventually card/N<=320a^2+64delta/a+epsilon.

5. `LogNearTieRarity.lean` imports LowLogNearTieBound, PrimeBandDensity.
   - `primeDivisorBandSet_eventually_le`: endpoint band count/N
       <=8*(v-u)/u+epsilon.
   - `logRatioSet_subset_ranges`: for delta<=tau, N>1, tau>=0,
       logRatioSet subset range2 U low(alpha=1/2-tau)
         U primeDivisorBand(u=1/2-2tau,v=1/2+2tau)
         U high(beta=1/2+tau).
     The band is detected by P(n+1).
   - `logRatioSet_eventually_le` for 0<tau<=1/8, a>0,
     0<=delta<=min(a/2,tau):
       card/N<=320a^2+64delta/a+32tau/(1/2-2tau)
         +(8exp19*(1/2-tau)/(tau/64)^2)*delta+epsilon.
   - **`logRatioSet_uniform_rarity`**:
       forall epsilon>0, exists delta>0, eventually card/N<=epsilon.
     Chooses a=min(1,epsilon/2560), tau=min(1/8,epsilon/1024),
     K=8exp19*(1/2-tau)/(tau/64)^2,
     delta=min(a/2,min(tau,epsilon/(8*(64/a+K+1)))).
     This completes the promised normalized-logarithmic near-diagonal
     regularity theorem. It is stronger than fixed-ratio near-tie rarity.

6. `SubpowerComparisonStability.lean` imports LogNearTieRarity.
   Namespace Erdos371 (the preceding files use Erdos371.FiniteSieve).
   - `power_near_tie_exception_hasDensity_zero`: if for every delta>0,
     eventually E(n) implies logRatioEvent n delta n, then E has density0.
   - `shrinking_logRatioEvent_hasDensity_zero`: for any real w(n)->0,
     {n:logRatioEvent n (w n) n} has density0.
   - **`subpower_multiplicative_perturbation_density_iff`**:
     positive integer a(n),b(n) each eventually<=n^delta for every delta>0
     give equivalent density statements for
       a(n)P(n)<b(n)P(n+1) and P(n)<P(n+1), for every density d.
     This extends the bounded multiplier stability theorem but does NOT
     establish existence of a density.

### Remaining barrier

Normalized-logarithmic near-ties are now handled. This permits continuous
approximations or increasingly fine logarithmic bins without losing positive
mass on the diagonal. It does NOT supply symmetry of the two-dimensional
limiting distribution. The signed modular-inverse kernel, rationalFactorSign
mean cancellation, mixed correlation symmetry, and gap-invariance hypotheses
all remain unproved. Equal marginals, no near ties, and dilation invariance
must NOT be substituted for joint symmetry.

The latest investigation considered whether dilation invariance plus the new
anti-concentration might force symmetry. No such theorem was established.
Self-similar dyadic subdivision models can retain cyclic comparison bias;
controlling all multiplier progressions would require a genuinely new step.

## Latest batch: logarithmic signed reductions and dilation audit

Spec.lean is STILL unchanged and unresolved. No proof/disproof is ready.

New files (all compiled with saved .olean; principal theorem axioms checked):

1. `LogarithmicSignedReduction.lean` imports LogNearTieRarity and
   SmoothedComparison, namespace Erdos371.
   - `primeLog n = Real.log (Nat.maxPrimeFac n)` (zero at n=0).
   - `normalizedPrimeLog N n = primeLog n / log N`.
   - `logDifference N n = (primeLog(n+1)-primeLog n)/log N`.
   - `primeLog_mul_change`: for k>0 and every n,
       0 <= primeLog(kn)-primeLog(n) <= log k.
   - `normalized_log_gap_dilation_bound` for N>1,k>0:
       |(L_N(k(n+1))-L_N(kn))-logDifference(N,n)|<=logk/logN.
     IMPORTANT: the gap-k side is restricted to divisible starting points.
     This is NOT full gap invariance and does not prove joint symmetry.
   - `normalizedPrimeLog_mem_unit`: n<=N,N>1 gives L_N(n) in [0,1].
   - `logDifference_sum`: sum_{n<N} D_N(n)=L_N(N).
   - `logDifference_first_moment_tendsto_zero`: mean D_N ->0 by telescoping.
   - `logRatioEvent_iff_logDifference`: for N>1,n>0,
       logRatioEvent(N,delta,n) iff |D_N(n)|<=delta.
   - `clippedOdd delta x = x/max(delta,|x|)`;
     `clippedLogSign delta N n = clippedOdd delta (D_N(n))`.
     For delta>0 this is a continuous odd function, bounded by1 in absolute
     value, equal to sign outside [-delta,delta].
   - `clippedLogSign_error_sum_bound`:
       sum|factorSign-clip|<=2+2*card(logRatioSet N delta).
   - `clippedLogSign_uniform_approximation`: forall epsilon>0, some delta>0
     gives mean absolute error<=epsilon eventually.
   - `continuous_odd_logDifference_cancellation_implies_density`:
     IF every continuous odd f has mean f(D_N)->0, THEN the target holds.
     That hypothesis is UNPROVED; only f(x)=x was handled unconditionally.

2. `ClippedLogCriterion.lean` imports LogarithmicSignedReduction.
   - `clippedLogSign_small_width_approximation`: strengthens the previous
     approximation uniformly for all positive eta<=delta, simultaneously
     at sufficiently large N.
   - **`density_iff_arbitrarily_fine_clipped_cancellation`**:
       original target iff
         forall epsilon>0, exists delta with 0<delta<=epsilon, eventually
           |mean clippedLogSign(delta,N,n)|<=epsilon.
     This is an EXACT new equivalent signed target, not a proof of either
     side. The restriction delta<=epsilon is essential; otherwise taking
     huge clipping widths would make the condition trivially true.

3. `LogarithmicCubicMoment.lean` imports LogarithmicSignedReduction.
   - `cubicLogSkew N n = L_N(n)^2*L_N(n+1)-L_N(n)*L_N(n+1)^2`.
   - `logDifference_cube_sum`:
       sum D_N(n)^3=L_N(N)^3+3*sum cubicLogSkew(N,n).
   - endpoint cube/N ->0.
   - `logDifference_cube_cancellation_iff`: mean D_N^3->0 iff mean
     cubicLogSkew->0. NEITHER CANCELLATION STATEMENT IS PROVED.
   - Continuous-odd test cancellation implies cubic skew cancellation.
     Cubic cancellation is part of that stronger sufficient route, NOT
     asserted necessary for the original density conjecture.

The attempted dilation route still has the progression-independence gap.
No argument removing the divisible-progression restriction was found.
The cubic expansion identifies a specific nonlinear correlation that the
first-moment telescoping identity does not control. The exact clipped
criterion also remains unresolved, alongside the earlier rational and
modular-inverse kernel criteria.

A request to the external reference page failed because DNS/network access
was unavailable; no external theorem/status update was obtained.

## Latest batch: smooth-cutoff reciprocity and rank-two kernels

The target Spec.lean is STILL unchanged, with its original sorry. No proof
or disproof is ready. All new files below compile; their principal theorem
axioms are only propext, Classical.choice, Quot.sound.

### 1. SmoothCutoffSkew.lean

Imports RoughMobiusHarmonic, BalancedKernel. Namespace Erdos371.

- `smoothIndicator B n = if P(n)<=B then 1 else0` (real-valued).
- `smoothCutoffSkew B C N` sums, for n<N,
    s_B(n+1)s_C(n+2)-s_C(n+1)s_B(n+2).
- `divisorConvolution f n = sum_{d|n} f(d)`.
- `divisorSkewKernel f g N` is
    sum_{a,b<N+2} f(a)g(b)*(bilinearCount(N,a,b)-bilinearCount(N,b,a)).
- Generic product and skew convolution identities are proved.
- `smoothCutoffSkew_full_kernel`: S(B,C,N)=K(roughMu_B,roughMu_C,N).
- `primeBandMoebius B C d = mu(d)` if d>1 and B<minFac(d)<=C, else0.
- `properRoughMoebius C d = mu(d)` if d>1 and C<minFac(d), else0.
- **`smoothCutoffSkew_band_kernel`**, B>=1, B<=C:
    S(B,C,N)=s_C(N+1)-s_B(N+1)+K(bandMu_BC,properRoughMu_C,N).
  Thus the weights are a separable rank-two skew, rather than the earlier
  discontinuous least-prime-factor sign weight.
- `smoothCutoffSkew_cancellation_iff`: for ANY sequences B(N)>=1 and
  C(N)>=B(N), normalized smooth skew tends0 iff normalized band kernel tends0.
  Endpoint correction is uniformly O(1/N).

### 2. UpperHalfSmoothSkew.lean

Imports SmoothCutoffSkew.

- `prime_of_large_minFac`: d>1, D<minFac(d), d<=D^2 imply d is prime.
- Band/proper rough Moebius weights reduce to minus prime indicators above
  the square-root cutoff.
- `primeBandDiscrepancy B C N` is the UNWEIGHTED sum of
    bilinearCount(N,p,q)-bilinearCount(N,q,p)
  over primes B<p<=C and q>C, with p,q<N+2.
- **`smoothCutoffSkew_above_sqrt`** for N+1<=B^2, 1<=B<=C:
    S(B,C,N)=s_C(N+1)-s_B(N+1)+primeBandDiscrepancy(B,C,N).
- The signed prime discrepancy sum has NOT been estimated as o(N).
  Its reduction to primes does not make termwise absolute bounds sufficient.

### 3. PowerSmoothReciprocity.lean

Imports SmoothCutoffSkew, ClippedLogCriterion.

- `thresholdBit a i = 1_{a<=i}`; `orderedGridSkew M a b` sums the adjacent
  threshold determinants over i<M. For a,b<=M it is three-way sign(a,b).
- `powerGridLabel M N n = ceil(M*normalizedPrimeLog N n)`.
- `powerGridCutoff M N i = floor(N^(i/M))`.
- For M>0,N>1,
    label(M,N,n)<=i iff P(n)<=powerGridCutoff(M,N,i).
- Equal labels for n<N imply |logDifference(N,n)|<=1/M.
- `powerGridSign M N n` is the ordered grid skew of adjacent labels.
- `powerGridSign_uniform_approximation`: for every epsilon>0 some FIXED
  M>0 makes its mean absolute error from factorSign <=epsilon eventually.
  This uses normalized-log near-tie rarity.
- Grid sign equals a finite sum of adjacent smooth-cutoff determinants.
  Shifting the n-average changes it by at most 2M/N.
- **`density_of_power_smooth_reciprocity`** proves the original conjecture
  CONDITIONALLY on, for every M>0 and every i<M,
    S(floorN^(i/M),floorN^((i+1)/M),N)/N ->0.
  No interior power-cutoff reciprocity was proved. This condition is
  sufficient, NOT claimed necessary for the original conjecture.

### 4. SmoothSkewCancellation.lean

Imports SmoothCutoffSkew.

- `smoothCutoffSkew_abs_bound`:
    |S(B,C,N)|<=2*#{n<N:P(n)<=B}+4, uniformly in C.
- `smoothCutoffSkew_tendsto_zero_of_smooth_count`: any vanishing smooth
  count for B(N) gives skew cancellation uniformly in arbitrary C(N).
- **`smoothCutoffSkew_subpower_cancellation`**: if
    log(B(N)+1)/logN ->0, then S(B(N),C(N),N)/N ->0 for ANY C(N).
- **`subpower_band_kernel_cancellation`**: with B>=1 and C>=B, the
  corresponding signed separable band kernel genuinely tends0 after /N.
  IMPORTANT: this does NOT estimate the earlier sign(minFac) kernel and
  does NOT cover B=N^u for a fixed u>0.

### Current arithmetic barrier

The subpower signed cancellation reflects the rarity of subpower-smooth
integers. Interior power-sized smoothness events are not rare, so the same
argument does not extend. Knowing K(roughMu_B0,roughMu_C)=o(N) for all C and
subpower B0 does NOT imply K(roughMu_B,roughMu_C)=o(N) for arbitrary B,C:
roughMu_B0 has divisor convolution approximately constant, whereas the
interior-cutoff functions are nonconstant.

For upper-half power cutoffs the remaining problem is now an explicit
unweighted prime-band reciprocal-discrepancy sum. Lower-half cutoffs retain
composite rough divisors. Neither signed estimate was obtained. The earlier
first-moment, dilation, continuous-clipping and cubic reductions remain
valid but do not fill this gap.

## Latest batch: top-corner signed estimates

Spec.lean is STILL unchanged and unresolved. No proof/disproof is ready.
No logarithmic-density theorem was proved in this batch either.

1. `TopBandSkewBound.lean` imports UpperHalfSmoothSkew, BothLargePrimeBound.
   Namespace Erdos371.
   - `shiftedLargePairSet B N`: n<N with both P(n+1),P(n+2)>B.
   - `smooth_band_skew_term_abs_le`: the band/proper-tail skew pointwise
     absolute value is bounded by the indicator that BOTH factors exceed B.
   - `band_kernel_abs_le_large_pairs`: |K(bandMu_BC,properRoughMu_C,N)|
     <=card(shiftedLargePairSet B N), for 1<=B<=C.
     This is an absolute bound AFTER summing the kernel, not an assertion
     of cancellation of individual divisor summands.
   - `shiftedLargePairSet_card_bound`: if N^(1-u)<=B, then the shifted count
     is <=card(bothLargePrimeSet N u)+1 (inject n -> n+1; one endpoint).
   - `band_kernel_top_ratio_bound`: the earlier full-log sieve supplies
       |K|/N <=largePairConstant*(u+1/logN)^2
         +2^65*N^(-1/2)+1/N, for 0<=u<=1/8.
   - **`band_kernel_top_eventually_le`**: for arbitrary cutoff sequences
     eventually 1<=B<=C and N^(1-u)<=B,
       eventually |K|/N<=largePairConstant*u^2+epsilon.
   - **`primeBandDiscrepancy_top_eventually_le`**: same bound for the
     unweighted prime-band discrepancy, with the additional eventual
     condition N+1<=B(N)^2.
   - This is O(u^2), NOT o(1) for fixed u>0.

2. `NearLinearSkewCancellation.lean` imports TopBandSkewBound.
   - `nearLinear_cutoff_eventually_ge_power`: B>=1 and
     log B(N)/logN ->1 imply N^(1-u)<=B(N) eventually for every u>0.
   - `nearLinear_cutoff_eventually_above_sqrt`: same hypotheses imply
     N+1<=B(N)^2 eventually. Proof uses log B/logN>1/2 and integrality.
   - **`nearLinear_band_kernel_cancellation`**: if B>=1,C>=B and
     log B(N)/logN ->1, then the signed band kernel /N ->0.
   - **`smoothCutoffSkew_nearLinear_cancellation`**: corresponding smooth
     cutoff skew /N ->0.
   - **`primeBandDiscrepancy_nearLinear_cancellation`**: corresponding
     unweighted prime-band discrepancy /N ->0.
   - These genuinely prove cancellation in the exponent-one boundary
     regime, but not for any fixed exponent 0<u<1.

Both files compiled and .olean files were saved. Principal theorem axioms
were checked to be only propext, Classical.choice, Quot.sound.

### Investigation of logarithmic averaging

No available Mathlib theorem directly provided the needed entropy-decrement,
prime exponential-sum, or natural-density transfer argument. More importantly,
a logarithmic averaging result alone would not meet the original target.
The natural averaging version of the dilation argument changes the endpoint
from X to X/p. An entropy-decrement-selected multiplier cannot simply be
chosen to land at a prescribed natural averaging endpoint. Restricting primes
to a short multiplicative interval does not by itself remove that selection/
scale issue. No arithmetic gap-invariance or progression-independence theorem
was obtained, and no logarithmic cancellation is being asserted.

### What remains

The signed kernels are now controlled at BOTH boundary exponent regimes:
subpower lower cutoffs (log B/logN ->0) and near-linear lower cutoffs
(log B/logN ->1). The fixed positive-power interior is still unproved.
The condition in density_of_power_smooth_reciprocity requires that interior,
so it cannot be discharged from these endpoint results.

## Stationary low-moment obstruction verified

`StationaryMomentObstruction.lean` imports RefinedPartitionObstruction and
now compiles. Its principal theorem axioms are only propext,
Classical.choice, Quot.sound.

The seven-state transition table has constant row/column mass 14. Its
largest-label rising/falling/tie masses are respectively 41, 43, 14 out
of total 98. Every two-step entry is 28; all later powers are uniform.
For inclusion observations with combined mass at most 966, arbitrary
conditioning on the model's tail type factors at EVERY positive gap.
Thus those low-observation gap identities do not imply symmetry of the
largest-label comparison.

This is NOT an arithmetic counterexample. It has positive diagonal mass,
does not implement logarithmic near-tie rarity, and does not impose the
older finite model's disjoint-support condition. No new cancellation
estimate for the arithmetic kernel was obtained in this step. Spec.lean
remains unchanged with its sorry.

## Exact opposite-residue prime-progression decomposition

`PrimeBandProgressions.lean` imports UpperHalfSmoothSkew. It compiles, with
an .olean saved. The printed axioms of its main theorems are only the
three permitted axioms.

Definitions:
- cofactorResidueCount X p q minus: positive b<=X/q with p|(bq-1)
  if minus=true, or p|(bq+1) if minus=false.
- oppositePrimeCount C X p b minus: primes C<q<=X satisfying the same
  divisibility condition.
- primeResidueClassCount C X p r: primes C<q<=X in r:ZMod p.

Verified exact identities:
- bilinearCount N p q = cofactorResidueCount (N+1) p q true, q>=2.
- bilinearCount N q p = cofactorResidueCount N p q false, q>0.
- sum_cofactorResidueCount switches the q and cofactor sums, with the
  exact cofactor range 1<=b<=X/(C+1).
- **primeBandDiscrepancy_progressions** expresses the original discrepancy
  as a sum over band primes p of
    SUM_{1<=b<=(N+1)/(C+1)} oppositePrimeCount C ((N+1)/b) p b true
    - SUM_{1<=b<=N/(C+1)} oppositePrimeCount C (N/b) p b false.
  The distinct endpoints are intentional and retained; no unproved
  endpoint cancellation is used.
- **progression_cofactor_coprime**: when N+1<=B^2, B<=C, and p>B is prime,
  every cofactor in the first range is smaller than B and coprime to p.
- **oppositePrimeCount_residue_classes**: for b>0 and b.Coprime p,
  the two counts are exactly the prime counts in b^{-1} and -b^{-1}
  modulo p.

No prime-progression estimate was proved. In the upper-half regime p is
larger than sqrt(N), so a direct level-1/2 prime-distribution theorem at
length <=N cannot cover these moduli. A possible level-one hypothesis
was considered, but neither it nor any conditional theorem invoking it
was formalized. The arithmetic cancellation remains unproved, as does
the conjecture. Spec.lean is still unchanged with its original sorry.

## Odd-character cancellation and cofactor energy

`OddCharacterSkew.lean` imports PrimeBandProgressions and compiles, with
an .olean saved. All printed theorem axioms are the permitted three.

Verified:
- odd_character_orthogonality:
    phi(p)*(1_{x=1}-1_{x=-1}) = 2 SUM_{chi odd} chi(x).
  Thus the principal and every other even character cancel exactly.
- **oppositePrimeCount_odd_characters**:
    phi(p)*(Pi_plus-Pi_minus)
      = 2 SUM_{chi odd} chi(b) SUM_{C<q<=X, q prime} chi(q),
  for b>0, with the SAME interval endpoint X in the two counts.
- odd_character_gram and odd_character_gram_initial: the odd-character
  Gram matrix on initial positive residues is diagonal when 2A<p.
- **odd_initial_interval_energy** for prime p and 2A<p:
    2 SUM_{chi odd} |SUM_{1<=b<=A} chi(b)|^2 = phi(p)*A.
- rectangularOppositePrimeSkew_characters factors the cofactor sum and
  prime sum for a RECTANGULAR block, with prime endpoint X independent
  of b. The original kernel is hyperbolic and is not identified with
  this rectangular block.
- **rectangularOppositePrimeSkew_energy_bound**:
    phi(p)*|D_rectangle|^2
      <= 2A SUM_{chi odd} |SUM_{C<q<=X, q prime} chi(q)|^2.
  This is a finite Cauchy--Schwarz estimate with exact cofactor energy.

The odd prime-character energy is NOT estimated. Even a useful per-modulus
energy estimate would need sufficiently strong averaging across moduli
and control of the hyperbolic endpoint to yield the required o(N) bound.
No new fixed-interior arithmetic cancellation limit was proved.
Spec.lean remains unchanged with its original sorry; no proof/disproof
is ready for submission.

## Structural-route check and finite prefix obstruction

Spec.lean is STILL unresolved and unchanged.

`PrefixBalanceObstruction.lean` imports Explore. It compiles and has an
.olean. The exact counts in the original range {0,...,3912} are:
  risingCount 3913 = 1955, fallingCount 3913 = 1958.
Both this conjunction and not_all_prefixes_rise_dominant were proved
with only the permitted axioms; the finite count uses `decide +kernel`.
This rules out a proposed prefix-nonnegativity shortcut. It is NOT a
counterexample to the density conjecture, and does not show anything
about asymptotic density failing to exist.

### Further analysis of the character-energy approach

The missing step is not merely an optimal estimate for each modulus's
prime-character energy. Even an energy of the expected diagonal size
would leave a rectangular per-modulus square-root bound. Taking absolute
values and summing this over prime moduli above sqrt(N) loses too much.
A genuinely signed estimate across moduli (and treatment of the
hyperbolic endpoint) is needed. No such estimate was obtained.

### Other structural ideas considered but NOT formalized

- Cycles of consecutive-factor edges satisfy a product divisibility
  constraint. If n_i -> n_i+1 has factors p_i -> p_(i+1), then the
  product of the p_i divides prod(n_i+1)-prod(n_i). For a directed
  k-cycle with n_i<=N this suggests the bound by
  (N+1)^k-N^k. This does not force reversibility: longer directed cycles
  remain possible. No cycle theorem was added to the project.
- Approximating the largest logarithmic prime factor by high power sums
  of logarithmic prime factors would lead to multiplicative phase
  autocorrelations. Their needed uniform imaginary-part cancellation
  is not known here. A generic assertion of uniform reality for ALL
  completely multiplicative functions is unsafe: functions n^(i*c*N)
  have a nontrivial phase increment on scale N. No multiplicative
  autocorrelation theorem or additive-score reduction was proved.

No proof or disproof is ready for submission.

## Additive logarithmic scores and multiplicative phases

`AdditiveLogScores.lean` imports LogarithmicSignedReduction, compiles,
and has an .olean saved. All printed theorem axioms are the allowed three.
Spec.lean is still unchanged and unresolved.

Definitions:
- additiveLogScore k n = SUM_p v_p(n)*(log p)^(k+1).
  The index is k; the exponent is k+1.
- normalizedAdditiveLogScore k N n divides this by (log N)^(k+1).
- additiveScoreSign k n is the THREE-WAY comparison sign of consecutive
  scores, with value zero for equal scores.
- additiveScorePhase k N t : Nat ->*0 Complex is zero at zero and
  exp(i*t*normalizedAdditiveLogScore k N n) for positive n.

Verified:
- additiveLogScore_mul: complete additivity, no coprimality needed.
- additiveLogScore_zero_index: index zero is log(n) for n>0.
- **normalizedAdditiveLogScore_sandwich**, for 0<n<=N and N>1, writing
  M=log P(n)/log N:
    M^(k+1) <= normalized score <= (M+1/(k+1))^(k+1).
  The intermediate upper bound is M^k. It uses total prime-factor log
  mass <=log N, not a bound on the number of factors.
- additiveLogScore_lt_of_log_gap: a normalized largest-log gap greater
  than 1/(k+1) determines the order of the additive scores.
- **additiveScoreSign_uniform_approximation**:
    for every epsilon>0, some K satisfies eventually in N, for ALL k>=K,
      mean_n<N |factorSign n-additiveScoreSign k n| <=epsilon.
  This uses the already-proved normalized-logarithmic near-tie rarity.
- additiveScorePhase_norm: unit modulus for n>0.
- **additiveScorePhase_correlation_im**: the imaginary part of the
  adjacent phase autocorrelation is exactly sin(t*(score_next-score)).
  No average of this correlation is evaluated.
- additiveScoreSign_zero_index: index-zero sign is 1 for every n>0.
  Thus cancellation does NOT hold automatically for every additive score.
- **density_of_additive_score_cancellation** proves the ORIGINAL target
  conditionally on: for every K there exists a FIXED k>=K whose signed
  score average tends to zero. This sufficient hypothesis remains unproved.

### Quantifier caution for this route

The approximation is uniform in all k>=K, so growing degree sequences
are permitted for the approximation itself. But fixed-frequency phase
correlations with degree k(N)->infinity can collapse to 1 as the scores
collapse toward zero; their imaginary parts then vanish without implying
comparison balance. Such a collapse is not the fixed-score cancellation
hypothesis above. No claim of a multiplicative-correlation theorem is made.
No fixed positive-index score cancellation limit has been proved here.

No proof or disproof is ready for submission.

## Fixed-degree correlation investigation: no new theorem

Investigated the remaining fixed-degree additive-score cancellation.
No applicable natural-density multiplicative-correlation theorem was
found in Mathlib, and no replacement proof was obtained. Complete
multiplicativity alone has not been shown to imply the required reality
or sign balance of the adjacent correlations. The verified score
approximation and phase identities remain conditional tools only.

Potential divisor/Ramanujan expansions return to off-diagonal signed
terms whose divisor products exceed the averaging length. Taking
absolute values or using per-modulus Cauchy--Schwarz does not close that
estimate. No new fixed-interior cancellation or proof of the target was
obtained. Spec.lean remains unchanged with sorry.

## Dyadic non-between harmonic cancellation

The dyadic pointwise identity was already in Explore.lean; it was not
re-proved unnecessarily. A new module DyadicHarmonicCancellation.lean
imports Explore, compiles, and has an .olean saved.

Verified:
- factorSign_dyadic_positive extends the existing identity to n=1.
- harmonic_dyadic_coboundary_bound: for ANY real sequence f with |f(n)|<=1,
    |SUM_{n=1..N} (f(n)-(f(2n)+f(2n+1))/2)/n| <= 3.
  The proof separates the doubled harmonic block, a bounded endpoint
  block, and reciprocal-denominator errors with a telescoping majorant.
- nonBetweenHarmonicSum N is
    SUM_{n=1..N} factorSign(n)*1_{NOT factorBetween(n)}/n.
- nonBetweenHarmonicSum_bound: its absolute value is <=3 uniformly in N.
- nonBetween_logarithmic_cancellation: dividing this particular sum by
  log(N+1) gives a sequence tending to zero.

All three principal theorems' axiom checks list only propext,
Classical.choice, Quot.sound. No admitted helper was used.

IMPORTANT LIMITATIONS:
This cancellation concerns only the NON-BETWEEN subevent. It does not
control the complementary signed between contribution. It does not assert
logarithmic density half for the full comparison, or natural density
half, or even existence of the individual non-between subevent densities.
The estimate is a generic bounded-sequence dyadic coboundary estimate,
not a contraction estimate for the original discrepancy.

Spec.lean remains unchanged with sorry. There is still no proof or
disproof to submit.

## Common hyperbolic endpoint and global odd-character formula

`CommonEndpointPrimeSkew.lean` imports OddCharacterSkew, compiles, and has
an .olean saved. All principal theorem axiom checks list only propext,
Classical.choice, Quot.sound.

New verified definitions and results:
- commonEndpointPrimeSkew B C N is the sum over band primes B<p<=C,
  p<N+2, and 1<=b<=N/(C+1), of the oppositePrimeCount difference with
  the SAME endpoint N/b for both signs.
- primeBandEndpoint B C N is the sum over band primes p and primes q>C
  of 1_{p|N AND q|(N+1)} (both prime sums restricted to range(N+2)).
- primeBandDiscrepancy_common_endpoint: the original prime-band discrepancy
  is commonEndpointPrimeSkew + primeBandEndpoint, exactly, for all B,C,N.
- prime_dvd_unique_above_sqrt: elementary uniqueness of a prime divisor
  greater than B in a positive integer <=B^2.
- primeBandEndpoint_bounds: if B<=C and N+1<=B^2, the endpoint correction
  lies in [0,1]. Thus endpoint alignment costs <=1 IN TOTAL, not per modulus.
- hyperbolicOppositePrime_odd_characters: odd-character expansion with
  the cofactor-dependent prime endpoint N/b retained exactly.
- oddHyperbolicPrimeSkew B C N is the complex sum
    SUM_{B<p<=C, p prime, p<N+2} 2/phi(p) *
      SUM_{chi odd mod p} SUM_{1<=b<=N/(C+1)}
        chi(b) SUM_{C<q<=N/b, q prime} chi(q).
- commonEndpointPrimeSkew_characters: its equality to the real common
  endpoint skew, embedded in Complex.
- primeBandDiscrepancy_odd_hyperbola_bound: norm of the original prime
  discrepancy minus oddHyperbolicPrimeSkew is <=1 in the upper-half regime.
- smoothCutoffSkew_odd_hyperbola_bound: the SAME bound <=1 holds for the
  smooth-cutoff skew when 1<=B<=C and N+1<=B^2. The smooth-convolution
  endpoint correction and the new alignment correction are mutually
  exclusive, so their total is <=1 rather than <=2.

The bulk odd-character sum is still UNESTIMATED. It is hyperbolic, not
rectangular. This module removes the endpoint mismatch rigorously; it does
not establish any fixed-interior cancellation or solve the target.
Per-modulus energy estimates and an absolute sum over moduli still lose
power in the range p>sqrt(N); no new analytic estimate closing that loss
was obtained.

Spec.lean remains unchanged with sorry. No proof or disproof is ready
for submission.

## A contracting cofactor remainder map

`CofactorDescent.lean` imports Explore, compiles, and has an .olean saved.
All printed axiom checks use only propext, Classical.choice, Quot.sound.
No conjecture proof or bulk cancellation estimate was obtained.

Writing p=P(n), q=P(n+1), a=n/p, b=(n+1)/q, define T(n) by:
  T(n)=n%(p*b) if p<q;
  T(n)=n%(q*a) otherwise.
This is primeCofactorDescent, distinct from the older primeReflection.

Verified arithmetic:
- prime_cofactor_remainder_fall: if p is prime, 1<b<p, p|n, b|(n+1),
  then m=n%(p*b)>0, P(m)=p, and P(m+1)<p.
- prime_cofactor_remainder_rise: if p is prime, 0<b<p, b|n, p|(n+1),
  then m=n%(p*b)>0, P(m)<p, and P(m+1)=p.
- **primeCofactorDescent_structure**: for n>1, n<P(n)P(n+1),
  and n+1 not prime:
    0<T(n)<n;
    factorSign(T(n))=-factorSign(n);
    max(P(T(n)),P(T(n)+1))=min(P(n),P(n+1));
    T(n)*max(P(n),P(n+1))<(n+1)*min(P(n),P(n+1)).
- primeCofactorDescent_eq_zero_of_prime_successor: prime successors map to 0.
- primeCofactorDescent_zero_iff: in the large-product region n>1,
  T(n)=0 iff n+1 is prime. This exception is genuine.
- **primeCofactorDescent_power_bound**: with n<N and the preceding hypotheses,
  if max(P(n),P(n+1))>=N^delta*min(P(n),P(n+1)), then T(n)<N^(1-delta).

Verified limitations (not disproofs of Erdős 371):
- primeCofactorDescent_collision: 14 and 44 both satisfy the large-product,
  non-prime-successor hypotheses, and both map to 4. The map is not injective.
- primeCofactorDescent_leaves_large_product: 245 satisfies the hypotheses
  and maps to 35, but P(35)P(36)=21<=35; the next value is T(35)=5.
  Thus the structure/sign-reversal lemma cannot be iterated automatically.
- No estimate of the preimage multiplicities was proved. Inverse descriptions
  again involve prime progressions and, outside the upper-half range,
  smooth-cofactor constraints. Contraction of indices alone does NOT prove
  equal comparison densities.

An external reference lookup was attempted again; DNS remained unavailable.
Spec.lean remains unchanged with sorry. No proof or disproof is ready to submit.

## Inverse-descent investigation: no bulk estimate obtained

Examined whether the contracting cofactor map bypasses the unresolved prime
progression discrepancy. It does not presently provide such a bypass.

Algebraic description (research reasoning, not a new Lean theorem):
- On the rising branch, let p=P(n), b=primeCofactor(n+1),
  m=n%(p*b), and k=n/(p*b). Then n=m+k*p*b, b|(m+1), and
  the higher prime q=P(n+1) equals (m+1)/b+k*p. Thus its residue r obeys
  b*r=1 mod p. The original cofactor of n must still be p-smooth.
- On the falling branch, retaining p=P(n+1) and b=primeCofactor(n),
  the analogous higher-prime progression has residue r=m/b and
  b*r=-1 mod p.
These descriptions bring the two orientations back to the opposite-residue
prime counts already occurring in CommonEndpointPrimeSkew. No estimate of
the difference of the preimage counts has been proved.

Also considered combining the old primeReflection on the small-product
region with cofactor descent on the large-product region. A pointwise
sign-reversing descent still would not supply an injective pairing or
control preimage multiplicities. No such density inference is asserted,
and no additional map-combination theorem was added.

No new verified theorem or fixed-interior signed cancellation was obtained
in this investigation. Spec.lean remains unchanged with sorry. There is
still no complete proof or disproof to submit.

## Additive inverse-theorem investigation: no new theorem

Investigated whether a persistent adjacent-comparison bias could force the
additive logarithmic scores into a logarithmic model. No applicable inverse
theorem was found in the Mathlib arithmetic-function or dynamics sources,
and no proof of the required inverse implication was obtained.

The existing score approximation only transfers the original comparison
problem to high-degree score signs. Complete additivity alone supplies no
cancellation (the verified degree-zero score is log(n), whose positive-index
increments all have positive sign). No claim is made that a nonlogarithmic
score automatically has a balanced sign distribution, or that a general
inverse theorem is false; the needed implication remains unproved.

Also reconsidered weighted prime-factor mass identities. These provide
marginal/telescoping relations but no proved elimination of the nonlinear
antisymmetric correlations. No new bulk estimate, Lean helper, proof, or
disproof was obtained in this round.

Spec.lean is unchanged and still contains sorry. Nothing has been submitted
as a completed solution.

## Logarithmic/ergodic investigation: neither required step proved

Revisited a possible logarithmic symmetry route for the stable normalized
largest-prime-factor labels. No logarithmic density-half theorem was proved.
The existing Hilbert-space symmetry theorem still requires an arithmetic
correlation invariance/symmetry input that is not available here.

The library search found no ready entropy-decrement/isotopy or prime-ergodic
result supplying that input. No missing theorem was assumed. In particular,
uniform control under dilation on divisible starting points was not promoted
to unrestricted gap correlations.

The natural-endpoint obstruction remains separate: dilation relates a gap-p
average near endpoint N to an original comparison average near N/p. A
hypothetical logarithmic balance theorem by itself would not establish the
natural-density limit. No valid Tauberian upgrade or endpoint-stability
estimate was obtained.

No new Lean theorem, bulk cancellation estimate, proof, or disproof resulted
from this round. Spec.lean is unchanged with sorry. No completed solution has
been submitted.

## Nonnegative multiplicative-function route: uniformity still missing

Considered adjacent-correlation symmetry for bounded nonnegative completely
multiplicative functions, motivated by the smooth-number indicators. The
Mathlib search did not supply a theorem establishing the required uniform
moving-cutoff symmetry, and no such theorem was proved here.

A fixed-function convergence argument would not license replacing its prime
cutoffs by B(N), C(N). Its onset of convergence could depend on those cutoffs.
The existing verified results still cover subpower and exponent-one boundary
regimes, not fixed positive exponents in the interior. No uniform rate or
other argument closing that distinction was obtained.

No new Lean theorem or fixed-interior signed cancellation was added in this
round. Spec.lean is unchanged with sorry; there is no completed proof or
disproof to submit.

## Fixed logarithmic mass revisited: no missing cancellation obtained

Re-examined whether the exact prime-factor logarithmic mass identity could
close the bulk signed gap. The existing `PartitionObstruction` modules
already verify fixed total mass for every partition, equal marginals,
symmetric low-mass inclusion moments, and biased largest-part comparisons.
Thus fixed mass plus those moment constraints alone is not sufficient.
These models are not arithmetic counterexamples; no claim is made that they
satisfy all arithmetic constraints or the actual prime-factor marginal law.

No stronger arithmetic identity, new bulk estimate, or new Lean theorem
was obtained in this investigation. Recompiled `Submission/Spec.lean`:
it still reports the original declaration uses `sorry`. The target and
its import were left unchanged. No completed proof or disproof is ready
for submission.

## Uniform small-multiplier investigation: transfer still unproved

Considered exploiting the exact small-multiplier invariance of the moving
smooth indicators, rather than only normalized-log dilation bounds.
No unrestricted natural-average transfer was proved. Restricting a gap-p
average at endpoint N to p-divisible starting points still yields an
adjacent average at endpoint approximately N/p. Moving the ambient endpoint
to p*N instead does not justify a common-scale entropy argument when p is
itself selected by that argument. No such selection or endpoint-stability
estimate was supplied.

The Mathlib search again found no correlation/entropy-decrement theorem
that closes this step. No new arithmetic theorem or completed proof was
obtained. Spec.lean remains unchanged with its original sorry.

## Verified moving multiplicative chirp obstruction

New file: `Submission/MultiplicativeChirpObstruction.lean`, importing only
FormalConjecturesUtil. It compiles without warnings, and an .olean is saved.
All printed main-theorem axiom checks list only propext, Classical.choice,
Quot.sound. The temporary Check.lean was removed.

This formalizes a previously only informal chirp obstruction. It is NOT a
counterexample to Erdős 371 or to smooth-cutoff reciprocity.

Namespace: `Erdos371.MultiplicativeChirpObstruction`.
- `chirp (t : ℝ) : ℕ →*₀ ℂ` is zero at zero and exp(i*t*log n) otherwise.
  It has norm one at positive integers, and norm at most one everywhere.
- `chirp_correlation_im`: its adjacent autocorrelation has imaginary part
  sin(t*(log(n+1)-log n)).
- **`chirp_correlation_sum_lower`**: for every N>=9,
    sum_{1<=n<=N} Im(chirp N (n+1)*conj(chirp N n)) >= N/60.
  Proof is analytic, not numerical: N*log(1+1/n) lies between N/(n+1)
  and N/n. The sine is nonnegative for n>N/3 and >=7/10 for n>N/2;
  all remaining terms are >=-1. Exact interval counts give N/60.
- `chirpCorrelationMean_lower`: the normalized mean is at least 1/60.
- `chirpCorrelationMean_not_tendsto_zero`.
- `chirp_dilation_bound`: for all n,k,t,
    |chirp t (k*n)-chirp t n| <= |chirp t k-1|.
- **`exists_chirp_subsequence_fixed_multipliers`**: there is a : Nat->Nat
  tending to infinity such that chirp(a_j)(k)->1 for every fixed k>0,
  while the above adjacent mean at endpoint a_j stays >=1/60 eventually.
  The proof uses sequential compactness of the countable torus. From a
  convergent subsequence with strictly increasing indices phi(j), take
  a_j=phi(2j)-phi(j)>=j; ratios converge to one in every coordinate.
- **`exists_dilation_stable_biased_chirps`**: on this same sequence, for
  every fixed k>0 and epsilon>0, eventually ALL n satisfy
    |chirp(a_j)(k*n)-chirp(a_j)(n)|<epsilon,
  while the imaginary adjacent correlation mean stays >=1/60.

Precise limitation established: complete multiplicativity, boundedness,
and asymptotic invariance under each fixed multiplier (even uniformly in
starting points) do NOT imply real natural adjacent autocorrelations for
arbitrary endpoint-dependent complex families.

These functions are complex-valued, not nonnegative smooth indicators,
and do not have the largest-prime-factor max structure. No polynomial-sized
multiplier invariance is asserted for this model. No conclusion about the
original prime-factor comparison follows from it. In particular this is not
a valid `erdos_371.disproof` and has not been placed in Spec.lean as one.

Spec.lean was recompiled and still reports the original sorry. Its import
and conjecture statement remain unchanged. No complete solution is ready
for submission.

## After the chirp obstruction: stronger arithmetic structure still needed

Investigated whether stronger growing-multiplier control and the max /
nonnegative structure could turn the chirp obstruction into a positive
cancellation argument. No such argument or new theorem was proved.
The chirp subsequence theorem only provides invariance for each fixed
multiplier; it does not assert the stronger polynomial-range control
available in the prime-factor setting. It cannot be used as a disproof
of that setting's reciprocity or of the original conjecture.

Considered an inverse-correlation route excluding high Archimedean chirps,
but no inverse theorem establishing that these are the only possible
obstructions was available or proved. Excluding one model would not by
itself prove the required correlations real or balance their signs.

Another attempt to access the Erdős reference page failed with DNS
resolution unavailable. No new Lean result was added in this round;
MultiplicativeChirpObstruction.lean remains the latest verified auxiliary
module. Spec.lean is unchanged with its original sorry. There is no valid
complete proof or disproof to submit.

## Analytic-exponent investigation: no cancellation theorem

Considered varying the exponent in additive prime-factor logarithmic scores.
The score with exponent one equals log(n), so its adjacent difference has
vanishing mean. This is only a single exponent; analytic dependence, even
if established with suitable bounds, would not justify extending that
vanishing to other exponents. The fixed-total-mass partition obstruction
is consistent with a power-sum difference vanishing at exponent one but
with biased largest-part comparisons.

No normal-family theorem, analytic continuation argument, or arithmetic
signed cancellation was proved in this round. No new Lean theorem or
change to Spec.lean was made. The original conjecture remains unresolved.

## Prime-label-count prefix bound ruled out

Tested the proposed combinatorial bound that a finite prime-cutoff
comparison has prefix rise-minus-fall discrepancy at most the number of
selected prime labels. It fails already for modulus 210 and endpoint 45.

Added to `Submission/PrefixBalanceObstruction.lean` (existing import unchanged):
- `cutoff_210_prefix_45_counts`: exactly 25 rises and 20 falls on range 45
  for cutoffPrime 210, while 210.primeFactors.card=4.
- `not_cutoff_prefix_bound_by_prime_count`: negates that universal bound,
  even restricting to positive even squarefree moduli.
Both were proved with kernel-checked finite arithmetic. The module compiles,
its .olean was updated, and all printed axioms are the permitted three.

This is only an obstruction to the proposed uniform finite-cutoff lemma.
It does NOT disprove a bound specifically for the original untruncated
maxPrimeFac sequence, and it is not a density counterexample. No new bulk
cancellation estimate or completed conjecture proof was obtained.
Spec.lean is unchanged with its original sorry.

## Prime-insertion recurrence investigated: signed gap persists

Re-examined inserting a new largest prime p into a finite cutoff modulus M
(all prime divisors of M smaller than p, with M positive and even).
At each interior multiple m of p, the new cutoff label becomes a strict
local maximum. Its two incident comparison signs then sum to zero; before
insertion their sum may be -2, 0, or 2. Thus the change of the prefix signed
count is minus the old two-sign sum over these multiples, with a bounded
endpoint correction. Multiplicative invariance identifies the center label
at p*k with that at k, but supplies no corresponding identification for
p*k-1 and p*k+1. The needed signed cancellation along those linear forms
was not established. This observation was not added as a Lean theorem.

No new bulk estimate, proof, or disproof was obtained. Spec.lean and its
import remain unchanged, with the original sorry. No completed solution
has been submitted.

## Verified square-root multiplier exclusion for the chirp model

New file: `Submission/PolynomialMultiplierChirpExclusion.lean`, importing
Submission.MultiplicativeChirpObstruction. It compiles, and its .olean is
saved. All three printed axiom checks list only propext, Classical.choice,
Quot.sound. Namespace Erdos371.MultiplicativeChirpObstruction.

- `chirp_sqrt_multiplier_separation`: for every N>=9 there is an integer k
  between floor(sqrt N)-1 and floor(sqrt N)+1 such that
    ||chirp N k - 1|| >= 1/8.
  This is an analytic, uniform result, not a finite computation. Put
  a=floor(sqrt N)-1, so a(a+2)+1=(a+1)^2 and N/2<a(a+2)<=N.
  The earlier adjacent sine bound gives imaginary correlation >=7/10 at
  a(a+2). Complete multiplicativity and triangle inequalities bound it
  by ||chirp N a-1|| + 2||chirp N (a+1)-1|| + ||chirp N (a+2)-1||.
- `no_uniform_sqrt_multiplier_invariance`: along ANY unbounded parameter
  sequence a_j, the chirps cannot converge uniformly to one on the positive
  multipliers k<=floor(sqrt a_j)+1.
- `maxPrimeFac_cutoff_small_multiplier`: for k>0, k<=B, and every n,
    P(k*n)<=B iff P(n)<=B.
  The n=0 case is included. Thus the arithmetic cutoff has exact invariance
  on a growing range, unlike the complex chirp obstruction at sqrt scale.

Limitations: this excludes the specific chirps only on the square-root
range. No exclusion on every smaller positive power range is claimed.
No theorem that chirps exhaust possible asymmetric-correlation obstructions
has been proved. In particular these results do NOT supply smooth-cutoff
reciprocity, fixed-degree additive-score cancellation, or a density proof.
Spec.lean remains unchanged with the original sorry; no completed proof or
disproof has been submitted.

## Verified chirp exclusion on every positive-power multiplier range

New file: `Submission/ChirpFiniteDifferences.lean`, importing
Submission.PolynomialMultiplierChirpExclusion. It compiles without warnings,
and its .olean is saved. All printed main-theorem axiom checks list only
propext, Classical.choice, Quot.sound. Namespace:
Erdos371.MultiplicativeChirpObstruction.

Verified calculus infrastructure:
- `hasDerivAt_fwdDiff_iter`: derivatives commute with finite forward
  differences on the positive real axis.
- `fwdDiff_iter_mean_value`: given a chain F_j with derivative F_{j+1},
  Delta^r F_0(x)=F_r(y) for some y in [x,x+r].
- `logDerivativeChain_hasDerivAt` and `log_fwdDiff_mean_value`:
  Delta^(r+1) log(x) = (-1)^r r! / y^(r+1) for some y in [x,x+r+1].
- `tendsto_scaled_log_fwdDiff`:
  x^(r+1)*Delta^(r+1)log(x) -> (-1)^r r! as x -> infinity.

Verified phase results:
- `phaseExp t x = exp(i*t*x)` and its subtraction/division identity.
- `tendsto_phaseExp_fwdDiff`: convergence to one of all fixed translates
  exp(i*a_j*log(k_j+s)) implies convergence to one of each fixed-order
  exponentiated logarithmic forward difference.
- `phaseExp_integer_ne_one`: exp(i*m) != 1 for each nonzero integer m,
  using irrationality of pi.
- `no_consecutive_resonance_at_power_scale`: if k_j -> infinity and
  a_j/k_j^(r+1) -> 1, the above convergence cannot hold for every fixed s.
- **`no_uniform_power_multiplier_invariance`**: for every delta>0 and
  every unbounded natural parameter sequence a_j, it is impossible that
  chirp(a_j)(m) -> 1 uniformly over positive m <= a_j^delta.
  Proof chooses r with 1/(r+1)<delta and k_j=floor(a_j^(1/(r+1))).
- **`eventual_power_multiplier_separation`**: for every delta>0 there is
  epsilon>0 such that, for all sufficiently large N, some positive
  m<=N^delta satisfies ||chirp N m-1||>=epsilon. A diagonal-selection
  argument derives this uniform eventual bound from the preceding theorem.

This supersedes the previous *square-root-only limitation* on what has been
proved about excluding the chirp model. It does NOT supersede the original
chirp obstruction: fixed-multiplier convergence is still possible and was
proved earlier. The distinction is fixed multipliers versus a growing
positive-power range.

Crucial remaining limitation: no inverse theorem reducing all possible
arithmetic correlation asymmetry to chirps was proved. Excluding this one
family, even on every positive-power range, does not establish cancellation
for smooth indicators or additive-score phases. The original signed bulk
gap remains. Spec.lean still has its unchanged original sorry. No completed
proof or disproof has been submitted.

## Growing-cofactor averaging investigated: no free shift average

Returned to BalancedKernel, RoughPartGoodPairs, SubpowerBalanced, and
UniqueRoughCofactor to examine whether removing bounded cofactor ranges
provides an ordinary averaged-shift cancellation argument.

For a divisor pair a|(n+1), b|(n+2), write n+1=a*u and n+2=b*v.
Then b*v-a*u=1. For fixed coprime u,v, solutions lie on coupled linear
forms a=a0+v*t, b=b0+u*t with v*b0-u*a0=1. The coefficients, residue
classes, admissible endpoints, and Mobius/least-prime-factor weights
remain coupled. Merely knowing u,v grow does not supply an unrestricted
average over independent additive shifts. No uniform weighted estimate
for these forms, or valid transfer from an averaged-shift theorem, was
established in this investigation.

No new Lean theorem was added this round. The previously compiled
ChirpFiniteDifferences results remain valid but do not estimate this
kernel. Spec.lean remains unchanged with its original sorry, and no
complete proof or disproof has been submitted.

## Prime-winner second-moment route formalized; energy estimate unproved

New verified file `Submission/PrimeWinnerEnergy.lean`, importing
RoughCofactors and SubpowerSmooth. It compiles without warnings and its
.olean is saved. All printed axioms are among the permitted three.
Namespace Erdos371.

Definitions:
- primeWinner n = max(P(n),P(n+1)).
- primeWinnerLabels N = {1} union primes below N+1. The extra label 1
  handles the original n=0 comparison.
- primeWinnerSum p N = sum of factorSign n over n<N with primeWinner n=p.
- primeWinnerEnergy N = sum_p (primeWinnerSum p N)^2 over those labels.

Verified results:
- primeWinnerSum_total: sum of group imbalances is risingCount-fallingCount.
- comparison_sq_le_primeWinnerEnergy: squared total discrepancy is at most
  the number of labels times primeWinnerEnergy, by Cauchy--Schwarz.
- primeWinnerLabels_card_tendsto_zero: number of labels / N tends to zero.
  Proof bounds primes by small primes plus sqrt(N)-rough numbers, using
  the previously proved elementary rough-number bounds.
- **density_of_linear_primeWinnerEnergy**: for any fixed real C, an eventual
  bound primeWinnerEnergy N <= C*N implies the original density-half claim.
  THIS IS CONDITIONAL. No such energy bound has been proved.
- primeWinner_23_116_counts: the actual, naturally ordered prime group 23
  has exactly 5 rises and 2 falls on [0,116), kernel checked.
- not_primeWinner_imbalance_le_two: individual groups are not universally
  bounded above by two in signed discrepancy.

Exploratory computations tested proposed group bounds, NOT counterexamples
to the density conjecture. They suggested examining a linear energy bound,
but finite computations provide no proof of such a bound. The only actual
prime-group numerical fact formalized is the 23,116 example above.

New verified file `Submission/PrimeWinnerEnergyObstruction.lean`, importing
only FormalConjecturesUtil. It compiles without warnings, .olean saved,
and all axiom checks are permitted. Namespace
Erdos371.PrimeWinnerEnergyObstruction.
- rank is an injective reordered-prime ranking. It places prime 3 at rank
  10243, primes congruent to 1 mod 3 above it, and other primes p at rank 2p.
- label n = sup of ranks of prime divisors of n.
- rank_injective and label_mul prove injectivity and the maximum-under-
  multiplication identity for positive arguments.
- group_three_counts: on [0,5121), the prime-3 winner group has exactly
  319 rises and 247 falls (kernel checked).
- single_group_energy_exceeds_N: its squared imbalance is 72^2=5184>5121.

Precise scope of this obstruction: it refutes deducing the candidate
constant-one energy bound from max-under-multiplication alone. It does NOT
refute any energy bound for the natural prime ordering, nor does this one
finite example refute all possible constants C in a linear bound. The
model's sup convention has label 0=label 1=0; no no-ties theorem for the
entire model was asserted. It is not a density disproof.

No new signed or quadratic estimate for the actual prime-winner groups
was obtained. The linear-energy hypothesis is a new concrete sufficient
target, not a solved step. Spec.lean remains unchanged with the original
sorry, and no completed proof or disproof has been submitted.

## Verified prime-winner flux and subpower-energy criterion

New verified files (saved .olean files; permitted axioms only):

- `PrimeWinnerFlux.lean`, imports PrimeWinnerEnergy and BothLargePrimeBound.
  Definitions primeLoser, primeLoserSum, bothAboveSet,
  primeWinnerL1Above, primeWinnerEnergyAbove.
  Exact identity `primeWinnerSum_sub_primeLoserSum`:
    winnerSum(p,N)-loserSum(p,N)=1_{P(N)=p}-1_{P(0)=p}.
  `primeWinnerL1Above_le_bothAbove` bounds the sum of absolute imbalances
  above B by #{n<N:P(n)>B and P(n+1)>B}+1.
  `primeWinnerSum_norm_le_multiples`: |winnerSum(p,N)|<=2 floor(N/p)+1.
  `primeWinnerEnergyAbove_bound`: if N<=K(B+1), high energy is at most
  (2K+1) times high L1 mass.
  `primeWinnerL1Above_top_eventually_le`: for 0<=u<=1/8 and cutoff
  B(N)>=N^(1-u), high L1/N is eventually <=largePairConstant*u^2+epsilon.
  `primeWinnerL1Above_fixed_cofactor_tendsto` and
  `primeWinnerEnergyAbove_fixed_cofactor_tendsto`: for fixed positive K,
  both high L1/N and high energy/N above floor(N/K) tend to zero.
  These are endpoint estimates, NOT bulk estimates.

- `PrimeWinnerSubpowerEnergy.lean`, imports PrimeWinnerFlux.
  `primeWinnerLowSum_sq_le`: low signed sum squared <=(B+1)*E(N).
  `primeWinnerLowSum_power_tendsto`: if E(N)<=N^(1+u/2) eventually for
  fixed 0<u<=1/8, the normalized signed sum below ceil(N^(1-u)) tends
  to zero. Cauchy--Schwarz gives squared upper bound
    N^(-u/2)+2*N^(-1+u/2).
  **`density_of_subpower_primeWinnerEnergy`**: the hypothesis
    forall eta>0, eventually E(N)<=N^(1+eta)
  implies the original density-half conjecture. Combine the low-group
  convergence with the O(u^2) high-group bound and let u tend to zero.
  This weakens the earlier sufficient linear-energy hypothesis.

Compilation initially found two local proof errors (wrong-side addition
of a norm inequality, and an overly broad reverse norm_natCast rewrite).
Both were fixed; the final compile succeeds without warnings. All three
printed theorem axiom checks use only propext, Classical.choice, Quot.sound.

Crucial limitation: neither the linear nor the subpower-loss BULK energy
hypothesis is proved. The latter is a sufficient arithmetic target, not
an unconditional bound. Spec.lean is unchanged and unresolved. No completed
proof or disproof has been submitted.

## Follow-up bulk investigation: no additional estimate

Reviewed whether observing a large part in one factorization and the
complementary small factors in the other could reconstruct the orientation
within the low-product CRT budget. This does not certify that the observed
part is the largest in its partition. Excluding unobserved larger parts can
exceed the budget. The already verified PartitionObstruction and
RefinedPartitionObstruction models retain exactly this ambiguity, so this
is not a deduction of joint or comparison symmetry from fixed total mass.
No new signed bulk bound or energy hypothesis was proved.

The subpower-energy criterion above is the latest verified result.
Spec.lean remains unchanged with its original sorry. No complete proof or
disproof is available or submitted.

## Signed-kernel continuation: no bulk cancellation proved

Revisited ReciprocalDiscrepancy, RoughDivisorGroups, BilinearRows,
RoughMobiusHarmonic, and AbsoluteKernelObstruction. Complete least-factor
and complete-row cancellations are already available, but they do not
apply unchanged to the rectangular reciprocal-root truncation. The
one-dimensional rough Mobius harmonic limit does not bound the same
weights twisted by that modular-inverse kernel. Termwise absolute values
are blocked by the verified linear absolute-mass lower bound.

Also reconsidered a rough-core graph/averaged-dilation approach. No
arithmetic independence from residue classes, spectral estimate for the
required graph, or valid natural-endpoint transfer was established.
Excluding high-frequency chirps alone is not such an inverse theorem.
The library search supplied no missing correlation theorem.

No new Lean theorem or signed bulk estimate was proved in this round.
The last verified advance remains density_of_subpower_primeWinnerEnergy,
whose energy hypothesis is unproved. Spec.lean remains unchanged with its
original sorry; no complete proof or disproof has been submitted.

## Verified logarithmic cutoff stability for the signed smooth skew

New file: `Submission/SmoothSkewCutoffStability.lean`, importing
SmoothCutoffSkew and WeightedPrimeHarmonic. It compiles without warnings;
its .olean is saved. All six printed axiom checks list only propext,
Classical.choice, Quot.sound. The temporary CutoffChecks.lean was removed.

Finite bounds:
- FiniteSieve.mediumPrimes_log_sum: the weighted prime mass over (B,C]
  equals primeLogHarmonic(C)-primeLogHarmonic(B).
- FiniteSieve.mediumPrimes_reciprocal_log_bound: for 1<B<=C,
    sum_{B<p<=C} 1/p <= (log C-log B+primeBandLogError)/log B,
  where primeBandLogError=1+log 4+primePowerErrorConstant.
  This follows from the previously verified log-weighted prime harmonic
  bounds, without a prime number theorem.
- smoothIndicator_band_sum_le: the number in a largest-factor band among
  1,...,N is at most N times that reciprocal prime mass.
- **smoothCutoffSkew_change_bound**: for 1<=B<=C and arbitrary D,N,
    |skew(B,D,N)-skew(C,D,N)|
      <=2*N*sum_{B<p<=C}1/p+1.
  Thus the finite bound is uniform in the other smoothness cutoff.

Convergence theorems:
- mediumPrimes_reciprocal_tendsto_zero: if B(N)->infinity, eventually
  B(N)<=C(N), and log C(N)/log B(N)->1, then the band reciprocal mass
  tends to zero, independently of any endpoint relation.
- **smoothCutoffSkew_log_cutoff_stability**: under those hypotheses,
  (skew(B(N),D(N),N)-skew(C(N),D(N),N))/N ->0 for every D(N).
- **smoothCutoffSkew_coalescing_cancellation**: skew(B(N),C(N),N)/N ->0.
- cutoff_atTop_of_positive_log_exponent.
- smoothCutoffSkew_same_exponent_stability: ordered B,C with the same
  positive limiting exponent log cutoff/log N may be interchanged,
  uniformly in the second cutoff.
- smoothCutoffSkew_bounded_multiple_stability: replacing any divergent
  B(N) by K*B(N), for fixed positive K, has negligible normalized effect.

Scope: this is a genuine vanishing estimate for COALESCING cutoffs,
including cutoffs located in the interior power range. It does NOT prove
reciprocity for TWO DISTINCT FIXED positive exponents. Summing the
quantitative modulus over increasingly many cutoff changes across a
fixed exponent interval does not give a vanishing error; the number of
changes cannot be ignored. Consequently the original density problem,
and the subpower prime-winner-energy hypothesis, remain unresolved.
Spec.lean is unchanged with the original sorry. No complete proof or
disproof has been submitted.

## Cutoff-stability versus growing-grid audit

Checked whether the new coalescing-cutoff theorem can be combined directly
with PowerSmoothReciprocity to finish the density proof. It cannot with
the current estimates. For cutoffs N^u and N^(u+delta), the leading
normalized cutoff-change bound is proportional to delta/u. Summing these
bounds over a fixed positive exponent interval gives a constant-sized
bound, not an error tending to zero as the mesh shrinks. This is a failure
of the proposed estimate to prove cancellation, NOT a lower bound on the
actual skew and NOT a disproof of the conjecture.

Also reconsidered the natural-endpoint issue in a dilation approach.
Stability under changing cutoffs is not stability under changing the
averaging endpoint from N to N/p. No theorem removing that distinction,
or a new fixed-interior signed estimate, was proved in this continuation.

The latest verified module remains SmoothSkewCutoffStability.lean.
Spec.lean remains unchanged with the original sorry. No complete proof or
disproof is ready for submission.

## Verified obstruction to every exact prime-winner-preserving pairing

New file: `Submission/PrimeWinnerPairingObstruction.lean`, importing
PrimeWinnerEnergy. Compiles without warnings, .olean saved, and both main
axiom checks use only propext, Classical.choice, Quot.sound. The temporary
CheckGroup.lean has been removed.

- `falling_primeWinner_three_unique`: for ALL natural n, if its prime
  winner is 3 and the comparison falls, then n=3. Proof: P(n)=3 and
  P(n+1)=2. Coprimality forces n=3^b and n+1=2^a. Powers of three are
  1 or 3 modulo 8, so a<=2; hence n=3. This is an unconditional proof,
  not an assertion based on a finite search.
- `no_injective_primeWinner_preserving_sign_reversal`: there is no
  injective f:Nat->Nat which, for every n>1, preserves primeWinner n
  and sends factorSign n to its negative. Both n=2 and n=8 are rises
  with primeWinner=3, so both would have to map to the unique fall 3.
  No requirement that f preserve intervals is imposed.

Precise limitation: this rules out an EXACT GLOBAL pairing preserving
all winner groups. It does not rule out a pairing after discarding a
finite or density-zero exceptional set. It is not a density disproof,
and has not been put into Spec.lean as erdos_371.disproof.
The file does not classify every rising member of group 3.

A preceding finite diagnostic used exact Python enumeration of smooth
integers through 10^8 for small prime bounds up to 31. It did not supply
an asymptotic group-imbalance or energy estimate. Those diagnostic values
are not Lean theorems and no conjecture counterexample was claimed.

The bulk signed estimate remains missing. Spec.lean is unchanged with
its original sorry. No completed proof or disproof has been submitted.

## Interior odd-character continuation: no new cancellation bound

Revisited CommonEndpointPrimeSkew and PrimeBandProgressions and searched
the available library for an applicable shifted-correlation result. No
such result supplying the fixed-interior bound was found. The exact odd
character formula retains its hyperbolic endpoint N/b. Separately bounding
moduli with the existing cofactor energy and a prime-character energy
estimate still incurs the previously identified loss above sqrt(N).
No uniform prime-progression theorem, new dispersion bound, or cancellation
of that hyperbolic sum was proved or assumed.

No new Lean theorem was added this round. The latest verified new module
remains PrimeWinnerPairingObstruction.lean; its obstruction is only to an
exact global pairing and is not a density disproof. Spec.lean is unchanged
with its original sorry. No complete solution has been submitted.

## Prime-average and weighted-reflection follow-up: still unresolved

Re-examined the prime-winner energy route. Squaring a group's signed sum
creates signed off-diagonal correlations of smoothness along kp-1 and
kp+1. Neither the existing multiplicity bound nor prime-label flux
controls those off-diagonal terms with subpower-loss energy. Averaging
labels, or dropping their primality condition for a nonnegative upper
bound, does not by itself give the missing signed cancellation. No
second-moment estimate was proved or assumed.

Also rechecked whether primeReflection could give a weighted pairing after
discarding exceptional inputs. Sign reversal and eventual two-periodicity
of individual orbits do not control the counting weights carried by their
fibers. The verified positive-proportion endpoint overflow is an additional
obstruction to using this map directly on range N. No negligible-exception
or density-preserving transport theorem was established. This says nothing
against a different asymptotic pairing or the density conjecture itself.

No new Lean theorem was added in this follow-up. Spec.lean is unchanged,
including its original conjecture and sorry. A complete proof or disproof
is still unavailable; nothing has been submitted for verification.

## Uniform small-prime averaging of the actual smooth skew

New file `Submission/SmoothSkewPrimeAveraging.lean`, importing
SmoothCutoffSkew and HarmonicCofactorCutoff. The proof uses the existing
primeDivCount_variance_upper; it does not assume a shifted-correlation or
entropy-decrement theorem. All three main printed axiom checks are among
the permitted three.

Definitions:
- primeWeightedSum S a N = sum_{1<=n<=N} omega_S(n)*a(n).
- smallPrimeSkewAverage S B C N is
    sum_{p in S} sum_{1<=m<=N/p}
      [smooth_B(m)*smooth_C(p*m+1)
       - smooth_C(m)*smooth_B(p*m+1)].

Verified:
- primeWeightedSum_error_sq: uniformly for real |a|<=1, with
  H=sum_{p in S}1/p and S consisting of primes,
    (H*sum_{1<=n<=N}a(n)-primeWeightedSum S a N)^2
      <= N*(N*H+2*H*card S).
- primeWeightedSum_error_bound: if card S<=N and N,H>0, the difference
  between the normalized unweighted mean and the H-normalized weighted
  mean has absolute value at most sqrt(3/H).
- sum_positive_multiples and primeWeightedSum_eq_progressions: exact
  reindexing, preserving the individual endpoint floor(N/p).
- smoothIndicator_mul_small: exact invariance under multiplication by a
  positive integer p<=B, at positive arguments.
- smallPrimeSkewAverage_eq_weighted: exact identity for p<=min(B,C).
- **smoothCutoffSkew_prime_average_bound**: normalized smooth skew differs
  from smallPrimeSkewAverage/(N*H) by at most sqrt(3/H).
- **smoothCutoffSkew_prime_average_error_tendsto**: for arbitrary moving
  cutoffs B,C and K->infinity with K<=min(B,C,N) eventually, choosing all
  primes <=K makes that replacement error tend to zero. This is uniform
  in both cutoffs, including distinct fixed interior power exponents.

Precise limitation: the vanishing estimate is for the REPLACEMENT ERROR,
not for the original skew or the remaining small-prime average. Values at
p*m+1 are not identified by small-multiplier invariance, and the endpoints
N/p have not been replaced by N. Neither an inverse theorem nor arithmetic
progression independence was proved. Thus the conjecture remains open in
this work. Spec.lean is unchanged with its original sorry; no complete
proof or disproof has been submitted.

## Verified logarithmic prime averaging and its contraction audit

New file: `Submission/SmoothSkewLogPrimeAveraging.lean`, importing
SmoothSkewPrimeAveraging and WeightedPrimeHarmonic. It compiles without
warnings; its .olean is saved. All three main printed axiom checks are
among propext, Classical.choice, Quot.sound. Temporary LogAverageChecks
files were removed.

Definitions:
- logPrimeAverage a N = sum_{p<=N prime} log(p) * sum_{1<=m<=N/p} a(p*m).
- logPrimeAverageConstant = 1 + primePowerErrorConstant + log(4).
- centeredSmoothSkewPoint B C n =
    smooth_B(n)*(smooth_C(n+1)-smooth_C(n-1)).
- centeredLogPrimeSkew B C N =
    sum_{p<=min(B,N) prime} log(p) * sum_{1<=m<=N/p}
      smooth_B(m)*(smooth_C(p*m+1)-smooth_C(p*m-1)).

Verified one-dimensional estimates:
- squarefreeSmallPrimeLog_le_log: the log of the selected radical is
  bounded by log(n) at positive n.
- squarefreeSmallPrimeLog_sum: its prefix sum is an exact sum of
  floor(N/p)*log(p).
- primeLogSum_upper: Chebyshev's theta <= N*log(4).
- squarefreeSmallPrimeLog_sum_lower and
  squarefree_log_deficit_sum_bound: total deficit from log(N) is at most
  N*logPrimeAverageConstant. Uses previously proved weighted-prime harmonic
  lower bound and floor error, not PNT.
- **logPrimeAverage_error_bound**: uniformly for EVERY real |a|<=1,
    |log(N)*sum_{1<=n<=N} a(n) - logPrimeAverage a N|
      <= N*logPrimeAverageConstant.
  Thus no small-prime cutoff or reciprocal-mass normalization is needed.

Verified application to the actual smooth skew:
- smoothCutoffSkew_centered_boundary: exact endpoint identity; its absolute
  error is at most one.
- centeredLogPrimeSkew_eq_average: exact removal of primes p>B and exact
  small-multiplier invariance at the center.
- **smoothCutoffSkew_log_prime_error**: for N>1,
    |skew(B,C,N)/N - centeredLogPrimeSkew(B,C,N)/(N*log N)|
      <= 1/N + logPrimeAverageConstant/log N.
- **smoothCutoffSkew_log_prime_error_tendsto**: this replacement error
  tends to zero for ARBITRARY moving cutoffs B,C; neither must grow.

Precise limitation and follow-up audit: this is cancellation only of the
replacement error. The centered prime average itself is not proved to
vanish. A proposed contraction based on total log-prime mass below B does
not follow: after extracting a prime p, the new endpoint is N/p while B
is unchanged, and the other values are still at p*m +/- 1. For power
cutoffs, the relative exponent increases as the endpoint contracts.
There is no proved common-endpoint or common-slope supremum estimate to
close a recurrence. Neither signed bulk cancellation nor the sufficient
prime-winner-energy bound was established.

Spec.lean remains unchanged with its original sorry. No complete proof or
disproof has been submitted.

## Centered local-pairing audit and an actual large-prime flow cycle

Investigated whether cancelling the two incident comparisons at local
extrema could be iterated to leave only rare long monotone chains. This
was not established: label-flow cycles can remain, so their circulation
cannot be bounded merely by a monotone-chain count. No signed bulk bound
was obtained from the local pairing.

New small verified module `Submission/PrimeFlowCycle.lean`, importing
PrimeReflection. It compiles without warnings, has a saved .olean, and
both printed axiom checks use only the permitted three.
- large_prime_flow_cycle: P(33)=11, P(34)=17; P(51)=17, P(52)=13;
  P(65)=13, P(66)=11. All three labels have squares greater than 66.
- large_prime_net_flow_cycle: in bilinearCount with endpoint 66, the
  orientations (11,17), (17,13), (13,11) each have count one, and their
  opposite orientations each have count zero. Thus subtracting reverse
  divisibility edges does not remove this directed triangle.

These are kernel-checked FINITE facts about the actual prime ordering.
They do not show a positive density of such cycles, do not rule out an
asymptotic pairing with exceptions, and do not disprove Erdős 371. They
only prevent asserting acyclicity of the remaining large-prime flow.

The last general arithmetic estimate remains logarithmic prime averaging,
whose shifted centered average is still unestimated. Spec.lean remains
unchanged with its original sorry. No complete proof or disproof has been
submitted.

## Fourier continuation: no signed minor-frequency estimate

Investigated expressing the smooth-cutoff skew through the antisymmetric
part of the additive Fourier cross-correlation. The constant-frequency
contribution is symmetric, but this does not control the remaining
frequencies. A Cauchy--Schwarz/Parseval estimate gives only an O(N) bound
for the remaining cross-term. It does not yield the o(N) needed for two
distinct fixed interior power cutoffs.

No uniform cross-phase estimate, shifted-correlation theorem, or valid
major/minor-frequency completion was proved. In particular, one-point
Fourier information would not alone justify cancellation of the entire
cross-term. No new Lean theorem was added in this round, and no Fourier
cancellation hypothesis was assumed.

The newest verified arithmetic modules remain SmoothSkewLogPrimeAveraging
and PrimeFlowCycle. Their precise limitations are recorded above.
Spec.lean remains unchanged with its original sorry. There is still no
complete proof or disproof ready for submission.

## Product-cutoff and complementary-divisor continuation

Revisited the reciprocal-root kernel, the exact complete least-factor
cancellation, and complete-row cancellation. Splitting at a product cutoff
controls the sufficiently small-product counting errors, but complementary
divisors do not remove the signed obstruction above the cutoff. The
complementary summand retains Mobius and least-prime-factor weights tied
to the full factorizations of the two consecutive integers. Ordinary CRT
counts for the smaller complementary products do not establish cancellation
of those weights. Complete-row identities still cannot be applied to the
truncated kernel without accounting for the excluded terms.

No new weighted correlation estimate, Lean theorem, proof, or disproof was
obtained in this continuation. No unproved cancellation lemma was added.
Spec.lean is unchanged and still contains its original sorry. Nothing has
been submitted for verification.

## Upper-half nested-cutoff follow-up: no further estimate

Rechecked the regime in which each integer has at most one prime divisor
above the lower cutoff. The existing UpperHalfSmoothSkew identity already
removes all higher inclusion-exclusion terms exactly. The remaining term
is the signed prime-band discrepancy, equivalently the difference of prime
counts in opposite reciprocal residue classes with endpoint N/b.

Nesting the two smoothness indicators does not supply equidistribution in
those residue classes. The existing odd-character orthogonality and
energy bounds still do not yield o(N) after summing moduli p>sqrt(N).
No stronger signed estimate or new Lean theorem was proved in this round.
Spec.lean is unchanged with its original sorry; no complete solution has
been submitted.

## Uniform harmonic-gap cancellation via the finite Hilbert inequality

New verified module: `Submission/HarmonicGapSkew.lean`, importing
SmoothCutoffSkew. It compiles without warnings, its .olean is saved, and
all three main printed axiom checks use only propext, Classical.choice,
Quot.sound. The temporary HilbertChecks.lean file was removed.

Namespace: Erdos371.HarmonicGap.

Verified analytic ingredients:
- monomial_orthogonality, polynomial_parseval: finite Fourier orthogonality
  and Parseval on [0,1].
- monomial_bernoulli_integral: the Fourier coefficients of B_1(x)=x-1/2,
  available in Mathlib's ZetaValues, realize the signed kernel 1/(j-i).
  The identity includes the diagonal, where division by zero is zero.
- hilbertSum_integral: exact integral realization of the finite double sum.
- **hilbertSum_energy_bound**:
    |sum_{i,j<N} a_i*b_j/(j-i)|
      <= (pi/2)*(sum_{i<N} a_i^2 + sum_{j<N} b_j^2).
  This is an unconditional finite Hilbert inequality, not an assumed
  Fourier minor-frequency estimate.
- **harmonicSkew_bounded**, for |a_i|,|b_i|<=1 on range N:
    |sum_{i<j<N} (a_i*b_j-b_i*a_j)/(j-i)| <= pi*N.
  It retains the signs, improving on the O(N log N) absolute kernel mass.
- smoothHarmonicSkew uses a_i=smoothIndicator B (i+1),
  b_i=smoothIndicator C (i+1).
- smoothHarmonicSkew_bound and smoothHarmonicSkew_normalized_bound:
  normalized absolute value <= pi/log N for N>1.
- **smoothHarmonicSkew_tendsto**: division by N*log N gives limit zero
  uniformly for ARBITRARY moving cutoffs B(N),C(N).

Crucial limitation: this averages over ALL positive gaps j-i, weighted by
1/(j-i). It is NOT the consecutive-integer skew, nor a proof of logarithmic
comparison density. Gap-one cancellation has not been deduced. Generic
bounded sequences can have biased gap-one skew while obeying this Hilbert
inequality, so an arithmetic transfer is necessary. The available dilation
estimates control divisible progressions only, not all residue classes.
No progression-independence or fixed-gap transfer was proved or assumed.

Possible follow-up, NOT yet formalized: the Hilbert bound can be localized
to truncated gaps by splitting into blocks and bounding the cross-boundary
terms. Such a result would still need the same arithmetic transfer to gap
one. No claim is made that localization alone solves the task.

The preceding fixed/growing-prime, moment-determinacy, and endpoint-variation
checks produced no additional arithmetic estimate: the low-product moment
models block the naive reconstruction, and the existing dilation lemmas do
not establish slow variation of natural prefix averages.

Spec.lean remains unchanged with its original sorry. There is still no
complete proof or disproof, and nothing has been submitted for verification.

## Harmonic-gap / divisible-progression transfer audit

Revisited the exact small-multiplier identities and the newly verified
Hilbert inequality. For pairs (n,n+h) with h dividing n and n+h<=N,
write n=h*m. If h<=min(B,C), both smooth indicators remove the multiplier
exactly. With the existing smoothCutoffSkew indexing, the resulting
harmonic contribution at gap h is

    smoothCutoffSkew B C (N/h-1) / h.

The endpoint must stay N/h-1 (natural subtraction). There are at most
N/h such terms, each with weight 1/h. Hence the total available absolute
mass of these divisible pairs is bounded by N*sum_{h>=1} 1/h^2 = O(N),
not N*log H. A hypothetical linear gap-one discrepancy is therefore not
contradicted by the O(N) harmonic Hilbert estimate. Obtaining amplification
would require reweighting the divisible samples and proving that the
result agrees with the unrestricted gap average. No such signed residue
independence estimate was proved.

Also checked the short-prime-interval / entropy approach at the level of
its scales. A common prime interval can make endpoints comparable, but
an unweighted average over a short interval of gaps does not have uniform
signed cancellation for arbitrary bounded observables (low additive
frequencies remain). Conversely, a wide harmonic gap average changes
cofactor endpoints. No entropy-decrement theorem, low-frequency arithmetic
estimate, or natural-density transfer was proved here. Available Mathlib
entropy searches did not supply those theorems.

No new Lean theorem was added in this audit. The latest verified auxiliary
module remains HarmonicGapSkew.lean. Spec.lean and its original statement
are unchanged, its sorry is still present, and no complete proof or
disproof is ready for submission.

## Dyadic iteration: actual cancellation can reappear

Rechecked the exact dyadic sign identity rather than assuming that its
non-between branches stay cancelled under further subdivision. Added and
compiled the small module `Submission/DyadicIterationCheck.lean`, importing
Explore. Its .olean is saved and the printed axiom check uses only
propext, Classical.choice, Quot.sound.

Verified `dyadic_cancellation_can_reappear`:
- factorBetween 2 is false;
- factorSign 4 + factorSign 5 = 0;
- sum_{j<4} factorSign (8+j) = 2.

Indeed P(8),...,P(12) are 2,3,5,11,3, giving signs +,+,+,-.
Thus deleting a non-between parent after its first cancellation does not
preserve the signed sum at the next depth. An iterated bound cannot simply
be replaced by a product of between indicators along surviving branches.
The existing non-between harmonic coboundary theorem remains valid, but
does not control these conditioned descendants.

This is only a finite arithmetic obstruction to that exact pruning step.
It does NOT rule out a more sophisticated asymptotic dyadic argument and
is NOT a disproof of Erdős 371. No bound for the reappearing bulk signed
contribution was proved. Spec.lean remains unchanged with its original
sorry, and no complete proof or disproof has been submitted.

## Exact endpoint smoothing of the reciprocal discrepancy

New module `Submission/EndpointSmoothedDiscrepancy.lean`, importing
ReciprocalDiscrepancy. It compiles without warnings, has a saved .olean,
and all three main printed axiom checks use only propext,
Classical.choice, Quot.sound. Temporary SmoothEndpointChecks was removed.

For coprime a,b>1, put D(k)=bilinearCount k a b-bilinearCount k b a.
Verified:
- **bilinearDiscrepancy_period_sum**:
    sum_{k<a*b} D(k) = adjacentRoot b a - adjacentRoot a b.
  Although D is the primitive of a zero-mean periodic divisibility
  difference, D itself need not have mean zero.
- reciprocalPeriodMean a b = (adjacentRoot b a-adjacentRoot a b)/(a*b).
- reciprocalPeriodMean_abs_le_one.
- bilinearDiscrepancy_periodic.
- **bilinearDiscrepancy_centered_endpoint_bound**:
    |sum_{k<N} D(k)-N*reciprocalPeriodMean a b| <= 2*a*b.
  Thus the normalized centered error is at most 2*a*b/N.
- **bilinearDiscrepancy_endpoint_average_tendsto**: for FIXED a,b,
  the endpoint average tends to reciprocalPeriodMean a b, not necessarily 0.
- reciprocalPeriodMean_five_seven = -6/35, with the CRT roots 20 and 14
  proved by the exact root-uniqueness theorem.

This is an individual-pair smoothing formula, not cancellation of the
actual growing weighted kernel. For a*b comparable to or exceeding the
endpoint, the normalized bound supplies no small error. For smaller
products, the root-dependent mean remains; it has not been proved to
cancel against the Mobius/least-factor weights. Swapping a and b changes
both this mean and the antisymmetric arithmetic weight by a sign, so it
does not cancel their product.

No smoothed o(N) estimate for the full discrepancy, and no Tauberian
completion of the original conjecture, was obtained. Spec.lean is
unchanged with its original sorry. No complete proof or disproof has
been submitted.

## Approximate reflection pairing follow-up

Re-examined the reflection map's displacement and multiplicities, rather
than treating its sign-reversal theorem as a pairing. Its displacement is
on the prime-PRODUCT scale, not just the winning-prime scale. The already
verified primeReflection_boundary_positive_proportion therefore directly
blocks the proposed near-identity interval argument; it cannot be repaired
merely by using that very large individual primes have small density.

A local reflection about the multiple of the winning prime instead moves
to the neighboring comparison. It reverses the sign only when that multiple
is a local maximum of the prime-factor labels. Otherwise the new winner
increases and the sign need not reverse. Following this operation gives
local monotone runs, whose left and right lengths have not been proved
balanced. Bounded run lengths alone would not imply comparison balance.
No estimate for the unmatched mass, no approximately measure-preserving
pairing, and no new arithmetic cancellation theorem were obtained.

No new Lean module was added in this follow-up. The latest verified module
remains EndpointSmoothedDiscrepancy.lean. Spec.lean is unchanged and still
contains its original sorry. No complete proof or disproof is available
for submission.

## Truncated harmonic-gap cancellation at arbitrary growing cutoffs

New module `Submission/TruncatedHarmonicGap.lean`, importing HarmonicGapSkew.
It compiles without warnings, its .olean is saved, and both main printed
axiom checks use only propext, Classical.choice, Quot.sound.

For bounded real a,b, define
  T(a,b,H,N) = sum_{i<j<N, j-i<=H} (a_i*b_j-b_i*a_j)/(j-i).
Verified:
- `mask_hilbert_bound`: positive cross-boundary kernel bounded by pi*H.
- `crossSkew_bound`: absolute cross-boundary signed contribution <=2*pi*H.
- Exact block decomposition and zero-padding identities.
- `truncatedSkew_multiple_bound`: |T(a,b,H,K*H)| <=3*pi*K*H.
- `truncatedSkew_bound`: |T(a,b,H,N)| <=6*pi*N for ALL H,N.
- The same bound for the actual smooth indicators.
- `smoothTruncatedHarmonicSkew_tendsto`: for arbitrary moving B,C,H,
  H tending to infinity implies T(B(N),C(N),H(N),N)/(N*log H(N)) -> 0.

Thus harmonic localization can use an arbitrarily slowly growing gap
cutoff below both smoothness thresholds. This DOES NOT establish fixed-gap
cancellation: restricting to starting points divisible by the gap produces
only O(N) total harmonic mass, not N*log H. The signed progression-to-full-
residue transfer remains unproved. No logarithmic or natural density-half
theorem has been obtained. Spec.lean remains unchanged with its sorry.

## Follow-up on the truncated-gap transfer

Recorded the new truncated harmonic theorem and re-examined its possible
connection to the small-prime and logarithmic-prime averaging identities.
No signed residue-independence or endpoint-stability estimate was obtained.
Dilation identifies the divisible sample with an average at N/p, not the
unrestricted gap-p sample at N. The replacement-error estimates in the
averaging modules do not bound their remaining shifted-prime sums.

Also considered whether bilinear modular-inverse cancellation or a
multiplier-invariant process argument would close this gap. No applicable
uniform estimate was proved; fixed-multiplier invariance alone is already
blocked by the chirp examples, and excluding those examples is not an
inverse theorem. No new arithmetic cancellation result was added.

The reference-page lookup still fails due to unavailable DNS. The sole
import and original conjecture in Spec.lean remain unchanged, including
the original sorry. No valid complete proof or disproof is ready.

## Upper-half cofactor-swap follow-up

Re-examined the prime-only discrepancy with its aligned hyperbolic endpoint
(CommonEndpointPrimeSkew), rather than attempting the harmonic-gap transfer.
For fixed cofactors, swapping the orientation changes a*p-b*q=1 to
b*q-a*p=1. Parametrizing these equations yields prime pairs in reflected
linear forms. There is no exact prime-preserving reflection on the positive
interval, and no aggregate signed estimate over the growing cofactor range
was proved. Bounds for a fixed cofactor pair or for endpoint corrections
alone do not control the sum over all such pairs.

Also revisited whether the low-product factorization moments could bypass
this estimate. The existing partition and stationary-moment obstruction
modules already rule out deducing comparison symmetry from those identities
alone. No new implication using the full arithmetic distribution was proved.
No new theorem has been added in this round. Spec.lean remains unchanged
with its original sorry; no complete proof or disproof is ready.

## Unconditional full prime-winner energy upper bound

New module `Submission/PrimeWinnerBulkUpper.lean`, importing PrimeWinnerFlux.
It compiles without warnings and its .olean is saved. Both main printed
axiom checks use only propext, Classical.choice, Quot.sound.

Verified:
- `primeWinnerSum_norm_sum_le`: sum_p |D_p(N)| <= N.
- `primeWinnerSum_low_norm_sum_le`: sum_{p<=B}|D_p(N)| is at most the
  number Psi(N,B) of B-smooth integers in range N.
- `primeWinnerSum_high_norm_bound`: for p>B,
  |D_p(N)| <= 2*N/(B+1)+1.
- **`primeWinnerEnergy_bulk_upper`**, for all B,N:
    E(N) <= Psi(N,B)^2 + (2*N/(B+1)+1)*N.
- `primeWinnerEnergy_bulk_ratio_upper` gives the corresponding normalized
  bound Psi(N,B)^2/N^2 + 2/(B+1) + 1/N, for N>0.
- **`primeWinnerEnergy_div_sq_tendsto_zero`**: E(N)/N^2 -> 0, choosing the
  already verified subpower cutoff and its smooth-number rarity estimate.

Scope: this is an unconditional subquadratic bound for the WHOLE energy,
not just a boundary range. Its proof uses group sparsity and triangle
inequalities, not cancellation inside a group. It is much weaker than
E(N)<=N^(1+eta) for every eta>0; it does NOT imply the density conjecture
via the existing energy criterion. No near-linear bulk bound was obtained.
Spec.lean remains unchanged with its original sorry. No complete proof or
disproof is ready for submission.

## Rankin bounds and arbitrary logarithmic savings in full energy

New compiled modules, with .olean files saved:
- `Submission/RankinSmoothBound.lean`, importing PrimeHarmonicBounds and
  PrimeWinnerBulkUpper.
- `Submission/PrimeWinnerEnergyLogSavings.lean`, importing RankinSmoothBound.
Both compile without warnings. Main axiom checks use exactly the three
permitted axioms. Temporary RankinChecks.lean was removed.

RankinSmoothBound verifies:
- `natNegRpowHom s`, the completely multiplicative function n^(-s).
- **`smooth_rankin_bound`** for s>0:
    #smoothNumbersUpTo(N,B) <= N^s * prod_{p<B}(1-p^(-s))^(-1).
  Uses Mathlib's finite-prime Euler product and positivity of the series.
- **`smooth_rankin_exp_bound`**, B>=1 and 1/2<=s<=1:
    #smoothNumbersUpTo(N,B)
      <= N^s * exp(4*B^(1-s)*(1+log B)).
  The prime sum is bounded by a full harmonic sum; no PNT is used.
- `smooth_count_rankin_exp_bound` handles the original range-N smooth
  predicate, including n=0, with an extra 1 and prime cutoff B+1.
- `polylogSmoothCutoff k N = floor((log N)^k)`.
- **`smooth_polylog_power_bound`**: for each fixed natural k, there exists
  0<delta<1 such that eventually
    #{n<N:P(n)<=polylogSmoothCutoff k N} <= 1+N^(1-delta).
  The proof chooses delta=1/(8*(k+1)).

PrimeWinnerEnergyLogSavings verifies:
- `log_nat_pow_div_rpow_tendsto_zero`.
- `polylog_smooth_ratio_power_bound` and the floor-cutoff reciprocal bound.
- **`primeWinnerEnergy_log_saving`**: for every fixed natural k,
    (log N)^k * E(N)/N^2 -> 0.
  Choose the group cutoff floor((log N)^(k+1)) in the unconditional
  full-energy bound, apply Rankin to the low groups, and use the reciprocal
  cutoff bound for the high groups.

These are UNSIGNED sparsity improvements, not cancellation inside the
prime groups. Arbitrary fixed logarithmic savings from N^2 still fall far
short of E(N)<=N^(1+eta) for every eta>0. No uniform rate in k is proved,
so choosing k=k(N) to save a full power of N is not justified. This result
does not prove the density conjecture. Spec.lean remains unchanged with
its original sorry, and no complete proof or disproof has been submitted.

## Pell / S-unit group investigation

Investigated whether Størmer-style structure of consecutive p-smooth pairs
could give a signed pairing within a prime-winner group, rather than another
unsigned sparsity estimate. Mathlib has Pell-equation infrastructure but no
applicable uniform signed count of these smooth pairs was found or proved.

The elementary Pell-doubling map n -> 4*n*(n+1), whose successor is
(2*n+1)^2, does not generally reverse the sign, even when it stays in the
same smooth group: 7 maps to 224, and both are falling comparisons with
winning prime 7 (7,8 and 224,225). Thus pairing successive Pell solutions
by sign alternation is not available. Finiteness for each FIXED prime would
also not by itself give a bound uniform over growing prime groups.

A Python calculation enumerated explicitly bounded smooth-number sets
up to 10^10 for primes through 11 to test a candidate pairing. It was NOT
used as a proof of global completeness, a group bound, or a density claim.
No theorem asserting exhaustiveness of those lists has been added. No
new signed estimate or Lean theorem resulted from this investigation.
Spec.lean is unchanged with its original sorry; no solution is ready.

## Full-factor reordered-prime prefix check

New module `Submission/FullRankingPrefixCheck.lean` is compiled with a saved
.olean. Both printed axiom checks use only propext, Classical.choice,
Quot.sound. The rank injectivity proof uses a kernel-checked finite part
and the explicit affine tail; no failed or admitted helper remains.

Unlike the earlier truncated-factor model, label(n) includes ALL prime
factors, ranked in a different injective order. It satisfies
label(a*b)=max(label(a),label(b)) for nonzero a,b. In the comparisons
n=1,...,40, it has 28 rises and 12 falls, while 42.primesBelow has 13
members. Hence discrepancy 16 exceeds all 13 available prime labels.

This rules out deriving a constant-one prime-count prefix bound from
max-under-multiplication and injectivity alone. It does NOT rule out a
bound for the natural prime order, nor a larger-constant bound. The rank
modification affects only finitely many primes and is not a density
counterexample. Spec.lean remains unchanged with its original sorry.

## Full-factorization follow-up

Reviewed whether keeping the complete logarithmic prime-factor partitions,
rather than only their largest parts, bypasses the energy obstruction.
The already verified PartitionObstruction and RefinedPartitionObstruction
models preserve each partition's total mass and all symmetric inclusion
moments within the CRT product budget; largest-part comparisons can still
be biased. These are not models of the complete arithmetic distribution
or of its actual prime-factor marginal law. No additional arithmetic
identity establishing symmetry beyond that budget was proved here.

Also considered smooth-number progression second moments for the winner
groups. Their definitions retain a simultaneous smoothness restriction on
the cofactor and on a neighboring integer; removing that restriction or
bounding a replacement error is not a signed estimate for those groups.
No near-linear bulk energy bound was obtained. The only new verified file
in this continuation is FullRankingPrefixCheck.lean. The original
conjecture remains unresolved and has not been submitted as proved.

## Weighted reflection boundary obstruction

New module `Submission/WeightedPrimeReflectionBoundary.lean`, importing
PrimeReflectionBoundary, compiles without warnings and has a saved .olean.
The two main axiom checks use only propext, Classical.choice, Quot.sound.

For weights w on range N, define
  escapeMass(N,w) = sum_{n<N, primeReflection(n)>=N} w(n),
  weightError(N,w) = sum_{n<N} |w(n)-1|.
Verified:
- **reflectionEscapeMass_lower**: the unweighted boundary count is at
  most escapeMass + weightError. This even permits signed weights.
- **reflectionEscapeMass_eventually_positive**: if weightError/N tends
  to zero, then escapeMass/N is eventually at least 1/20000.
- **no_uniform_weights_with_negligible_reflection_escape**: no weight
  family makes both normalized quantities tend to zero.
- For nonnegative weights supported in range N, exact stationarity under
  primeReflection forces w(n)=0 at every escaping input.
- **stationary_reflection_weight_error_lower**: all such stationary
  weights have weightError/N at least 1/10000 eventually. No assumption
  about their total mass is needed.

This extends the earlier unweighted boundary obstruction to all L1-small
reweightings of that specific reflection. It does NOT exclude a different
pairing, signed cancellation among boundary terms, or weights whose L1
change is macroscopic but whose signed correction is separately controlled.
No estimate of that signed correction was obtained. Thus this is a rigorous
limitation on a proof strategy, not a proof or disproof of Erdős 371.
Spec.lean and its import remain unchanged, including the original sorry.
No complete solution has been submitted.

## Cofactor-character and bounded smooth-pair follow-up

Revisited the exact opposite-residue character formula with a view toward
character cancellation in the cofactor variable. Its cofactor second moment
is already exactly phi(p)*A/2 when 2*A<p. Even a prime-character energy of
diagonal order leaves a per-modulus square-root estimate whose absolute sum
above sqrt(N) is too large. A bound for individual short character sums does
not establish the needed signed cancellation across moduli, nor remove the
hyperbolic endpoint N/b. No new character estimate was proved or assumed.

A separate Python structural check enumerated the 114831 integers <=10^12
with all prime factors among 2,3,5,7,11,13, then checked which successors were
also in that finite set. For winner primes 2,3,5,7,11,13 the observed pair
counts were 1,3,6,13,17,28 and signed totals 1,1,0,1,3,4. This is only a
BOUNDED enumeration. It is not a proof that these lists include every
consecutive smooth pair, a global group bound, or an asymptotic assertion.
It supplied no sign-alternating pairing or new cancellation estimate.

No Lean theorem was added in this follow-up. Spec.lean remains unchanged
with its original sorry. There is still no complete proof or disproof to
submit; the latest new verified module is WeightedPrimeReflectionBoundary.

## Direct-reference and signed-kernel follow-up

A single direct-IP DNS-over-HTTPS attempt also timed out, so the external
reference remains unavailable even without relying on the local resolver.
The local /opt documentation contains Lean/Pantograph tooling, not an
additional arithmetic result relevant to the conjecture. Further network
retries are not warranted in this environment.

Re-examined the exact rectangular Mobius/least-factor kernel. Complementing
large divisors introduces the parity factor (-1)^(omega(n)+omega(n+1)) and
does not turn the remaining weighted progression correlations into counts
that CRT alone evaluates. No cancellation of those correlations was proved.
Likewise, symmetrizing small-prime divisor averaging at n and n+1 leaves
opposite-residue shifted sums, not a telescoping sum over consecutive
arguments. No new estimate for the signed kernel was obtained or assumed.

No auxiliary obstruction theorem was added in this continuation. Spec.lean
is unchanged with its original sorry; no complete proof or disproof exists
in the project for submission.

## Signed-flow contraction follow-up

Checked the winner/loser conservation identity and the dyadic/log-prime
averaging identities specifically for a contraction of a SIGNED norm.
No such contraction was obtained. Winner/loser conservation permits signed
circulations (the actual finite prime-flow cycle is already verified).
Its absolute-value consequence controls the top power band but not the
interior. The dyadic identity does not allow permanently pruning a
cancelled branch, as DyadicIterationCheck already demonstrates. The
log-prime identity bounds its replacement error, not the remaining sum.

Also audited the Lean source tree for admissions: the only occurrence of
`sorry` or `admit`, or a declaration beginning with `axiom`, is the original
`sorry` in Spec.lean. This audit is not a proof of the target; the main
arithmetic cancellation remains unproved. No new auxiliary theorem was
added in this follow-up, and nothing has been submitted as a solution.

## Reciprocal-kernel and multiplicative-transfer review

Rechecked BalancedKernel, ReciprocalDiscrepancy, AbsoluteKernelObstruction,
PrimeWinnerSubpowerEnergy, and the smooth-cutoff/prime-averaging reductions.
The reciprocal-root formula is exact, but its two antisymmetries do not
cancel the weighted sum: swapping the arguments changes BOTH the weight
and the discrepancy, so their product is symmetric. Taking termwise
absolute values is already ruled out by the verified linear lower bound.
No signed bilinear or prime-character bound was obtained in this review.

Also reconsidered transferring the harmonic-gap bound using exact
invariance of smooth indicators under small multipliers. Simultaneous
scaling of both arguments samples a divisible residue class and changes
the endpoint to N/p. Neither exact multiplier invariance nor the existing
one-dimensional prime-divisor averaging estimate supplies the missing
full-residue transfer. No uniform inverse theorem or endpoint-stability
claim has been proved or assumed.

A local search of the imported number-theory library found no applicable
shifted-smooth-number asymptotic or largest-prime comparison theorem.
No new Lean module or mathematical estimate resulted from this review.
Spec.lean remains unchanged with its original sorry. The conjecture is
still unresolved in this project; no complete solution has been submitted.

## Exact cofactor-descent preimages

New module `Submission/CofactorDescentPreimage.lean` compiles and has a saved
.olean. All four printed theorem axiom checks use only propext,
Classical.choice, and Quot.sound; no failed or admitted helper remains.

Verified forward identities, including outside the large-product region:
- Rising n, with p=P(n), q=P(n+1), b=(n+1)/q:
    T(n)=b*(q mod p)-1,  n/(p*b)=q/p.
- Falling n, with p=P(n+1), q=P(n), b=n/q:
    T(n)=b*(q mod p),    n/(p*b)=q/p.

Verified inverse constructions for 0<r<p, k>0, q=r+p*k prime, and b<p:
- Rising construction: 1<b, p divides b*r-1,
    n=b*q-1, a=(b*r-1)/p+b*k.
  Then P(n)=p iff P(a)<=p. Under that smoothness condition,
  P(n+1)=q, n is rising, T(n)=b*r-1, the large-product condition
  holds, and n/(p*b)=k.
- Falling construction: 0<b, p divides b*r+1,
    n=b*q, a=(b*r+1)/p+b*k.
  Then P(n+1)=p iff P(a)<=p. Under that smoothness condition,
  P(n)=q, n is falling, T(n)=b*r, the large-product condition
  holds, and n/(p*b)=k.

These are algebraic identities and inverse constructions, NOT an asymptotic
count or a cancellation theorem. Counting the inverse parameters retains a
prime linear form r+p*k together with a smooth linear form a0+b*k. Dropping
that latter condition changes the arithmetic count; no estimate proving
cancellation of the signed preimage weights was obtained. Thus the descent
map has not supplied a contraction or a density-preserving pairing.

Spec.lean remains unchanged with its original sorry. The original density
conjecture is unresolved in this project, and no solution has been submitted.

## Joint-residue transfer follow-up

Reviewed whether exact invariance of smooth indicators under small prime
multipliers could establish independence of the JOINT adjacent observable
from residue classes. No such estimate was obtained. One-dimensional
smooth-number distribution in residue classes, even if available uniformly,
would not by itself establish the corresponding two-coordinate claim.

Rechecked the short-prime-interval variant at the level of its parameters:
comparable multipliers make N/p comparable, but do not identify the resulting
joint averages with the one at the prescribed natural endpoint. A short gap
average also needs control of low additive frequencies. Neither that joint
transfer nor an endpoint-stability estimate was proved in this follow-up.

No new Lean module or asymptotic estimate resulted. The latest new verified
module remains CofactorDescentPreimage.lean. Spec.lean remains unchanged
with its original sorry; no complete proof or disproof is ready to submit.

## Prime-tower energy review

Revisited prime-winner energy via the decomposition of a p-smooth integer
into its p-power part and its part with smaller prime factors. For positive
integers, the new p-layer can be expressed by divisibility by p together
with p-smoothness of the quotient. This leads back to sums involving

    1_{P(m)<=p} * (1_{P(p*m-1)<=p} - 1_{P(p*m+1)<=p}),

with endpoint corrections. No orthogonality or sign-definite recurrence for
these sums was proved. Squaring still introduces opposite-shift, off-diagonal
smoothness correlations; the existing unsigned group bounds and winner/loser
flux identity do not estimate them at the needed near-linear scale.

This review did not produce a new Lean theorem or an asymptotic estimate.
Spec.lean and its original statement remain unchanged, including the sorry.
There is still no complete proof or disproof to submit.

## Additive-score distributional follow-up

Reviewed AdditiveLogScores and its uniform approximation theorem as a
possible route through additive-function limit laws. The existing theorem
correctly requires cancellation for arbitrarily large fixed score indices;
it does not supply that cancellation. A limit theorem for counts of small
prime factors does not automatically apply to scores dominated by large
logarithmic prime factors. No applicable distributional theorem or valid
interpolation in the score index was found or proved.

The already verified index-zero identity is important: that score equals
log n and its comparison rises at every positive n. It is therefore not a
balanced base case from which sign cancellation can simply be continued to
larger indices. The multiplicative phase representation also leaves its
imaginary autocorrelation mean unevaluated.

No new Lean theorem resulted from this follow-up. Spec.lean still has the
original sorry, with its import and conjecture statement unchanged. No
complete proof or disproof has been obtained or submitted.

## Affine prime-extraction recurrence review

Investigated enlarging the centered logarithmic-prime averaging problem to
pairs of affine linear forms with determinant +/-1. Extracting a prime from
one form on its divisible residue class preserves that determinant, so the
algebraic class can accommodate the changing slopes. Reflection-compatible
pairs of opposite offsets also preserve the intended signed orientation.

This did NOT yield a contraction estimate. Successive residue restrictions
shorten the parameter interval and increase a slope. No uniform o(N) bound
for the accumulated short-progression remainder was established. The
existing two-linear-form sieve is an upper-bound sieve, not a signed
asymptotic that controls this remainder. Merely enlarging the supremum class
does not justify iterating away the missing estimate.

No new conditional theorem or Lean module was added. Spec.lean remains
unchanged with its original sorry. No complete proof or disproof has been
obtained or submitted.

## Reference-access and utility-source check

Checked the environment for an overlooked reference source. No HTTP/HTTPS/
ALL proxy is configured, and no local paper cache was found under /workspace
or /opt. No additional network request was made. The installed utility
`Data/Nat/MaxPrimeFac.lean` contains elementary prime-factor lemmas, not the
needed asymptotic; `NumberTheory/SmoothScale.lean` only defines scaleL.
No applicable comparison-density theorem was located in those sources.

This supplied no new mathematical estimate. Spec.lean remains unchanged
with its original sorry. No complete proof or disproof is available for
submission.

## Local-maximum deletion / longer-gap review

Considered converting the gap-one comparison sum into longer-gap sums by
successively deleting local maxima. The two incident signs at a strict
maximum cancel, but reconnecting its neighbors introduces a new comparison.
Thus the original signed sum is not invariant under the deletion. Iteration
selects gaps according to intervening prime-factor labels; these are not the
unrestricted reciprocal-gap sums estimated by the Hilbert inequality.

No estimate transferring this selected, arithmetic-weighted collection of
comparisons to the existing harmonic-gap bound was obtained. The earlier
finite flow-cycle and dyadic-pruning checks remain limitations on simpler
cancellation arguments, not disproofs of the conjecture.

No new theorem was added. Spec.lean remains unchanged with its original
sorry. No complete proof or disproof has been obtained or submitted.

## Exponential-smoothing / Abel-mean review

Considered replacing the sharp endpoint by exponential weights. For a fixed
coprime pair a,b>1, the elementary geometric-series expression for the
weighted divisibility difference is

    (exp(-t*r)-exp(-t*s))/(1-exp(-t*a*b)),

where r,s are its two reciprocal roots and t>0. This retains the dependence
on those roots. The existing verified endpoint-period mean is consistent
with its fixed-modulus limit; no cancellation of the growing weighted
modulus sum follows merely from replacing the cutoff.

No required Abel-mean estimate, and hence no Tauberian completion of the
natural-density claim, was established. No new Lean theorem was added for
this review. Spec.lean remains unchanged with the original sorry. There is
still no complete proof or disproof to submit.

## Exact energy increments and bounded computational diagnostic

New module `Submission/PrimeWinnerEnergyIncrement.lean` compiles and has a
saved .olean. Its three printed main axiom checks use only propext,
Classical.choice, and Quot.sound. It contains no admitted helper.

Verified:
- primeWinnerSum_succ and vanishing outside the label set;
- primeWinnerEnergy_succ:
    E(N+1)=E(N)+1+2*factorSign(N)*D_{winner(N)}(N);
- primeWinnerCrossSum(N)=sum_{n<N} factorSign(n)*D_{winner(n)}(n);
- primeWinnerEnergy_eq_diagonal_add_cross:
    E(N)=N+2*primeWinnerCrossSum(N);
- primeWinnerCrossSum_pair_formula: the cross sum runs over m<n with
  matching winner labels, weighted by the product of their signs;
- primeWinnerEnergy_le_diagonal_iff:
    E(N)<=N iff primeWinnerCrossSum(N)<=0.

The nonpositivity on the right is NOT proved. The identities expose the
unproved signed inequality; they do not establish a linear energy bound.

A targeted Python sieve/update diagnostic checked every prefix N<=10^6
for the stronger finite candidate E(N)<=N and found no violation. The
reported values E(10),E(100),...,E(10^6) were
    4, 14, 140, 1814, 19530, 191312.
At N=10^6 the signed comparison count was 298 and the largest absolute
prime-group imbalance was 32 (at p=5039). These are computational results,
NOT Lean-verified finite theorems and NOT an asymptotic proof.

A second diagnostic separated adjacent same-winner pairs (local peaks)
from the other cross terms. At N=10^6 there were 335916 such peaks and the
nonadjacent signed-pair total was -68428. No positive nonadjacent total
was found in that bounded run. No general nonpositivity claim is assumed,
and no theorem extrapolating from this computation has been added.

Spec.lean remains unchanged with its original sorry. No complete proof or
disproof has been obtained or submitted.

## Verified adjacent / nonadjacent energy separation

New module `Submission/PrimeWinnerNonadjacent.lean` compiles without warnings
and has a saved .olean. All four printed axiom checks use only propext,
Classical.choice, and Quot.sound.

Definitions:
- A(N)=adjacentWinnerCount(N), the number of n<N with 0<n and
  winner(n-1)=winner(n).
- R(N)=primeWinnerNonadjacentCrossSum(N), the signed sum over m+1<n<N
  with matching winner labels.

Verified:
- same_adjacent_winner_sign_product: adjacent comparisons with matching
  winners have sign product -1;
- primeWinnerCrossSum_adjacent_split: crossSum(N)=R(N)-A(N);
- primeWinnerEnergy_nonadjacent_formula: E(N)=N-2*A(N)+2*R(N);
- primeWinnerEnergy_le_diagonal_iff_nonadjacent:
    E(N)<=N iff R(N)<=A(N).

The one-sided inequality R(N)<=A(N) is NOT proved. The earlier diagnostic
observed the stronger R(N)<=0 only on its finite tested range. No universal
nonpositivity claim, injection pairing nonadjacent terms, or contraction
bound was obtained. These identities isolate the required inequality but
do not establish it and do not settle Erdős 371.

Spec.lean remains unchanged with its original sorry. No complete proof or
disproof has been obtained or submitted.

## Multiplication and cross-scale reflection follow-up

Reviewed the latest energy decomposition against the exact small-multiplier
identity and the existing obstruction examples. The identity on divisible
starting points still changes the adjacent-average endpoint from N to N/p.
No common-endpoint transfer or uniform entropy estimate was proved. The
moving chirp model is not a counterexample for smooth indicators, but fixed-
multiplier invariance alone is already insufficient; polynomial-range
invariance has not been turned into the needed correlation estimate.

Also considered a signed recurrence between scales using primeReflection.
The orbit theorem preserves the winner and eventually reaches a two-cycle,
but it does not identify the pushforward of counting measure. Counting its
preimages retains arithmetic smoothness restrictions. Neither a controlled
signed boundary term nor a contraction on natural averages was obtained.
The existing cofactor-descent inverse formulas likewise retain simultaneous
primality and smoothness of linear forms.

No new theorem or asymptotic bound resulted from this follow-up. In
particular, the inequality primeWinnerNonadjacentCrossSum N <=
adjacentWinnerCount N remains unproved. Spec.lean retains its original
import, conjecture statement, and sorry. No proof or disproof has been
submitted.

## Polynomial multiplier range and reciprocal-operator review

Checked ChirpFiniteDifferences and the smooth-prime averaging identities.
The existing no_uniform_power_multiplier_invariance theorem already excludes
the moving chirps on every fixed positive-power multiplier range. Smooth
cutoffs have exact invariance on their permitted range. These facts do not
by themselves give a natural-endpoint correlation theorem, and none was
proved in this continuation.

Considered treating the reciprocal discrepancies as a signed matrix rather
than summing their absolute values. Complete-period cancellation and the
individual bound do not provide the required operator estimate over growing
moduli. A short-cofactor change of variables leaves simultaneous conditions
on the two linear forms; no uniform signed estimate for that range was
obtained. No new spectral or arithmetic inequality is being assumed.

No new Lean theorem, complete proof, or disproof resulted. The candidate
nonadjacent energy bound remains unproved. Spec.lean is unchanged with its
original sorry, and no completed solution has been submitted.

## Verified energy bound with logarithmically growing cofactors

New module `Submission/PrimeWinnerGrowingCofactor.lean` compiles without
warnings and has a saved .olean. Its three printed main axiom checks use
only propext, Classical.choice, and Quot.sound.

New unconditional results:
- `primeWinnerEnergyAbove_top_ratio_bound`: if N>1, 0<=u<=1/8,
  N^(1-u)<=B, and N<=K*(B+1), then

    E_above(B,N)/N <= (2*K+1) *
      (largePairConstant*(u+1/log N)^2 + 2^65*N^(-1/2) + 1/N).

  This combines the winner/loser flux inequality with the finite uniform
  two-large-prime sieve estimate. The parameter u may depend on N.
- `div_cutoff_ge_power_of_mul_le_rpow`: an explicit floor-division cutoff
  bound when K<=N and 2*K<=N^u.
- `logarithmicCofactorCutoff N = floor(log N)`, tending to infinity.
- `logarithmicCofactorExponent N = log(2*log N)/log N`, tending to zero,
  with verified eventual positivity, upper bound 1/8, and cutoff inequality.
- `primeWinnerEnergyAbove_logarithmic_cofactor_tendsto`:

    E_above(N/floor(log N),N)/N -> 0.

  The proof majorizes the normalized energy eventually by

    3*largePairConstant*(log(2*log N)+1)^2/log N
      + 3*2^65*log N/N^(1/2) + 3*log N/N,

  each term tending to zero. This is a genuine extension of the previous
  fixed-cofactor energy theorem to an explicitly growing cofactor range.

Limit: the cutoff still has exponent tending to one. No near-linear energy
bound for the complementary groups p<=N/floor(log N), no nonadjacent
cross-term inequality, and no fixed-interior signed cancellation have been
proved. This result does not settle Erdős 371.

Spec.lean remains unchanged with its original sorry. No complete proof or
disproof has been obtained or submitted.

## Verified subquadratic logarithmic-power cofactor range

New module `Submission/PrimeWinnerLogPowerCofactor.lean` compiles without
warnings and has a saved .olean. Its three printed main axiom checks use
only propext, Classical.choice, and Quot.sound.

Definitions:
- logPowerCofactorCutoff a N = floor((log N)^a).
- logPowerCofactorExponent a N = log(2*(log N)^a)/log N.

Verified:
- The cofactor cutoff tends to infinity for a>0.
- The exponent tends to zero for every fixed real a.
- For a>=0, the positivity and finite cutoff hypotheses needed by the
  uniform two-large-prime energy bound hold eventually.
- affine_log_square_div_rpow_tendsto_zero, an elementary limit used with
  exponent 2-a>0.
- primeWinnerEnergyAbove_logPower_cofactor_tendsto:

    for every 0<=a<2,
    E_above(N/floor((log N)^a),N)/N -> 0.

The eventual majorant has main term

    3*largePairConstant*(log 2+a*log(log N)+1)^2/(log N)^(2-a),

and errors 3*2^65*(log N)^a/N^(1/2) and 3*(log N)^a/N.
All three terms tend to zero under the stated hypotheses. The proof uses
the finite uniform estimate, not an unjustified substitution into a
fixed-parameter eventual theorem.

Limit: all these cutoffs still have exponent tending to one. This supplies
no near-linear energy estimate for a fixed interior prime-power band, and
it cannot be iterated to cover those bands from the statements proved here.
The original density conjecture remains unresolved.

Spec.lean retains the original import, statement, and sorry. No complete
proof or disproof has been obtained or submitted.

## Attempted propagation from the new boundary energy range

Reviewed whether the logarithmic-power cofactor estimate could be bootstrapped
to fixed-interior prime groups using winner/loser conservation or descent.
No propagation inequality was obtained. The flux identity preserves the signed
group imbalance; bounding its loser side absolutely becomes too weak as the
cutoff is lowered. Descent changes both the index and winner label, but its
preimage formulas retain simultaneous prime and smooth linear-form conditions.
Their multiplicities have not been controlled by a contractive signed estimate.

The full-energy logarithmic savings also do not bridge this gap: they remain
at a quadratic scale. No uniform choice of a growing logarithmic exponent was
justified, and the fixed a<2 boundary theorem was not extrapolated to a growing
a or to prime cutoffs of fixed exponent below one.

No new Lean theorem or estimate resulted from this propagation review. The
latest verified arithmetic result remains primeWinnerEnergyAbove_logPower_
cofactor_tendsto. Spec.lean is unchanged with its original sorry. No complete
proof or disproof has been obtained or submitted.

## Verified uniform two-sided prime averaging

New module `Submission/DoublePrimeAveraging.lean` compiles without warnings
and has a saved .olean. All five printed main axiom checks use only propext,
Classical.choice, and Quot.sound.

For H=sum_{p in S}1/p and omega_S(n)=primeDivCount S n, define

    W_S(a,N)=sum_{1<=n<=N} omega_S(n)*omega_S(n+1)*a(n).

Verified uniformly for |a(n)|<=1, S consisting of primes, card(S)<=N, N>0:
- doublePrimeWeightedSum_error_bound:
    |H^2*sum a(n)-W_S(a,N)| <= 6*N*H+6*N*H*sqrt(H).
- doublePrimeWeightedSum_normalized_error_bound, when H>0:
    |sum a(n)/N-W_S(a,N)/(N*H^2)| <= 6/H+6/sqrt(H).
- doublePrimeWeightedSum_error_tendsto for arbitrary endpoint-dependent
  bounded observables and prime cutoffs K(N)->infinity with K(N)<=N.

The bounds use only the existing one-dimensional variance estimate for the
two shifted prime-divisor counts. They do not assert independence of the
observable from the joint prime-factor process.

Also verified:
- exact divisibility and progression formulas for W_S;
- smoothIndicator_div_small;
- twoSidedPrimeSkewAverage_eq_weighted;
- twoSidedPrimeSkewAverage_cofactor_formula:
    sum over p,q in S, 1<=m<=N/p, 1<=k<=(N+1)/q, p*m+1=q*k,
    of smooth_B(m)*smooth_C(k)-smooth_C(m)*smooth_B(k);
- smoothCutoffSkew_twoSided_prime_error_tendsto: applying the two-sided
  weighting to the actual moving smooth-cutoff skew has vanishing error.

LIMIT: neither the weighted average nor its determinant-one cofactor form
has been proved to cancel. Swapping (p,m) with (q,k) changes the determinant
orientation to minus one, so it does not pair terms within the original sum.
The hyperbolic endpoints have been retained, not silently replaced. No
uniform estimate comparing the two orientations was obtained.

This is an unconditional replacement-error estimate and exact arithmetic
formula, not a settlement of the original density conjecture. Spec.lean
is unchanged with its original sorry. No complete proof or disproof has
been obtained or submitted.

## Two-sided averaging / Cauchy--Schwarz transfer review

Examined the cross terms obtained from the new two-sided prime average.
For permitted small multipliers, the values at p*m+1 and q*m+1 can be
rewritten at p*q*m+q and p*q*m+p. This gives gap q-p, but only along a
selected progression modulo p*q. It does not give the unrestricted
starting-point sum in the verified harmonic-gap Hilbert inequality.
Moreover, squaring an average introduces same-function correlations,
not just the antisymmetric wedge sum controlled by that inequality.

No bound replacing those selected progression correlations by full gap
averages, and no direct estimate of the resulting bilinear operator, was
obtained. The uniform two-sided replacement error remains valid; it is
not being treated as cancellation of the remaining cofactor sum.

No new Lean theorem or signed asymptotic estimate resulted from this
follow-up. Spec.lean remains unchanged with its original sorry. No
complete proof or disproof has been obtained or submitted.

## Support-weighted logarithmic extraction follow-up

Rechecked whether the smooth support makes logarithmic prime extraction a
contractive recurrence. The center being B-smooth correctly removes primes
above B, but the extracted sum still has endpoint N/p and shifted arguments
p*m+/-1. Repeating extraction changes the relative exponent of B and increases
the slope. The initial ratio log B/log N is not a uniform contraction factor
along these branches. No estimate controlling the terminal short-progression
sums was proved.

No new Lean theorem, bulk cancellation estimate, proof, or disproof resulted.
The latest verified module remains DoublePrimeAveraging.lean. Spec.lean is
unchanged with its original sorry; no completed solution has been submitted.

## Smallest-losing-prime reflection: structure, compression, and obstruction

Three new modules compile without warnings, with saved .olean files:
- SmallPrimeReflection.lean
- SmallPrimeReflectionDensity.lean
- SmallPrimeReflectionMultiplicity.lean
All printed main axiom checks use only propext, Classical.choice, Quot.sound.

Definitions:
- losingNumber n = n on a rise and n+1 on a fall.
- leastLosingPrime n = minFac(losingNumber n).
- smallPrimeReflection n = a*q-1-n%(a*q), where a is the least losing
  prime and q is the prime winner.

Verified structure for every n>1:
- 1 < smallPrimeReflection n < leastLosingPrime n * primeWinner n;
- sign reversal and preservation of primeWinner;
- the original least losing prime divides the reflected losing integer;
- leastLosingPrime(smallPrimeReflection n) <= leastLosingPrime n;
- the map is not injective (2 and 8 already collide).
The generic divisorReflection_eq_root and divisorReflection_structure
lemmas handle arbitrary prescribed adjacent prime divisors.

New unconditional density bounds:
- For every fixed natural K,
    #{n<N: n>1 and N<K*primeWinner n}/N -> 0.
  A finite bound is 2*K*pi(N+1), obtained by cofactor injection.
- For every fixed real epsilon>0,
    #{n<N: epsilon*N <= smallPrimeReflection n}/N -> 0.
  The finite bound splits the exceptional set into n<=1, rough losing
  integers, and winners >N/K. Fixed coprime densities give tightness of
  the least losing prime. This is genuine density compression, not merely
  absence of interval escape.

The multiplicity review proves a stronger obstruction for THIS map:
- For arbitrary endpoint-dependent S(N) subset range N and any fixed C,
  if all fibers of the reflection restricted to S(N) have size <=C, then
    card(S(N))/N -> 0.
- In particular, every injective restriction has density zero, so deleting
  a density-zero exceptional set cannot repair it into an injective pairing.
- There is no uniform finite bound on the map's fiber sizes.

Thus the smallest-factor map removes the earlier reflection's positive-density
escape problem, but cannot pair a positive-density subset of the original
interval with bounded multiplicity. These results do not establish cancellation
of the original signed count or control the bulk prime-winner energy.

Spec.lean remains unchanged with its original sorry. No complete proof or
disproof of Erdős 371 has been obtained or submitted.

## Dilation-operator transfer review and critical cofactor improvement

Revisited a possible averaged operator approach using exact invariance of
smooth indicators under permitted multipliers. The selected progression
sum at gap p becomes an adjacent sum at endpoint N/p. Neither of the two
missing transfers was proved:
- from divisibility-selected progressions to unrestricted starting points;
- from the varying natural endpoints N/p back to the endpoint N.
The harmonic-gap inequality and prime-divisor variance bounds are not being
used as if they supplied either transfer. No cancellation theorem resulted
from this review.

A separate quantitative improvement is now verified in
Submission/PrimeWinnerCriticalCofactor.lean (saved .olean, no warnings).
All four printed main axiom checks use only propext, Classical.choice,
Quot.sound.

Definitions:
  criticalCofactorWeight r N =
    (log N)^2 / (1+log(log N))^r
  criticalCofactorCutoff r N = floor(criticalCofactorWeight r N).

Verified:
- one_add_log_rpow_div_rpow_tendsto_zero for r>=0 and s>0;
- criticalCofactor_data: eventually log N<=weight<=(log N)^2,
  the cutoff is positive, and it is <=floor((log N)^2);
- criticalCofactorCutoff_tendsto_atTop;
- criticalCofactorWeight_dominates_logPower: for every r>=0, a<2,
  and fixed real M, eventually M*(log N)^a <= criticalCofactorWeight r N;
- corresponding eventual domination of the earlier integer cofactor cutoffs;
- primeWinnerEnergyAbove_critical_cofactor_tendsto: for every r>2,

    E_above(N/criticalCofactorCutoff r N,N)/N -> 0.

The proof uses the finite uniform energy estimate with exponent
log(2*(log N)^2)/log N. The smaller cutoff weight is retained in the
multiplicative factor rather than replaced by (log N)^2 there. The
main eventual majorant is

  3*largePairConstant*(log 2+3)^2/(1+log(log N))^(r-2),

plus 3*2^65*(log N)^2/sqrt(N) and 3*(log N)^2/N.
All terms tend to zero. No substitution of a growing parameter into a
fixed-parameter asymptotic theorem is used.

LIMIT: this remains an exponent-one boundary range. No bound on the
complementary interior prime-winner energy, or on the full signed count,
has been proved. Spec.lean remains unchanged with its original sorry.
There is no complete proof or disproof to submit.

## Complete low-product-moment recovery review

Checked whether the full hierarchy of CRT-accessible inclusion moments,
together with the fixed logarithmic mass on each integer, could recover
symmetry of the comparison by a largest-part/complement induction.
The existing PartitionObstruction.lean already rules out that implication:
it has fixed mass, equal marginals, disjoint paired supports, no largest-part
ties, symmetry of EVERY inclusion moment within the full one-integer mass
budget, and a biased largest-part comparison. RefinedPartitionObstruction
also retains arbitrary tail-type conditioning. Thus this review did not
supply a valid recovery theorem. The stronger actual arithmetic information
about primes, residues, and divisor products above the endpoint remains
necessary; it was not inferred from the finite models.

Revisited the reciprocal-root formula as the remaining arithmetic problem.
Root reflection exchanges orientations, but the antisymmetric arithmetic
weight also changes sign, so it does not cancel the weighted sum. Neither
a signed estimate for that growing kernel nor an interior energy bound was
obtained. No new Lean theorem resulted from this review.

Spec.lean is unchanged and still contains its original sorry. No complete
proof or disproof has been obtained or submitted.

## Weighted cofactor sieve and improved critical energy range

The analytic-phase review did not produce a starting interval of cancellation
in the phase parameter. Telescoping handles the linear term; higher odd
terms remain mixed correlations. Analyticity was not used to extend a zero
at a single point to an interval.

Five NEW verified modules, all compiled without warnings and with .olean files:
- WeightedCofactorPairs.lean
- PrimeLoserWeighted.lean
- PrimeLoserWeightedBound.lean
- PrimeWinnerWeightedEnergy.lean
- PrimeWinnerWeightedCritical.lean
Every printed main axiom check uses only propext, Classical.choice, Quot.sound.

1. Weighted cofactor sieve
   weightedSlopeSum_bound proves

     sum_{a,b<=X} max(a,b)*slopeSieveFactor(a*b)/(a*b)
       <= 2*exp(16)*X*(1+log X).

   It combines the existing weighted and unweighted second moments of the
   singular slope factor. Consequently cofactorWeightedPrimePairCount_bound
   gives the finite bound

     sum_{a,b<=X} max(a,b)*card(cofactorPrimePairSet N a b z)
       <= 8*exp(19)*N*X*(1+log X)/log(z+1)^2
          + 2*X^3*(z+1)^64,

   provided z>=1 and X^2<=N. This saves one log X compared with replacing
   max(a,b) by X before summing.

2. Actual weighted loser counts
   largestPrimeCofactor n = max(n/P(n),(n+1)/P(n+1)).
   loserMultiplicityWeight N n = 2*N/primeLoser(n)+1 (real division).
   weightedLoserCount B N sums this weight over n<N with both P(n),P(n+1)>B.

   bothAbove_weighted_cofactor_le embeds the actual cofactor fibers in the
   corresponding cofactorPrimePairSets, without claiming uniqueness for
   arbitrary prescribed prime cofactors.

   weightedLoserCount_halving proves, for B>=1, z<=B, N>=2,

     T(B,N) <= 3*T(B,floor(N/2))
               + 7*cofactorWeightedPrimePairCount N floor(N/(B+1)) z.

   On the late half, N/min(P(n),P(n+1)) <= 3*largestPrimeCofactor n.
   The early half is bounded by three times the smaller-endpoint weight.

3. Iterated finite bound
   Strong induction, using 3*(N/2)^2 <= 3*N^2/4 and the cubic analogue,
   proves weightedLoserCount_bound:

     T(B,N) <=
       224*exp(19)*N^2*(1+log X)/((B+1)*log(z+1)^2)
       + 28*N^3*(z+1)^64/(B+1)^3,

   whenever B>=1, 1<=z<=B, N<=X*(B+1), and N<=(B+1)^2.
   The sieve level z remains fixed throughout the induction.

4. Connection to the actual prime-winner energy
   primeWinnerEnergyAbove_le_weightedLoserCount proves

     E_above(B,N) <= T(B,N)+(2*X+1)

   whenever N<=X*(B+1). It uses the exact winner/loser flux and sums the
   endpoint correction only once, rather than once per prime.
   primeWinnerEnergyAbove_weighted_bound combines this with the finite bound.

5. Uniform power-sieve estimate and new asymptotic
   Define weightedEnergyConstant = 224*exp(19)*256^2.
   For N>1, sqrt(N)<=B, and N<=X*(B+1), the verified finite estimate is

     E_above(B,N)/N <=
       weightedEnergyConstant*X*(1+log X)/(log N)^2
       + 28*2^64*X^3/N^(3/4) + (2*X+1)/N.

   The sieve level is floor(N^(1/256)).

   primeWinnerEnergyAbove_weighted_critical_tendsto improves the previous
   critical cofactor theorem: for EVERY FIXED r>1 (previously r>2),

     E_above(N/criticalCofactorCutoff r N,N)/N -> 0,

   where criticalCofactorCutoff r N is floor((log N)^2/(1+log log N)^r).
   The new main majorant is

     2*weightedEnergyConstant/(1+log log N)^(r-1),

   and errors are bounded by 28*2^64*(log N)^6/N^(3/4) and
   3*(log N)^2/N. All terms tend to zero. The proof is uniform at the
   finite-estimate stage and does not substitute a growing parameter into
   a fixed-parameter asymptotic theorem.

LIMIT: the cutoff still has exponent tending to one. This supplies no
near-linear bound for the full energy and no cancellation theorem for the
fixed-interior prime range. The original density conjecture is unresolved.
Spec.lean is unchanged with its original sorry; no complete proof or
negation has been submitted.

## Weighted-energy interior propagation review

Checked the new weighted bound against the sufficient full-energy criteria
and the exact adjacent/nonadjacent decomposition. For a fixed positive
cofactor exponent u, substituting X approximately N^u into its main
normalized bound gives a quantity of order N^u/log N, not a quantity
tending to zero. Thus the logarithmic gain does not alone produce a
near-linear full-energy estimate or a contraction through interior bands.

The winner/loser flux preserves the same signed imbalance. Replacing its
loser side by the new nonnegative weighted count improves the boundary
bound but still does not estimate the signed nonadjacent cross term in
E(N)=N-2*adjacentWinnerCount(N)+2*primeWinnerNonadjacentCrossSum(N).
No proof of R(N)<=adjacentWinnerCount(N), or of a weaker sufficient
subpower full-energy bound, was obtained. The finite large-prime net-flow
cycle also prevents invoking acyclicity of the actual prime-label flow.

No new Lean theorem resulted from this review. The latest arithmetic
result remains primeWinnerEnergyAbove_weighted_critical_tendsto (r>1).
Spec.lean is unchanged with its original sorry; no complete proof or
disproof is ready for submission.

## Divisor-cycle product bound and prime-loser collision reduction

Three new modules compile without warnings and have saved .olean files.
All printed main axiom checks use only propext, Classical.choice, Quot.sound.

1. DivisorCycleBound.lean (imports FormalConjecturesUtil)
   - prod_succ_sub_prod_mono: the increment prod(n_i+1)-prod(n_i)
     is coordinatewise monotone for natural entries.
   - divisor_cycle_product_bound: for a nonempty finite permutation sigma,
     positive n_i<=N, p_i|n_i, and p_(sigma i)|n_i+1,
       prod p_i <= (N+1)^k-N^k <= k*(N+1)^(k-1).
     No primality or distinctness assumption is needed.
   - This excludes sufficiently short cycles in a high-label range, but
     DOES NOT control long cycles or establish signed comparison balance.

2. PrimeLoserCollisions.lean (imports PrimeLoserWeighted)
   - unordered_divisor_pair_unique: if coprime p,q have p*q>=2N, at most
     one n<N realizes either orientation p|n,q|n+1 or q|n,p|n+1.
   - large_primeLabel_pair_injective: if B>=1 and 2N<=(B+1)^2, the map
     n -> (primeLoser n, primeWinner n) is injective on bothAboveSet B N.
   - primeLoserIncidences p N = {n<N:primeLoser n=p}.
   - primeLoserCollisions B N = ordered distinct pairs n,m in bothAboveSet
     B N with primeLoser n=primeLoser m.
   - primeLoserCollisions_distinct_winners: in the above size range,
     an off-diagonal collision has distinct winning prime labels. Thus
     its common loser and its two winners are three distinct primes.

3. PrimeLoserCollisionEnergy.lean (imports PrimeLoserCollisions)
   - Generic squared-fiber count <= same-label pair count.
   - Generic same-label pair count = diagonal + off-diagonal count.
   - sum_primeLoserIncidences_sq_le:
       sum_{p in labels,p>B} degree(p)^2
          <= card(bothAboveSet B N)+card(primeLoserCollisions B N).
   - primeWinnerEnergyAbove_le_collisions:
       E_above(B,N) <= 2*card(bothAboveSet B N)
                       +2*card(primeLoserCollisions B N)+2.
     The endpoint contribution is paid once. No bound on the collision
     count is assumed or proved here.

CURRENT NEW INVESTIGATION (not yet a theorem): count off-diagonal loser
incidences directly with a dimension-three prime sieve, rather than
multiplying the first moment by its maximum degree. A collision with
common loser p and winners q,r has
    k*p+epsilon=a*q, l*p+delta=b*r,
with signs epsilon,delta in {-1,1} and k,l,a,b<=X when p>N/X.
For distinct incidences the two neighbor linear forms are nonproportional.
All three local roots are distinct at primes >2X^2. The divisibility
conditions restrict p to at most one residue modulo lcm(a,b).
Heuristic finite sieve main term after summing slopes is
    N*X*polylog(X)/(log N)^3,
which could extend the proved boundary cofactor range from log-power <2
to log-power <3. THIS ESTIMATE HAS NOT BEEN PROVED YET. It would still
not address a fixed interior prime-power band or settle the conjecture.
A possible next step is an AP version of the existing product-cutoff
Selberg sieve, retaining the density 1/M of one enforced residue modulo M.

Spec.lean is unchanged with its original sorry; no completed proof or
disproof is ready or has been submitted.

## Progression Selberg sieve and three local roots

Three additional verified modules, all with saved .olean files and only
the permitted axioms in their printed checks:

- ProgressionSelberg.lean (imports TwoLinearSelberg)
  - selbergMass_reciprocal_le_product retains the Euler product rather
    than replacing every local factor by an exponential.
  - residue_selberg_progression_bound: for an enforced class n%M=r,
    coprime sieving moduli S, and local logarithmic mass <=log(Z)/2,
      count <= (2N/M)*exp(-sum card(R_p)/p)+2*M^8*Z^4.
    It inserts modulus M with forbidden set range(M) minus {r} and uses
    product cutoff M^2*Z. The proof treats M=1 separately. The local
    factor for M is exactly 1/M; it is not replaced by exp(-1).

- ThreeResidueProgressionSieve.lean (imports ProgressionSelberg)
  - upperSievingPrimes D z = primes D<p<=z.
  - lower reciprocal mass H(z)-H(D), valid even if z<D.
  - exp(-3H(z)) <= exp(3)/log(z+1)^3.
  - threeResidue_progression_sieve_bound: if D>=3, z>=1,
    0<M<=D, r<M, and card(R_p)=3 for D<p<=z,
      count <= 2*exp(3)*exp(3H(D))*N/(M*log(z+1)^3)
               +2*M^8*(z+1)^96.
    Uses Z=(z+1)^24 and the elementary weighted prime harmonic bound.

- ThreePrimeLocalRoots.lean (imports ThreeResidueProgressionSieve)
  - integerLinearResidues p k e = {r<p : (p:Int)|(k:Int)*r+e}.
    It has one element when p is prime and p does not divide k.
  - threePrimeResidues p k l e d = {0} union the two signed roots.
    If |e|=|d|=1, p does not divide k*l, and
      0<natAbs(l*e-k*d)<p,
    its cardinality is three. Covers both signs without natural subtraction.
  - mod_mem_threePrimeResidues identifies avoidance with nondivisibility
    of n, k*n+e, and l*n+d.

NEXT: connect an actual triple-prime pattern
  k*p+e=a*q, l*p+d=b*r
with primes p,q,r>z to one progression modulo lcm(a,b), apply the new
sieve, then sum cofactor/slopes. None of those remaining steps, nor the
proposed log-power-3 cofactor energy theorem, has yet been proved.
Spec.lean remains unchanged and unresolved.

## Verified three-prime-pattern sieve

New module ThreePrimePatternSieve.lean imports ThreePrimeLocalRoots,
compiles without warnings, and has a saved .olean. Both printed checks
use only propext, Classical.choice, Quot.sound.

- signed_neighbor_coprime and signed_neighbor_modEq: from
    k*p+e=a*q, |e|=1,
  obtain gcd(a,k)=1; two solutions have p congruent modulo a.
- threePrimePatternSet T k l a b z e d consists of primes p<T, p>z,
  admitting primes q,r>z with k*p+e=a*q and l*p+d=b*r.
- threePrimePatternSet_progression: if nonempty and a,b>0, all such p
  lie in one residue modulo lcm(a,b).
- signed_neighbor_determinant_bound: |l*e-k*d|<=2X for k,l<=X.
- threePrimePatternSet_sieve_bound: for 1<=k,l,a,b<=X, z>=1,
  |e|=|d|=1 and l*e-k*d nonzero, with D=3+2X^2,
    card <= 2*exp(3)*exp(3H(D))*T/(lcm(a,b)*log(z+1)^3)
            +2*lcm(a,b)^8*(z+1)^96.
  All small local degeneracies are removed by sieving only at D<p<=z.
  No primality equidistribution assumption is used.

STILL TO DO for the proposed log-power-3 energy improvement:
1. Encode actual loser collisions by k,l,a,b and two signs and verify
   that their determinant is nonzero (distinct comparisons).
2. Bound the cardinality of each fixed-data fiber by this pattern count,
   with endpoint T=N/max(k,l)+1.
3. Sum 1/lcm(a,b) <= harmonic(X)^3 and sum 1/max(k,l) <=2X.
4. Control exp(3H(3+2X^2)) by a fixed power of log(X+constant), using
   the existing elementary double-log upper Mertens bound.
5. Choose z=floor(N^(1/1024)) and X=logPowerCofactorCutoff a N, a<3.
None of these remaining steps is assumed. Spec.lean remains unchanged
and unresolved.

## Actual collision coordinates, cofactor sums, and uniform collision bound

Three further modules compile without warnings, with saved .olean files.
All printed main checks use only the three permitted axioms.

1. PrimeLoserCollisionPatterns.lean (imports PrimeLoserCollisionEnergy and
   ThreePrimePatternSieve)
   - loserIncidenceCofactor, winnerIncidenceCofactor, incidenceShift (+/-1).
   - Exact equations, with k=loser cofactor, a=winner cofactor, p=loser,
     q=winner, e=shift:
       k*p+e=a*q,  2*n+1=2*k*p+e  (integer arithmetic).
   - Cofactors lie in Icc 1 (N/(B+1)) on bothAboveSet B N for B>=1.
   - primeLoserCollisions_det_ne_zero: for distinct comparisons with the
     same loser, l*e-k*d is nonzero. This does NOT require the high-label
     pair-injectivity size restriction; it follows from reconstruction.
   - primeLoserCollisionFiber fixes k,l,a,b,e,d.
   - Its map to the common prime loser is injective.
   - primeLoserCollisionFiber_card_le_pattern embeds it into
       threePrimePatternSet (N/max(k,l)+1) k l a b z e d,
     provided z<=B and B>=1.

2. CofactorTripleSummation.lean (imports ThreePrimePatternSieve)
   - sum_reciprocal_lcm_le_harmonic_cube:
       sum_{a,b<=X} 1/lcm(a,b) <= harmonic(X)^3.
     Proof: inject (a,b) into (gcd(a,b),a/gcd,b/gcd), all in [1,X];
     lcm is the product of these three coordinates. No divisor-sum
     estimate or analytic number theory is needed.
   - sum_reciprocal_max_le:
       sum_{k,l<=X} 1/max(k,l) <= 2X.

3. PrimeLoserCollisionBound.lean (imports the preceding two)
   - The actual collision-coordinate map lies in the cofactor/sign box.
     An exact fiberwise cardinal sum is verified.
   - Empty fibers are handled before invoking the nonzero determinant
     condition; no determinant condition is silently assumed for all
     tuples in the summation box.
   - primeLoserCollisionFiber_simple_bound retains 1/max(k,l) and
     1/lcm(a,b), and bounds the sieve error by 2*X^16*(z+1)^96.
   - MAIN FINITE THEOREM primeLoserCollisions_sieve_bound:
     if B>=1, 1<=z<=B, N/(B+1)<=X<=N, D=3+2X^2, then
       card(primeLoserCollisions B N) <=
         32*exp(3)*exp(3H(D))*N*X*harmonic(X)^3/log(z+1)^3
           +8*X^20*(z+1)^96.
     It is uniform in all four parameters. This is a genuine count of
     off-diagonal actual incidences, not maximum-degree times first moment.

NEXT: control exp(3H(3+2X^2)) by a fixed power of log(X+constant), choose
z=floor(N^(1/1024)), and prove collisionCount/N ->0 for X=floor(log(N)^a),
a<3. Combine with the already proved bothAbove count and collision-energy
reduction. The finite bound is now complete, but these asymptotic steps
have NOT yet been formalized. Even their completion only gives an
exponent-one boundary energy estimate, not the full conjecture.
Spec.lean remains unchanged with its original sorry. No submission.

## Completed subcubic logarithmic cofactor energy theorem

Three new verified modules, all saved as .olean, compiled without warnings.
All main printed axiom checks use only propext, Classical.choice, Quot.sound.

- PrimeHarmonicLogEnvelope.lean (imports PrimeLoserCollisionBound)
  * nat_log_two_le_two_log_add_one: Nat.log 2 n <= 2*log(n+1).
  * primeHarmonic_real_log_envelope:
      H(D) <= 48+24*log(1+log(D+1)).
  * exp_three_primeHarmonic_real_log_bound:
      exp(3H(D)) <= exp(144)*(1+log(D+1))^72.
  * collision_primeHarmonic_weight_bound, X>=1:
      exp(3H(3+2X^2))*harmonic(X)^3
        <= exp(144)*6^72*(1+log X)^75.
  These coarse constants are uniform and elementary.

- PrimeLoserCollisionPowerSieve.lean (imports PrimeHarmonicLogEnvelope)
  * collisionLogConstant =32*exp(3)*exp(144)*6^72.
  * collisionPowerConstant =collisionLogConstant*1024^3.
  * primeLoserCollisions_power_sieve_ratio, N>1, 1<=X<=N,
    N/(B+1)<=X and sqrt(N)<=B:
      collisionCount(B,N)/N <=
        collisionPowerConstant*X*(1+log X)^75/(log N)^3
          +8*2^96*X^20/N^(1/2).
    Uses sieve level floor(N^(1/1024)); its error power 3/32 is enlarged
    to 1/2 for convenience.

- PrimeWinnerSubcubicLogCofactor.lean (imports the preceding module and
  PrimeWinnerCriticalCofactor)
  * logPowerCofactor_collision_data: eventual positivity, K<=N,
    N/(N/K+1)<=K, and sqrt(N)<=floor(N/K), for K=floor(log(N)^a), a>=0.
  * logPowerCofactor_collision_main_bound bounds the finite main factor by
      (a+1)^75*(1+log log N)^75/(log N)^(3-a).
  * primeLoserCollisions_logPower_tendsto, for EVERY fixed 0<=a<3:
      collisionCount(N/logPowerCofactorCutoff a N,N)/N ->0.
  * bothAbove_logPower_tendsto, for EVERY fixed a>=0:
      card(bothAboveSet (N/logPowerCofactorCutoff a N) N)/N ->0.
    Uses the uniform top-band pair sieve with exponent u_N->0, not a
    growing substitution into a fixed-parameter limit.
  * MAIN RESULT primeWinnerEnergyAbove_subcubic_logPower_tendsto:
      E_above(N/logPowerCofactorCutoff a N,N)/N ->0
    for every fixed 0<=a<3. This improves the earlier log-power <2 range.
    Proof combines the collision second moment with the actual first
    moment and the single endpoint correction.

IMPORTANT LIMIT: this still only controls primes above N/(log N)^a,
whose exponent tends to one. It does not give a near-linear bound on the
full prime-winner energy, does not control a fixed interior power band,
and does not settle the density conjecture. No unproved cancellation
hypothesis has been inserted into Spec.lean.

Technical note: avoid `ring` on the final comparison of the asymptotic
majorants with both (a+1)^75 and (1+log log N)^75. It expands thousands
of monomials and can run for minutes using gigabytes of memory. The
verified proof uses only [mul_div_assoc,mul_assoc] there. New temporary
Check*.lean files and DebugSubcubic.lean have been removed.

Spec.lean retains its original statement, import, and sorry (same SHA256).
No completed proof or disproof has been submitted.

## Polynomial-multiplier transfer revisited; actual interior collision obstruction

Rechecked whether exact invariance under all multipliers up to a fixed
positive power of the endpoint supplies the missing natural-average
transfer. It still only identifies divisibility-selected progressions
and changes their endpoints. No unrestricted progression transfer,
strong-stationarity theorem, entropy-decrement estimate, or signed
cancellation was obtained. The earlier polynomial chirp exclusions are
not being treated as if they proved such a theorem.

Instead, proved an obstruction to extending the NEW unsigned collision
method to a fixed interior prime range. This uses the ACTUAL maxPrimeFac
sequence, not a reordered-prime or abstract stationary model.

Three new modules compile without warnings and have saved .olean files;
all printed main checks use only propext, Classical.choice, Quot.sound.

1. TwoBandLargePrimeLower.lean (imports LargePrimeDensityLower)
   - largePrimeSet_reciprocal_split gives the exact split at a second
     integer cutoff.
   - largePrimeDivisorSet_ratio_ge_reciprocal retains the reciprocal sum
     before applying a weighted-log lower bound.
   - largePrimeDivisorSet_two_band_lower combines the two band estimates.
   - ceilPowerCutoff v N = ceil(N^v), with verified log bounds,
     log(cutoff)/log N ->v, and order/square-size data.
   - largePrimeDivisorSet_two_power_bands_eventually_ge: for fixed
     1/2<v<=w<=1 and epsilon>0, eventually
       count(largePrimeDivisorSet ceil(N^v) N)/N
         >= (w-v)/w+(1-w)-epsilon.
     This improves the old one-band bound 1-v. It uses only the existing
     elementary primeLogHarmonic estimates; no prime number theorem.

2. BothLargePrimeLower.lean (imports TwoBandLargePrimeLower,
   PositiveComparison, and PrimeWinnerFlux)
   - largePrimeDivisorSet_eq_maxPrimeFac_filter, for B>=1.
   - Finite union/shift inequality:
       2*card(largePrimeDivisorSet B N)
         <= card(bothAboveSet B N)+N+1.
   - bothAbove_upperHalf_positive_proportion:
       eventually card(bothAboveSet ceil(N^(21/40)) N)/N >=1/20.
     Use v=21/40, w=3/4; two-band marginal lower is 11/20 before
     errors, or 27/50 after choosing epsilon=1/100.
   - ceilPowerCutoff_upperHalf_product_eventually:
       eventually 2N<=(ceil(N^(21/40))+1)^2.

3. PrimeLoserCollisionGrowth.lean (imports BothLargePrimeLower and
   PrimeLoserCollisionPatterns)
   - bothAbove_card_sq_le_labels_mul_collisions: with B>=1,
       M^2 <= L*(M+Q),
     where M=card(bothAboveSet B N), L=card(primeWinnerLabels N), and
     Q=card(primeLoserCollisions B N). This is Cauchy--Schwarz in the
     reverse direction from the earlier upper-bound application.
   - bothAbove_ratio_sq_le_labels_ratio:
       (M/N)^2 <= (L/N)*(1+Q/N), N>0.
   - General theorem primeLoserCollisions_ratio_tendsto_atTop_of_positive_mass:
     whenever B(N)>=1 eventually and M/N>=c>0 eventually, Q/N ->+infinity,
     since L/N ->0.
   - MAIN ACTUAL OBSTRUCTION:
       primeLoserCollisions_upperHalf_ratio_tendsto_atTop:
       card(primeLoserCollisions ceil(N^(21/40)) N)/N ->+infinity.
   - no_linear_upperHalf_unsigned_collision_bound negates the existence
     of any eventual bound Q(N)<=C*N in this range.
   - upperHalf_collisions_distinct_winners_eventually: every collision
     still has different winner primes. The superlinear growth does not
     come from repeated occurrences of one unordered prime pair.

LIMIT: This negates only an UNSIGNED auxiliary bound, not the original
conjecture or any signed energy bound. It shows that a proof through
interior energy must retain cancellation between signs of off-diagonal
incidences. The conjecture in Spec.lean is unchanged and remains admitted;
no complete proof or disproof is ready or has been submitted.

## Exact signed collision identity and polynomial unsigned obstruction

Three new substantive modules compile without warnings and have saved .olean
files. All printed main theorem axioms use only propext, Classical.choice,
and Quot.sound. No original-target proof or disproof was obtained.

1. PrimeLoserSignedCollisions.lean
   - Defines primeLoserEnergyAbove, primeLoserSignedCollisions,
     primeLoserOppositeCollisions, and primeLoserEndpointCorrection.
   - weighted_fiber_square_sum is a general exact weighted-fiber identity.
   - primeLoserEnergyAbove_signed_formula, for ALL B,N:
       loserEnergyAbove(B,N) = M(B,N) + signedCollisions(B,N),
     with M=card(bothAboveSet), and ordered off-diagonal collisions.
   - primeLoserSignedCollisions_eq_card_sub_twice_opposite:
       signedCollisions = Q-2*Qopp.
   - primeWinnerEnergyAbove_eq_loser_add_endpoint and
     primeWinnerEnergyAbove_signed_collision_formula:
       winnerEnergyAbove = M+Q-2*Qopp+endpointCorrection.
     The endpoint is exactly
       if B<P(N) then 2*primeLoserSum(P(N),N)+1 else 0.
     These identities include B=0 and small N; no extra primality assumption
     or discarded low label is hidden in them.
   - primeLoserEndpointCorrection_bound:
       abs(endpointCorrection) <= 4*N/(B+1)+5.
   - primeLoserEndpointCorrection_ratio_tendsto: the correction divided by
     N tends to zero for any cutoff B(N)->infinity.
   - primeWinnerEnergyAbove_le_iff_signed_collisions is an exact finite
     criterion retaining the endpoint, not an asserted estimate.
   - primeLoserSignedCollisions_lower: signedCollisions >= -M, by positivity
     of the loser energy. Hence 2*Qopp<=Q+M unconditionally. It provides NO
     upper bound for signedCollisions, which is what the energy approach needs.

2. PrimeLoserCollisionCancellation.lean
   - collision_energy_balance_error: for N,Q>0,
       abs(Eabove/Q + 2*Qopp/Q - 1) <= 10*N/Q.
   - collision_energy_balance_tendsto: if Q/N->infinity then
       Eabove/Q + 2*Qopp/Q ->1.
   - collision_half_iff_energy_small_relative_to_collisions:
       Qopp/Q->1/2 iff Eabove/Q->0.
     IMPORTANT: this is E=o(Q), NOT the stronger E=O(N). In a superlinear
     collision range, merely proving asymptotically half of the collisions
     have opposite signs would not by itself give a linear energy bound.
   - collision_half_of_linear_energy, and concrete specialization
     upperHalf_collision_half_of_linear_energy, prove a NECESSARY conditional
     consequence of the still-unproved linear high-label energy hypothesis.

3. PrimeLoserCollisionPowerGrowth.lean
   - primeLoserBandSet B C N restricts bothAboveSet B N to loser labels <=C.
   - Its mass plus card(bothAboveSet C N) equals card(bothAboveSet B N), B<=C.
   - primeLoserBandSet_card_sq_bound:
       bandMass^2 <= (C+1)*(N+Q(B,N)).
     Uses at most C+1 labels, not the larger primeWinnerLabels set.
   - primeLoserCollisions_power_growth_of_band_mass: if bandMass>=c*N,
     c>0, and C(N)+1<=K*N^(1-u), K,u>0, eventually, then
       Q(B(N),N) >= N^(1+u/2) eventually.
   - upperHalf_positive_band_mass_exists: there exists 0<u<=1/8 with
       bandMass(ceil(N^(21/40)), ceil(N^(1-u)), N) >= N/40
     eventually, and the upper label cutoff plus one <=3*N^(1-u).
     Choose u=min(1/8,1/(160*(largePairConstant+1))), retain the earlier
     lower mass N/20, and subtract the top-band sieve bound <=N/80.
   - MAIN actual obstruction primeLoserCollisions_upperHalf_polynomial_growth:
       exists delta>0, eventually
         Q(ceil(N^(21/40)),N) >= N^(1+delta).
     This strengthens the earlier Q/N->infinity to fixed polynomial growth.
     It still concerns UNSIGNED collisions, not a density disproof or a
     counterexample to a signed energy estimate.

Review of the signed sieve possibility did not supply a valid replacement
of prime indicators by majorants in signed sums. Entrywise majorization
is not monotone for squared signed sums; the existing three-prime-pattern
sieve remains an unsigned upper bound. No signed interior estimate, inverse
correlation theorem, or natural-average residue transfer was proved.

Spec.lean is unchanged with its original import, statement, and sorry.
No completed solution has been submitted.

## Prime-weighted energy and a weaker relative cancellation criterion

Five new substantive modules (849 lines total) compile without warnings and
have saved .olean files. All printed main axiom checks use only propext,
Classical.choice, Quot.sound. No completed original proof or disproof exists.
The temporary CheckPrimeWeight.lean was removed.

The distinction from the preceding unweighted obstruction is important:
relative half-cancellation of UNWEIGHTED collisions only gave E=o(Q), which
was too weak for the earlier near-linear criterion. Weighting a collision by
its common loser prime instead produces a total mass of order N^2, and
ordinary relative cancellation at this weighted scale IS a sufficient
criterion. Its needed lower bound remains unproved.

1. PrimeWinnerPrimeWeightedEnergy.lean
   - primeWinnerPrimeWeightedEnergy N = sum_p p*(primeWinnerSum p N)^2.
     Denote this W(N). This is different from the earlier module named
     PrimeWinnerWeightedEnergy, which bounded the unweighted E via cofactor
     weights; use the full new name to avoid confusing the two.
   - primeWinnerL1 N = sum_p abs(primeWinnerSum p N).
   - For N>0: W(N)<=3*N*primeWinnerL1(N).
   - primeWinnerL1Above_sq_le_primeWeightedEnergy: weighted Cauchy--Schwarz
     bounds the squared high-label L1 mass by W times sum_{p>B}1/p.
   - high_primeWinnerLabels_reciprocal_bound: for u>0, N>=4, and
     B=ceil(N^u), this reciprocal sum is <=2/u. Uses the already proved
     elementary primeLogHarmonic upper bound.
   - W(N)/N^2->0 implies L1 above ceil(N^u), divided by N, tends to zero
     for every fixed u>0.
   - The low labels are bounded by the existing smooth_count_ratio_log_bound.
   - MAIN equivalence primeWeightedEnergy_tendsto_iff_primeWinnerL1:
       W(N)/N^2->0 iff primeWinnerL1(N)/N->0.
   - density_of_primeWeightedEnergy proves the ORIGINAL conjecture
     CONDITIONALLY on W(N)/N^2->0. No such limit is asserted unconditionally.

2. PrimeLoserPrimeWeightedCollisions.lean
   - Definitions:
       primeLoserPrimeWeightedCollisions N
         = sum_{(n,m) in primeLoserCollisions 0 N}
             primeLoser(n)*factorSign(n)*factorSign(m).
       primeLoserPrimeWeightedDiagonal N
         = sum_{n in bothAboveSet 0 N} primeLoser(n).
       primeLoserPrimeWeightedEndpoint N
         = P(N)*primeLoserEndpointCorrection(0,N).
   - label_weighted_fiber_square_sum is an exact general finite identity.
   - primeWinnerPrimeWeightedEnergy_collision_formula, for ALL N:
       W = weightedDiagonal + weightedSignedCollisions + weightedEndpoint.
   - abs(weightedEndpoint)<=9*N, so weightedEndpoint/N^2->0 unconditionally.
   - primeWinner_sum_div_sq_tendsto_zero proves
       sum_{n<N} primeWinner(n)/N^2->0,
     using the earlier fixed-cofactor large-winner sparsity and a cutoff N/K.
     Thus weightedDiagonal/N^2->0 unconditionally as well.
   - MAIN equivalence primeWeightedEnergy_tendsto_iff_weightedSignedCollisions:
       W/N^2->0 iff weightedSignedCollisions/N^2->0.
   - density_of_primeWeightedSignedCollisions is the corresponding
     CONDITIONAL original-target theorem.

3. PrimeLoserWeightedCollisionMass.lean
   - primeLoserWeightedCollisionMass N (Qw) sums primeLoser(n) over all
     ordered loser collisions at B=0.
   - primeLoserWeightedOppositeMass N (Ow) sums that same weight over
     opposite-sign collisions.
   - Exact identity: weightedSignedCollisions=Qw-2*Ow.
   - primeLoserIncidences_card_le_twice_div: for p>0, incidence degree
     d_p<=2*floor(N/p), with NO +1. A positive loser excludes n=0.
   - Hence p*d_p<=2*N, and the exact unsigned weighted second moment gives
       Qw<=2*N^2
     for every N. No signed cancellation is used here.
   - bothAbove_card_sq_le_weighted_second_moment uses weighted
     Cauchy--Schwarz in the opposite direction.
   - MAIN unconditional lower bound primeLoserWeightedCollisionMass_eventually_lower:
       Qw >= N^2/3200 eventually.
     This uses the earlier mass >=N/20 above ceil(N^(21/40)), the reciprocal
     label bound <=4, and the negligible weighted diagonal.
   - Thus the actual weighted collision mass is Theta(N^2), unlike the
     unweighted mass's polynomial superlinearity relative to N.

4. PrimeLoserWeightedRelativeCancellation.lean
   - primeLoserWeightedOppositeRatio N = Ow/Qw (Lean's zero-division
     convention is harmless; the lower bound gives Qw>0 eventually).
   - weighted_collision_relative_eventually_bounds:
       abs((Qw-2Ow)/N^2) <= 2*abs(1-2*Ow/Qw),
       abs(1-2*Ow/Qw) <= 3200*abs((Qw-2Ow)/N^2), eventually.
   - MAIN equivalence primeWeightedEnergy_tendsto_iff_weighted_opposite_half:
       W/N^2->0 iff Ow/Qw->1/2.
     NO convergence rate in this latter relative limit is required.
   - density_of_primeWeightedOppositeCollision_half is the corresponding
     sufficient theorem for the original conjecture.
   - Unconditional primeLoserWeightedOppositeRatio_eventually_upper:
       for every epsilon>0, eventually Ow/Qw<=1/2+epsilon.
     This is only positivity of the weighted loser energy plus the
     negligible diagonal, NOT the missing half-cancellation estimate.
   - density_of_weightedOpposite_liminf: the reverse one-sided condition
       for every epsilon>0, eventually Ow/Qw>=1/2-epsilon
     would suffice for the ORIGINAL target. This remains unproved.

5. PrimeWeightedEnergyFromSubpower.lean
   - primeWeightedEnergy_le_low_energy_add_high_l1:
       W<=B*E+3*N*primeWinnerL1Above(B,N), N>0.
   - primeWeightedEnergy_power_split, under E<=N^(1+u/2), 0<u<=1/8:
       W/N^2 <=2*N^(-u/2)+3*primeWinnerL1Above(ceil(N^(1-u)),N)/N.
   - primeWeightedEnergy_tendsto_of_subpower_energy formally proves that
     the earlier sufficient hypothesis E<=N^(1+eta) eventually for EVERY
     eta>0 implies W/N^2->0. The new criterion does not require such a
     near-linear unweighted-energy rate.

Remaining mathematical issue: prove the lower relative bound for Ow/Qw, or
another genuine signed estimate. The positivity, degree bounds, and unsigned
sieves only prove the opposite one-sided bound. Reconsidering signed prime
progressions, Fourier/large-sieve bounds, and winner/loser flow did not give
this estimate. In particular, weighted flux is not automatically a
contraction, and replacing actual prime indicators by unsigned sieve
majorants is still invalid inside signed squared sums.

The rough-part graph/moment possibility was also examined informally, but no
expansion theorem was obtained. Short directed-cycle exclusion alone does
not imply orientation balance: high-girth lifts of biased cyclic flows need
not be reversible. No graph-expansion or natural-average transfer theorem
has been added or assumed.

Spec.lean retains the unchanged import, conjecture statement, and sorry
(SHA256 34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff).
No complete proof/disproof has been submitted.

## Genuine positive lower bound for the weighted opposite-sign fraction

Two new modules compile without warnings and have saved .olean files. Their
printed main axiom checks use only propext, Classical.choice, and Quot.sound.
The temporary CheckLocalMin.lean was removed. Spec.lean is still unresolved.

This batch supplies an UNCONDITIONAL lower bound in the direction needed by
the latest weighted criterion, but only a fixed positive constant, not 1/2.

1. PrimeFactorLocalMinima.lean
   - riseRunStartCount q N counts fall-to-rise transitions of a binary
     orientation sequence.
   - variation_run_potential is a general finite induction for values in
     [0,1]. Its potential is a(N+1) on an increasing edge and 2-a(N+1) on
     a decreasing edge. A fall-to-rise transition pays two units.
   - variation_le_twice_run_starts_add_two:
       sum_{n<N} abs(a(n+1)-a(n)) <= 2*riseRunStartCount(q,N)+2.
     No probabilistic or arithmetic assumption is hidden in this lemma.
   - primeLocalMinima N consists of 0<n<N with
       P(n)<P(n-1) and P(n)<P(n+1).
     Its cardinal equals the run-start count for the actual comparisons.
   - normalizedPrimeLog_variation_bound:
       sum_{n<N} abs(logDifference(N,n)) <= 2*card(primeLocalMinima N)+2.
     The harmless n=0 logarithmic tie is handled explicitly.
   - logDifference_variation_lower:
       delta*(N-card(logRatioSet N delta)-1)
         <= sum_{n<N} abs(logDifference(N,n)).
   - MAIN unconditional primeLocalMinima_positive_lower_proportion:
       exists c>0, eventually card(primeLocalMinima N)/N>=c.
     Apply the previously verified near-tie rarity with epsilon=1/4, then
     take c=delta/8 and absorb the fixed endpoint error.
   - primeLocalMinimaAbove B N restricts the center to P(n)>B.
   - smooth_ceil_power_count_eventually_le bounds the proportion with
     P(n)<=ceil(N^u) by 8*u+epsilon, using existing logarithmic smooth bounds.
   - primeLocalMinimaAbove_power_positive_mass:
       exists u,c>0, eventually
         card(primeLocalMinimaAbove ceil(N^u) N)/N>=c.
     Choose u from the positive local-minimum proportion and discard the
     small smooth-label set. No joint smooth-number asymptotic is used.

2. LocalMinimaOppositeCollisions.lean
   - primeLocalMinima_incidence_data: each strict local minimum at n yields
     a fall at n-1 and a rise at n, both having prime loser P(n), and both
     lying in bothAboveSet 0 N.
   - The map (n,m) -> (n-1,m), on pairs of local minima with P(n)=P(m),
     injects into the ordered opposite-sign loser collisions. It preserves
     their weight P(n). Equality of the two output indices is ruled out by
     their opposite signs; the predecessor map is injective on positive n.
   - primeLocalMinimaAbove_sq_le_weightedOpposite:
       card(localMinimaAbove B N)^2
         <= (sum_{p in labels, p>B} 1/p)*primeLoserWeightedOppositeMass N.
     This is weighted Cauchy--Schwarz plus the weight-preserving injection.
   - MAIN unconditional primeLoserWeightedOppositeMass_positive_quadratic:
       exists c>0, eventually Ow(N)>=c*N^2.
     If local-minimum mass above ceil(N^u) is >=c0*N, the proof gives
     coefficient u*c0^2/2 using the reciprocal-label bound <=2/u.
   - primeLoserWeightedOppositeRatio_positive_lower:
       exists c>0, eventually Ow(N)/Qw(N)>=c.
     Combine the preceding theorem with Qw<=2*N^2 and the already proved
     eventual positivity of Qw.

Hence the current unconditional information is
    c <= weightedOppositeRatio(N) <= 1/2+o(1)
for SOME fixed c>0. The lower bound is not arbitrarily close to 1/2 and
therefore does not discharge density_of_weightedOpposite_liminf. Neither
existence of this ratio's limit nor the original density is proved.

Further route checks did NOT produce the sharp bound:
- The winner group's divisibility expression suggests reverse-prime
  martingale orthogonality over a COMPLETE CRT period. No estimate transfers
  that full-period picture to the growing natural prefix; divisor products
  above the endpoint remain the obstruction. No new martingale theorem was
  formalized or assumed.
- Averaging prime-group cofactor sums using the existing small-prime
  variance bound still leaves selected progressions and a coupled endpoint.
  A Cauchy--Schwarz step loses the same reciprocal-prime mass gained by
  averaging; no decay of the weighted signed remainder was obtained.
- Repeated local-minimum deletion is NOT a contraction proof. Reconnecting
  the surviving neighbors creates a new, generally nonzero comparison at a
  larger prime label and a selected longer gap. The positive lower bound
  above is not being iterated as if the original arithmetic hypotheses and
  signed energy were preserved.

The unchanged Spec.lean SHA256 remains
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No completed proof/disproof has been submitted.

## Local-minimum deletion energy obstruction completed

LocalMinimumDeletionEnergy.lean now compiles and has a saved .olean file.
The last numerical simplification was fixed with `norm_num at h`.
Both printed axiom checks use only propext, Classical.choice, and Quot.sound.

The exact single-deletion formula is
  W_new = W_old + q*(2*s*S_q + 1),
where q is the smaller of the two neighboring labels and s is the sign of
the shortcut. In the actual prefix P(0),...,P(5)=0,1,2,3,2,5, deleting the
strict local minimum P(4)=2 increases weighted winner energy from 8 to 11.
This rules out a general contraction argument by local-minimum deletion;
it does not disprove Erdos 371. Spec.lean remains unchanged and unresolved.

## Latest signed-kernel audit: target still unresolved

Reviewed BalancedKernel.lean and the prime-weighted energy criterion after
finishing the local-minimum deletion example. The signed modular-inverse
kernel remains unbounded by o(N); the available absolute-mass estimates do
not imply signed cancellation. Dilation stability still controls only
selected divisible progressions. No transfer to the unrestricted natural
prefix has been obtained. No conditional criterion has been substituted for
the original statement. The sole verified change in this continuation is
the completed auxiliary LocalMinimumDeletionEnergy.lean module. Spec.lean
remains unchanged, with its original sorry. No valid submission is ready.

## Congruence-forced prime-winner runs: new exact formula and obstruction

New module PrimeWinnerCongruenceRuns.lean compiles without warnings, has a
saved .olean, and all six printed axiom checks use only propext,
Classical.choice, and Quot.sound. CheckCongruence.lean was removed.
Spec.lean remains unchanged and unresolved.

A new prospective uniform estimate |S_p(N)| <= pi(floor(N/p))+1 was tested
as a possible source of logarithmic savings. A targeted Python diagnostic
up to 10^6 found counterexamples (first p=2939,N=26451, value 6 versus 5).
The stronger structured example below is formally verified, without scanning
the whole prefix. No numerical conclusion about the main density is drawn.

Verified arithmetic facts:
- maxPrimeFac_mul_sub_one_lt_of_succ_dvd: if 0<k, k+1<p and
  k+1 divides p+1, then P(kp-1)<p. The divisor k+1 and its complementary
  factor are both below p.
- congruenceRunQuotient(p,k) = p+(p+1)/(k-1).
- If 2<=k<p and k-1 divides p+1, then
    (k-1)*congruenceRunQuotient(p,k)=kp+1,
    p<congruenceRunQuotient(p,k)<=2p+1,
    P(kp+1)>p iff congruenceRunQuotient(p,k) is prime.
  Composite quotients have largest prime factor <=p.
- congruence_run_pair_contribution: under BOTH divisibility assumptions
  and p prime, the edges at kp-1 and kp contribute to the p-winner group
  exactly 1 if that quotient is prime, otherwise 0.
- primeWinnerSum_mul_endpoint, for every prime p and every K:
    S_p(Kp+1) = sum_{1<=k<=K} [contribution(p,kp-1)+contribution(p,kp)].
  This reindexes the entire group, retaining the endpoint correctly.
- primeWinnerSum_congruence_run: if 1<=K, K+1<p, and every j in
  [1,K+1] divides p+1, then
    S_p(Kp+1) = #{2<=k<=K : p+(p+1)/(k-1) is prime}.
- primeWinnerSum_congruence_run_all_prime gives S_p(Kp+1)=K-1 under
  the EXPLICIT additional hypothesis that all those quotients are prime.
  No simultaneous-primality existence theorem is asserted or assumed.
- primeWinnerSum_5039_45352: S_5039(45352)=7. Here K=9 and p+1=5040.
  The eight quotient values are 10079,7559,6719,6299,6047,5879,5759,5669;
  exactly seven are prime (5759 is composite). Finite primality facts use
  norm_num/kernel proofs, not native_decide.
- not_primeWinnerSum_bounded_by_cofactor_prime_count disproves the above
  universal constant-one bound: pi(floor(45352/5039))+1=5<7.

The exact congruence-run identity explains why same-sign group contributions
need not admit an internal cancellation pairing. It does not refute a larger
constant bound, an averaged energy bound, or the original density conjecture.
No new signed cancellation estimate across the prime groups has been proved.
The prime-insertion/CRT review also did not bypass the large-product barrier.
No complete proof/disproof has been submitted.

## Analytic additive-score density discontinuity and diagonal warning

New module AdditiveDensityDiscontinuity.lean compiles without warnings and
has a saved .olean. Its four printed main axiom checks use only propext,
Classical.choice, and Quot.sound. CheckAnalytic.lean was removed.
The original Spec.lean remains unchanged and unresolved.

The explicit family is F_t(n)=log(n)-t*v_2(n), where v_2 is factorization 2.
Verified:
- score_mul: F_t is completely additive on positive integers.
- score_continuous and score_analyticAt: for each n the dependence on t is
  continuous and real analytic (indeed linear).
- score_tendsto_zero_parameter: F_t(n) -> log(n) as t -> 0.
- log_increment_bound and log_increment_lower:
    1/(n+1) <= log(n+1)-log(n) <= 1/n, for n>0.
- score_rise_iff_even: if t>0, n>0 and 1/n<t, a rise occurs exactly at
  even n. The neighboring 2-adic valuations differ by at least one.
- score_positive_parameter_density_half: every FIXED positive t has
  comparison density 1/2.
- score_zero_parameter_density_one: at t=0 the comparison density is 1.
- pointwise_continuous_additive_density_jump packages the complete
  additivity, parameter continuity, and the distinct densities.
- diagonalParameter(N)=1/(N+1)^3 is positive and tends to zero.
- diagonalParameter_prefix_rises: for EVERY 0<n<=N, the comparison of
  F_(diagonalParameter N) at n,n+1 is a rise. Use v_2(n+1)<n+1 and the
  lower logarithmic increment bound.
- diagonal_parameter_density_one: using the parameter diagonalParameter(n)
  at the n-th comparison gives density one, even though each fixed positive
  parameter separately has comparison density one half.

This is a counterexample to generic continuity/interchange-of-limits
arguments for comparison densities, not to Erdos 371 and not to any of the
existing carefully quantified approximation criteria. No cancellation for
fixed positive-index additiveLogScore was obtained. The large-prime
contributions prevent applying the ordinary small-prime limit-law argument.

Also reviewed the divisible-gap graph/averaged-dilation possibility. A
common-endpoint graph average still samples the original signed means at
N/p, not at N; concentrating p in a short relative interval removes the
large reciprocal-prime averaging mass. No graph-expansion theorem or
natural-endpoint transfer was proved or assumed.
No complete proof/disproof has been submitted.

## Marginal-law reconstruction audit: no new arithmetic conclusion

Revisited whether the actual prime-factor marginal law, rather than merely
equal marginals, could determine comparison symmetry from the CRT-accessible
inclusion moments. No uniqueness theorem was obtained. The existing finite
partition models are NOT models of the actual marginal law; no theorem here
promotes them to countermodels for that stronger hypothesis. A possible
split/merge perturbation of continuous partition laws was considered, but
no measure-theoretic embedding into the actual marginal law was proved or
assumed. This remains an audit, not a new formal obstruction theorem.

The arithmetic large-product terms and their signed correlations remain
uncontrolled. No new auxiliary file was added in this round, and no
conditional reduction was substituted for the original theorem. The latest
verified module remains AdditiveDensityDiscontinuity.lean. Spec.lean has its
unchanged import, statement and original sorry. No valid proof submission
is ready.

## Upper-half logarithmic-weight removal audit

Re-examined the prime-band discrepancy when both prime labels exceed sqrt(N).
A large prime divisor is unique there. Weighting its indicator by log(q)
allows subtraction from the full factorization logarithm, but the remaining
small-prime terms are still evaluated on the selected opposite-residue
progressions. No cancellation theorem for that weighted discrepancy was
obtained. The existing centered logarithmic averaging result controls a
replacement error, not the remaining shifted smooth-number sum.

A geometric expansion of the reciprocal large-prime logarithmic weight is
uniformly convergent away from the square-root boundary, but produces signed
cofactor-weighted sums. Those sums are not known to vanish. The expansion
therefore cannot be used as a contraction proof or as an unconditional
weight-removal argument. No such assertion has been added.

No new Lean module was added in this audit. Spec.lean remains unchanged with
its original sorry. No complete proof or disproof is available for submission.

## Direct discrepancy and matching audit

Returned to the total signed discrepancy rather than the stronger prime-group
energy. Reviewed the existing full-ranking prefix obstruction and the exact
cofactor/small-prime reflections. No direct o(N) bound for the total signed
count, and no matching leaving only o(N) unmatched inputs, was obtained.

The reordered-prime counterexamples do not refute such a bound for the
natural prime order. Conversely, the natural prime order does not remove
the proved multiplicity and endpoint problems of the available reflection
maps. No injectivity, Hall condition, or uniform unmatched-count bound was
proved. The relation between the order of large prime labels and the reverse
order of their cofactors still leaves the same arithmetic progression counts.

No new theorem was added in this audit. Spec.lean retains its original sorry
and unchanged statement/import. No completed proof/disproof is ready.

## Further signed-envelope and logarithmic-mass audit

Rechecked the exact mixed-divisor reduction, the weighted opposite-collision
criterion, and the additive logarithmic mass identities. No new signed
estimate was obtained. In particular:
- Removing the one-sided divisor terms leaves the genuinely mixed sum,
  not a quantity bounded by a vanishing unsigned tail.
- Exact factorization logarithmic mass gives linear telescoping, but does
  not estimate the cubic mixed skew or higher nonlinear comparison tests.
- The CRT-accessible product restriction must remain in any mixed-moment
  argument. No extension beyond that restriction was proved.
- The existing finite partition models do not have the actual prime-factor
  marginal law. No continuous embedding or stronger obstruction involving
  that law has been formalized or used.

No new Lean theorem was added during this audit. The target remains
unresolved, and Spec.lean has its original import, statement, and sorry.
There is no valid completed proof or disproof to submit.

## Polynomial multiplier / natural-endpoint continuation

Reviewed PolynomialMultiplierChirpExclusion, DoublePrimeAveraging,
MultiplierInvariantModel, the common-endpoint character formula, and the
subpower comparison stability statement. The latter changes the VALUES
being compared by subpower multipliers; it does not transfer prefix averages
from N/p to N. Exact small-multiplier invariance still applies to selected
multiples and is not independence from residue classes.

Considered whether a signed-edge estimate on the small-smooth-multiplier
quotient, or an entropy argument with endpoints depending on the selected
prime, could supply natural-prefix symmetry. No such estimate or endpoint
transfer was proved. The existing DivisorCycleBound already supplies the
short directed-cycle product bound; that bound alone does not control the
signed flow or its energy. No new theorem was added or assumed.

Spec.lean remains unchanged and unresolved. No completed proof/disproof is
available for verification.

## New exact skew identity for nested multiplicative indicators

NestedMultiplicativeSkew.lean compiles without warnings and has a saved .olean.
All seven printed axiom checks use only propext, Classical.choice, Quot.sound.
It is an auxiliary example, not a disproof of Erdos 371.

Let f(n)=1 precisely when n>0 and every prime divisor is 1 modulo 3.
Let g(n)=1 precisely when 3 does not divide n. Verified:
- f and g are completely multiplicative (including zero).
- f(n)<=g(n) for every n.
- f(n)g(n+1)-g(n)f(n+1)=f(n), pointwise as integers.
  Indeed f(n)=1 forces n=1 mod 3, so the predecessor is divisible by 3
  and the successor is not.
- Consequently the prefix skew is exactly #{1<=n<=N:f(n)=1}.
- The count/skew at N=100 is 14, kernel checked.
- Neither f nor g equals any initial-segment largest-prime cutoff.
  The explicit witnesses use f(2)=0,f(7)=1 and g(3)=0,g(5)=1.

This arose while testing the proposed auxiliary universal bound
  |skew(f,g;N)| <= pi(N+1)
for arbitrary nested completely multiplicative zero-one indicators. A
separate exact-integer Python sieve found for this structured example
  count_f(10^6)=80587, pi(10^6)=78498.
These large finite counts are diagnostic only, NOT Lean-certified theorems.
No asymptotic for this example is asserted here. No conclusion against the
original largest-prime-factor conjecture follows from it.

The diagnostic script check_nested_skew.py is retained. IMPORTANT: GLPK can
return an incumbent at the time limit without throwing an exception. Its
output status was corrected to say optimality is NOT certified. The earlier
N=300 incumbent 29 was below the explicit structured value 36; no global
optimality claim is made for any of these runs. A forced structured candidate
confirmed the 36 objective. Local-search diagnostics also found no useful
natural-cutoff estimate. They have no role in the Lean proofs.

An attempted direct kernel evaluation of primeCounting(10000) was killed
(return code 137) after about 76 seconds, so the large-count experiment was
not pursued by that method. CheckNestedCount.lean has been removed.

Spec.lean remains unchanged, including its original sorry. No signed
cancellation estimate for the natural prime order has been obtained, and
there is no complete proof/disproof to submit.

## Least-losing-prime reflection: canonical orbit theorem and harmonic check

New module Submission/SmallPrimeReflectionOrbit.lean compiles without warnings
and has a saved .olean. Its six printed main axiom checks use only propext,
Classical.choice, Quot.sound. Spec.lean remains unchanged and unresolved.

Write T=smallPrimeReflection, l=leastLosingPrime, p=primeWinner. Verified:
- smallPrimeReflection_mod_free: if n<l(n)*p(n), then
    T(n)=l(n)*p(n)-1-n.
- losingNumber_reflection_add_mod_free: under this same smallness condition,
  the losing numbers of n and T(n) sum to l(n)*p(n).
- leastLosingPrime_small_reflection_eq_two: for n>1 satisfying the smallness
  condition, l(T(n))=2. If l(n)=2, use monotonicity. Otherwise the product
  and original losing number are odd, so the reflected losing number is even.
- leastLosingPrime_reflection_descent: for every n>1, either l(T(n))<l(n),
  or l(T(T(n)))=2. In the equality case T(n) is inside the same period.
- smallPrimeReflection_reaches_least_two: some k<=2*l(n) has l(T^[k](n))=2.
  This is proved by strong induction on l(n), not by assuming stationarity.
- smallPrimeReflection_canonical_of_least_two: if l(n)=2, then T(n)=p(n)
  on a rise, and T(n)=p(n)-1 on a fall.
- smallPrimeReflection_eventually_canonical: there is k<=2*l(n)+1 such
  that every j>=k satisfies T^[j](n) in {p(n)-1,p(n)} and
    T^[j+2](n)=T^[j](n).

A kernel-checked example shows why a claim of entry within two steps would
be false: 774 -> 85 -> 129 -> 42 -> 43 -> 42, with winner 43.
In particular, the modulo reduction cannot be ignored in the parity argument.

The finite harmonic check now also has a Lean proof:
  reflectionHarmonicFiber(N,m) = sum_{2<=n<N, T(n)=m} 1/n, as a rational.
  reflectionHarmonicFiber(9,3)=5/8 != 1/3.
The incoming indices here are 2 and 8. This only rules out exact finite
harmonic stationarity. It does NOT disprove normalized asymptotic harmonic
stationarity, nor establish any logarithmic density result.

LIMIT: eventual orbit balance does not imply natural-input balance. The map
is noninjective; neither fiber weights nor the distribution of hitting-time
parity have been controlled. No proof of the conjecture follows from this
module.

Also reconsidered an o(N) skew bound uniform over moving nested multiplicative
indicators. The earlier example blocks a prime-count-sized bound, not this
asymptotic bound. No uniform estimate was obtained. Fixed-function approximation
or fixed-cutoff convergence was not substituted for the missing uniformity.
The original signed arithmetic cancellation and sharp weighted-opposite lower
bound remain unproved. No complete proof/disproof is ready to submit.

## Both orientations sharpen the actual local-minimum collision lower bound

New module Submission/LocalMinimaCollisionSymmetry.lean has been added.
It proves an improvement for the ACTUAL prime-factor sequence, not a model
counterexample. The original Spec.lean remains unchanged and unresolved.

Verified definitions and identities:
- primeLoserFallRiseCollisions restricts the existing ordered opposite
  collision set to pairs whose first factorSign is -1.
- primeLoserWeightedFallRiseMass is the sum of their common loser-prime weight.
- Swapping entries preserves opposite-collision membership and their common
  prime label, and swaps fall-to-rise with rise-to-fall.
- primeLoserWeightedOppositeMass_eq_twice_fallRise:
    O_w(N) = 2 * primeLoserWeightedFallRiseMass(N), exactly.

The old local-minimum injection lands in just the fall-to-rise half. Keeping
its reversed partners therefore gives the sharper finite inequalities:
- 2 * sum_{n,m local minima above B, P(n)=P(m)} P(n) <= O_w(N).
- twice_primeLocalMinimaAbove_sq_le_weightedOpposite:
    2 * card(local minima above B)^2
      <= (sum_{p in primeWinnerLabels(N), p>B} 1/p) * O_w(N).
- primeLocalMinimaAbove_power_sq_le_opposite: for u>0 and N>=4,
    u * card(local minima above ceil(N^u))^2 <= O_w(N).

Consequently, if the known local-minimum proportion in that power range is
at least c>=0 eventually, then eventually
    u*c^2*N^2 <= O_w(N),
    u*c^2/2 <= primeLoserWeightedOppositeRatio(N).
For the SAME u,c this doubles the previously derived lower bounds.
weightedOpposite_improved_positive_lower applies this to the already proved
existence of positive u,c and is unconditional.

LIMIT: the result remains a fixed positive lower bound, not a bound tending
to one half. Swapping the entries of an opposite-sign pair does not convert
same-sign pairs into opposite-sign pairs. No cancellation or contraction
has been inferred from this exact orientation symmetry.

Also reviewed the divisor-cycle product bound and dyadic sign identity.
The former only excludes sufficiently short cycles in sufficiently high
prime ranges. The latter still contains the sign-selected between event;
an unsigned bound on that event does not give a signed contraction. The
existing counterexamples to local-minimum deletion monotonicity and permanent
dyadic pruning remain applicable. No new contraction estimate was proved.
No complete proof or disproof of Erdos 371 is ready to submit.

## Signed determinant and direct residue-kernel continuation

Revisited the exact loser-collision coordinates and the direct Alladi/Mobius
reciprocal-root reduction, seeking a signed estimate rather than a better
fixed positive constant. No new cancellation estimate was obtained.

For collision shifts e,d in {+1,-1}, the determinant l*e-k*d has the
same-sign form ±(l-k) or the opposite-sign form ±(l+k). The existing unsigned
three-prime sieve estimates do not compare the corresponding signed counts.
Swapping the two incidences, or reversing both signs, preserves e*d; this
cannot turn the proved orientation symmetry into cancellation between
same-sign and opposite-sign collisions.

The direct two-prime/divisor formula avoids the stronger weighted energy
hypothesis, but retains the exact reciprocal-root indicators and endpoint
restrictions. Swapping the divisor arguments changes the signs of both its
least-factor weight and its discrepancy kernel. Their product is unchanged,
not canceled. Complete-row or one-dimensional rough Mobius cancellation was
not applied to the remaining truncated kernel without a valid estimate.

No new Lean theorem was added in this round. The latest verified module is
LocalMinimaCollisionSymmetry.lean; its six printed main axiom checks use only
propext, Classical.choice, Quot.sound, and its .olean is saved. Spec.lean is
unchanged with its original sorry. No complete proof/disproof is ready for
submission.

## Multiplicative-stability and reversal-symmetry continuation

Investigated whether exact almost-everywhere fixed-multiplier invariance,
together with the stronger growing-multiplier cutoff identity, forces
reversal symmetry of adjacent comparisons. No such implication was proved.
The library search found no stable-set or strong-stationarity theorem that
supplies it.

The distinction remains essential: P(k*n)=P(n) away from small prime labels,
and the analogous identity at k*(n+1), concern values on a selected divisible
progression. They do not assert independence of the two-point observable
from that progression, nor equate natural prefix averages at N and N/k.
Existing fixed-multiplier models and the growing-range chirp exclusion were
reviewed without promoting either to an arithmetic correlation theorem.
No logarithmic-to-natural-density transfer or full-observable gap invariance
was assumed.

No new Lean theorem or signed cancellation bound was obtained in this round.
Spec.lean retains its original import, conjecture statement, and sorry.
No complete proof or disproof is ready for verification.

## Logarithmic factorization/contraction follow-up

Checked the logarithmic factorization averaging, nonlinear odd-moment identity,
and uniform smooth-cutoff stability for a possible signed contraction. No
contraction was obtained. The first logarithmic difference moment telescopes;
the cubic identity retains cubicLogSkew, and no estimate making that mixed
correlation vanish was proved. The centered logarithmic prime average still
contains its N/p endpoint and opposite shifted smoothness conditions.

The uniform cutoff-change bound permits logarithmically coalescing cutoffs.
It does not move between two distinct fixed power exponents with vanishing
error, or justify iterating a fixed-cutoff convergence result along a growing
cutoff. A targeted library search found no largest-prime-factor comparison
density theorem supplying the missing estimate.

No new Lean module was added, and no stronger cancellation hypothesis was
assumed. Spec.lean is unchanged with its original sorry. The conjecture is
still unresolved here; no complete proof or disproof is ready to submit.

## Four-label dyadic separation model completed

Submission/DyadicSeparatedBias.lean now compiles without warnings, has a saved
.olean, and all seven printed main axiom checks use only permitted axioms.
This is ONLY an auxiliary model, not maxPrimeFac and not a disproof of 371.

The four-label recursive subdivision has exact label(2*n)=label(n) for every
n, and label(n)!=label(n+1) for n>=2. Its finite transition rule uses a middle
label distinct from both endpoints. The kernel checks that every distinct
ordered endpoint pair has signed block sum at least 2 after six subdivisions.
It follows that sum_{n<64*M} sign(n)>=2*M-132. The verified theorem
not_half_density shows {n:label(n)<label(n+1)} does not have density 1/2.
No claim of existence of its density is made. A separate kernel check shows
label(15)!=max(label(3),label(5)) and label(15)!=label(5), so the model lacks
both max-under-multiplication and multiplication-by-three invariance.

Conclusion limited to the proposed strategy: doubling invariance plus a fixed
finite ordered range and no adjacent ties does not force comparison balance.
The actual conjecture and its needed signed arithmetic cancellation remain
unresolved. Spec.lean is unchanged; no complete solution is ready to submit.

## Post-dyadic arithmetic review

Revisited whether invariance under all sufficiently small multipliers supplies
unrestricted two-point gap invariance. It does not follow from the available
identities: dilation samples a divisible progression and changes the endpoint.
The Hilbert-space symmetry theorem in StationarySymmetry still lacks its
arithmetic gap-invariance hypothesis. No such hypothesis has been proved.

Also reviewed uniform skew cancellation for nested nonnegative multiplicative
indicators. The existing fixed residue example only obstructs overly strong
finite bounds; it does not disprove uniform o(N) skew. Conversely, fixed-function
mean/correlation convergence is not uniform for moving prime cutoffs. No
uniform cancellation theorem was obtained. Reciprocal-root bilinear formulas
still retain prime/smooth restrictions, and unsigned sieve bounds do not
compare the two orientations. No new arithmetic theorem or settlement was
claimed. Spec.lean remains unchanged with its original sorry.

## Composite losing-divisor reflection and exact marked balance

New module Submission/CompositeDivisorReflection.lean compiles without warnings
and has a saved .olean. All five printed main axiom checks use only propext,
Classical.choice, Quot.sound. No admissions or unsafe evaluation are used.
Spec.lean remains unchanged and unresolved.

Actual arithmetic generalization:
- small_divisor_prime_pair_rise/fall allow the smaller divisor a to be
  composite, assuming 0<a<p, p prime, and the input below a*p. The prescribed
  p side has largest prime factor exactly p, and the a side has largest
  prime factor below p.
- composite_losing_divisor_reflection: for n>1, any divisor a of losingNumber n
  with 1<a<primeWinner n gives a reflection divisorReflection n a (primeWinner n)
  that reverses factorSign and preserves primeWinner. The original input need
  not be below the period: the reflected output is reduced into that period.
  This is not an assertion of distribution preservation.

Marked balancing identity:
- riseDivisorMarks p consists of 2<=a<p, 1<=b<p, p | a*b+1.
- fallDivisorMarks p has the same factor bounds and p | a*b-1.
- (a,b) -> (a,p-b) is a bijection between these marked sets.
- For prime p, every rise mark represents the ACTUAL rise at n=a*b, with
  primeWinner n=p. Every fall mark represents the ACTUAL fall at n=a*b-1,
  again with primeWinner n=p.
- riseDivisorMarks_reflection_index identifies the reflected index exactly:
    divisorReflection(a*b,a,p) = a*(p-b)-1.
- marked_divisor_comparison_balance: the two complete marked sums of
  w(a)*factorSign cancel for arbitrary real divisor weight w.
- marked_divisor_prefix_boundary retains the exact prefix remainder:
    sum_rise w(a) [a*b<N] - sum_fall w(a) [a*b<=N]
      = sum_rise w(a) ([a*b<N]-[a*(p-b)<=N]).

LIMIT: the marked bijection does not make the unmarked index map injective.
No estimate making the displayed signed boundary remainder negligible has
been proved, and no replacement of divisor multiplicity by constant weight
has been justified. Complete marked balance alone does not settle natural
comparison density. No complete proof or disproof is ready to submit.

## Elementary Kloosterman fourth moment: a new signed estimate

Two new modules compile without warnings, have saved .olean files, and their
main printed axiom checks use only propext, Classical.choice, Quot.sound:
- Submission/KloostermanFourthMoment.lean (imports FormalConjecturesUtil)
- Submission/KloostermanFourierTests.lean (imports KloostermanFourthMoment)
Namespace: Erdos371.Kloosterman. No admissions or unsafe evaluation.
Spec.lean remains unchanged and unresolved.

For a finite field F of cardinality q and primitive additive character psi,
define S(a,b)=sum_{x in F^units} psi(a*x+b/x). Verified:
- inverse_pair_collision: equal sums and reciprocal sums of unit pairs, with
  nonzero sum, imply equality of the unordered pairs.
- inverse_curve_energy_bound: the additive energy E of x -> (x,1/x), x!=0,
  is at most 3*card(F^units)^2. Zero-sum fibers are separately bounded by the
  unit cardinality; nonzero-sum fibers have at most two elements.
- curve_parseval: exact two-dimensional character orthogonality for arbitrary
  finite parametrized curves. This proof uses a local maxHeartbeats 2000000.
- kloosterman_fourth_moment: sum_{a,b} |S(a,b)|^4=q^2*E.
- kloostermanSum_scale: S(a*t,b/t)=S(a,b) for units t.
- kloosterman_orbit_lower: for a!=0, the scaling orbit gives
    card(F^units)*|S(a,b)|^4 <= sum_{c,d}|S(c,d)|^4.
- kloosterman_norm_fourth_le: |S(a,b)|^4<=3*q^3 for a!=0.
- Inversion exchanges a and b, extending the bound to a!=0 OR b!=0.
- kloosterman_normalized_bound:
    |S(a,b)|/q <= sqrt(sqrt(3/q)) at every nonzero frequency.
- prime_kloosterman_normalized_bound specializes to ZMod p and stdAddChar.
- prime_kloosterman_normalized_tendsto gives convergence to zero along any
  prime-modulus sequence tending to infinity, uniformly in moving nonzero
  frequencies. Primality is supplied by [forall n, Fact (p n).Prime].
This is the elementary fourth-moment saving, NOT an assumed Weil bound.

Fourier test module:
- fourierPolynomial psi c x = sum_a c(a)*psi(a*x).
- inverseCorrelation = sum_{x!=0} fourierPolynomial c x * fourierPolynomial d (1/x).
- inverseCorrelation_expand identifies it exactly with sum_{a,b} c(a)d(b)S(a,b).
- inverseCorrelation_normalized_error_bound:
    |inverseCorrelation-(q-1)c(0)d(0)|/q
      <= sqrt(sqrt(3/q)) * (sum_a |c(a)|) * (sum_b |d(b)|).
- prime_inverseCorrelation_normalized_tendsto proves cancellation when those
  two Fourier coefficient L1 norms are bounded uniformly along prime moduli.
The coefficient hypotheses are explicit and have NOT been established for
moving prime-factor observables.

Scope and remaining work:
Swapping the marked divisor factors does not itself preserve the natural
prefix boundary. The Kloosterman estimate supplies a genuine signed arithmetic
tool but has not yet been applied to a sharp inverse-rectangle/hyperbolic
count. A possible next step is finite Fourier inversion, interval-transform
L1 bounds, and then the marked prefix boundary. Even such marked boundary
cancellation would still require a valid removal of divisor multiplicities.
The direct rough-Mobius kernel additionally retains composite moduli and
least-factor weights; the new prime-field estimate was not substituted for
an estimate of that kernel. No proof/disproof of Erdős 371 is ready to submit.

## Uniform modular-inverse rectangle discrepancy via smoothing

Three new modules compile without warnings, have saved .olean files, and all
printed main axiom checks use only propext, Classical.choice, Quot.sound:
- Submission/FiniteFieldFourierInversion.lean
- Submission/InverseRectangleSmoothing.lean
- Submission/InverseIntervalRectangles.lean
All use namespace Erdos371.Kloosterman. Spec.lean is unchanged and unresolved.

The route deliberately avoids a sharp logarithmic Fourier L1 bound for sharp
intervals. Translation smoothing and Parseval supply enough control instead.

FiniteFieldFourierInversion:
- fourierCoeff psi f a = (sum_x f(x)*psi(-a*x))/q.
- fourier_inversion, fourier_bilinear_parseval, fourier_parseval.
- finiteConvolution f g x = sum_y f(y)g(x-y).
- fourierCoeff_convolution = q*hat(f)*hat(g).
- setIndicator A is complex 0/1; its squared norm sum is card(A).
- smoothedIndicator A J = (1/card J)*convolution(1_J,1_A).
- smoothedIndicator_fourier_l1_sq, for J nonempty:
    (sum_a |hat(smoothedIndicator A J)(a)|)^2 <= card(A)/card(J).

InverseRectangleSmoothing:
- smoothedIndicator has norm <=1 and unchanged zero Fourier coefficient.
- translationError A y = sum_x |1_A(x)-1_A(x-y)|.
- smoothingError A J = average_{y in J} translationError A y.
- smoothedIndicator_l1_error <= smoothingError.
- inverseRectangleCount A B counts x in F^units with x in A and 1/x in B.
- inverseRectangleCount_smoothing_bound gives
    |count-(q-1)(card A/q)(card B/q)|/q
      <= (smoothingError A J+smoothingError B J)/q
           + sqrt(sqrt(3/q))*q/card J.
All coefficient costs and approximation errors are explicit.

InverseIntervalRectangles, for prime p:
- residueInterval p L = {x : ZMod p | x.val<L}.
- Its cardinality is L when L<=p.
- Its one-step translation L1 error is <=2. Only x=0 and x=(L mod p)
  can contribute; wraparound is included rather than discarded.
- translationError_nat_le bounds the error of n shifts by n times the
  one-step error, using an exact finite-group reindexing.
- For 0<H<=p, smoothing by residueInterval p H has error <=2H.
- inverse_interval_rectangle_bound, with L,M<=p and 0<H<=p:
    |count-(p-1)(L/p)(M/p)|/p
      <= 4H/p + sqrt(sqrt(3/p))*p/H.
- Taking H=floor(p/K)+1 for K>=2 gives an upper bound
    4/K + 4/p + K*sqrt(sqrt(3/p)).
- inverse_interval_rectangle_tendsto proves o(p) discrepancy along every
  sequence of prime moduli tending to infinity, uniformly in moving L,M<=p.
- inverse_interval_rectangle_ratio_tendsto is the usual normalized form:
    |count/p-(L/p)(M/p)| -> 0.
The last change of main term costs at most 1/p.

LIMIT AND NEXT STEP:
This is an unconditional modular-inverse rectangle-counting result. It has
not yet been converted into cancellation for the signed marked hyperbolic
cutoff a*b<N. One can next handle the -1 inverse orientation and approximate
the hyperbolic region by finite rectangles, keeping the boundary count.
Even successful marked-prefix cancellation would leave the removal of divisor
multiplicities unresolved. The direct rough-Mobius kernel also still has its
composite-modulus and least-factor restrictions. None of these gaps was
silently replaced by the new prime-field rectangle theorem. No complete
proof or disproof of the original conjecture is ready for submission.

## Both inverse orientations, monotone regions, and marked hyperbola cancellation

Four new modules compile and have saved .olean files. Their printed main
axiom checks use only propext, Classical.choice, Quot.sound. No admissions.
Spec.lean remains unchanged and unresolved.

1. Submission/SignedInverseRectangles.lean
   Namespace Erdos371.Kloosterman. Negated sets preserve cardinality and
   translationError exactly, by the substitution x -> y-x and norm symmetry.
   orientedInterval p true M is the negation of residueInterval p M;
   false is the original interval. signedRectangleCount is explicitly the
   count of units x with x.val<L and (if s then -1/x else 1/x).val<M.
   Both signs satisfy the same smoothing bound. For T>=2:
     |signedRectangleCount/p-(L/p)(M/p)|
       <=4/T+5/p+T*sqrt(sqrt(3/p)), uniformly L,M<=p.

2. Submission/MonotoneRegionRectangles.lean
   Namespace Erdos371.MonotoneRectangles; generic finite combinatorics.
   rectCount a b L M counts i with a(i)<L,b(i)<M.
   regionCount a b h counts i with a(i)<h(b(i)).
   sliceCount records b(i)/H=j. Verified exact fiber partition, antitone
   staircase sandwich, and strip=prefix rectangle difference (with clipping
   at p). stairArea is the corresponding normalized rectangular area.
   stairArea_gap bounds upper-minus-lower area by H/p, via telescoping
   heights and clipped widths <=H.
   monotone_region_comparison: two point sets with b,d<p and rectangle
   errors <=delta have region-count normalized difference at most
     H/p+4*K*delta,
   whenever H>0, p<=K*H, h is antitone, and h(0)<=p.
   No boundary cells or multiplicities are dropped.

3. Submission/InverseMonotoneRegions.lean
   Namespace Erdos371.Kloosterman.
   orientedInverse p s x = if s then -1/x else 1/x.
   orientedRegionCount applies regionCount to (x.val,orientedInverse.val).
   Applying the two rectangle estimates yields the explicit finite bound
     H/p+4*K*(4/T+5/p+T*sqrt(sqrt(3/p))).
   oriented_region_difference_tendsto: normalized signed count difference
   tends to zero along every prime-modulus sequence tending to infinity,
   uniformly over moving antitone h with h(0)<=p.
   Proof chooses fixed K,T depending on epsilon and H=floor(p/K)+1; it
   does not exchange limits in a moving unproved estimate.
   hyperbolaCutoff p N y = if y=0 then p else min p ((N-1)/y+1).
   It is globally antitone; for positive a,b with a<p, a<cutoff iff a*b<N,
   including N=0 (both conditions false on positive a).
   inverse_hyperbola_difference_tendsto proves
     |inverseHyperbolaCount(p,true,N)-inverseHyperbolaCount(p,false,N)|/p ->0
   uniformly in arbitrary moving integer N. Counts are over units, with
   products of the two canonical integer representatives less than N.

4. Submission/MarkedHyperbolaCancellation.lean
   Imports InverseMonotoneRegions and CompositeDivisorReflection.
   chosenDivisorMarks p true=riseDivisorMarks p; false=fallDivisorMarks p.
   canonicalDivisorPair sends x to (x.val,orientedInverse.val).
   For first coordinate >=2, it lies in the corresponding actual divisor
   mark set. Conversely every mark arises from a unique unit. These facts
   are proved using the exact ZMod divisibility criteria, including the
   nontruncated subtraction condition for the falling product a*b-1.
   markedProductCount p s N counts chosen marks with COMMON condition a*b<N.
   markedProductCount_eq_unit_filter is the exact bijection. Removing first
   coordinate one costs at most one mark per sign.
   marked_product_difference_tendsto proves the resulting actual marked
   rise/fall difference is o(p), uniformly in the common losing-product N.

IMPORTANT LIMITS:
This is not unweighted Erdős 371. Each index is counted with its eligible
factorization multiplicity; some indices have no eligible mark. The estimate
is normalized by the fixed winning prime p, not by the original prefix N.
No summation over winning primes giving o(N) has been proved. In addition,
the common losing-product cutoff is not yet the exact index-prefix cutoff:
a rise at n=a*b uses a*b<N, whereas a fall at n=a*b-1 uses a*b<=N.

Possible next finite step: control this one-unit cutoff shift using a thin
antitone band. The integer cutoff functions for N and N+1 differ by at most
one on positive coordinates. A staircase-area comparison for two pointwise
close heights gives an extra O(1/p), while the existing rectangle and grid
errors still vanish. This can avoid needing a separate divisor-function
bound. Even that refinement would not remove divisor multiplicity or fix
the normalization/summation gap. No complete proof/disproof is ready to submit.

## Thin-band boundary and exact marked index-prefix cancellation

Two new modules compile and have saved .olean files. Their main axiom checks
use only propext, Classical.choice, Quot.sound. No admissions were added.
Spec.lean remains unchanged with its original sorry; no solution submitted.

1. Submission/ThinMonotoneBands.lean
   Namespace Erdos371.MonotoneRectangles; imports MonotoneRegionRectangles.
   - stairArea_sub_le: if k(j)<=h(j)+r, the difference in staircase areas is
     at most r/p. Clipped widths telescope to at most one after normalization.
   - stairArea_gap_of_close: upper area for k minus lower area for antitone h
     is at most H/p+r/p.
   - regionCount_mono: pointwise increasing the height increases the count.
   - thin_monotone_band: if h,k are antitone, h<=k<=h+r, and rectangle errors
     are at most delta, then
         |regionCount(k)/p-regionCount(h)/p| <= H/p+r/p+4*K*delta,
     under the existing H>0, p<=K*H, height-at-zero<=p hypotheses.

2. Submission/InverseHyperbolaBoundary.lean
   Imports MarkedHyperbolaCancellation and ThinMonotoneBands.
   Namespace Erdos371.Kloosterman.
   - hyperbolaCutoff_mono: increasing N increases its integer cutoff.
   - hyperbolaCutoff_succ_le: the cutoffs for N+1 and N differ by at most one,
     including y=0 and N=0; uses Nat.succ_div on positive N.
   - inverse_hyperbola_boundary_bound: either orientation has boundary mass
     bounded, after normalization by p, by
         H/p+1/p+4*K*(4/T+5/p+T*sqrt(sqrt(3/p))).
   - inverse_hyperbola_boundary_tendsto: uniform o(p) product-equality mass,
     allowing both the orientation and cutoff to move with the prime modulus.
   - inverse_hyperbola_prefix_difference_tendsto: negative inverse with ab<N
     and positive inverse with ab<N+1 have difference o(p).
   - markedProductCount_two_cutoff_difference_bound: transfer costs at most
     2/p for arbitrary separate rise and fall cutoffs.
   - markedIndexCount counts a rise at ab and a fall at ab-1, both with their
     index < N. Its true branch is markedProductCount(true,N); its false
     branch is markedProductCount(false,N+1). The equality for the false
     branch explicitly uses positivity of products in the marked set.
   - marked_index_prefix_difference_tendsto: the EXACT marked natural-index
     prefix counts differ by o(p), uniformly in arbitrary moving N.

LIMITS REMAIN:
This does not remove divisor-factorization multiplicity or cover indices
without any eligible mark. For example, n=27 is an actual rise with winning
prime 7, but 27 has no factorization a*b with 2<=a<7 and 1<=b<7. Conversely
n=6 with winner 7 has marks (2,3),(3,2),(6,1). These are explanatory arithmetic
examples, not newly asserted Lean theorems. There is no unweighted transfer
estimate, and the new o(p) error is not an o(N) estimate after summing over
winning primes. The exact-prefix refinement repairs only the one-unit
boundary issue. No full proof or disproof of the original conjecture is ready.

## High-winning-prime coverage and exact reciprocal-multiplicity unweighting

Three new modules compile without warnings and have saved .olean files.
Their printed main axiom checks use only propext, Classical.choice, Quot.sound.
No admissions, unsafe evaluation, or additional axioms were used. Spec.lean
remains unchanged with its original sorry; no solution has been submitted.

1. Submission/BalancedSmoothFactorization.lean
   Imports CompositeDivisorReflection; namespace Erdos371.
   - exists_divisor_above_le_mul_maxPrimeFac: if 1<=k<m, there is d|m with
       k<d<=k*P(m).
     Choose the least divisor above k, remove one prime factor r, and use
     minimality to get d/r<=k and r<=P(m).
   - exists_two_factors_lt_of_square_lt_cube:
     if m>1, P(m)<p, and m^2<p^3, there are a,b with
       2<=a<p, 1<=b<p, a*b=m.
     For m>=p put k=floor(m/p); the square/cube inequality gives k^2<p.
     If P(m)>k, use a=P(m). Otherwise the preceding divisor lemma gives
     k<a<=k*P(m)<=k^2<p. In either case b=m/a<p. For m<p use (m,1).

2. Submission/HighWinnerMarkCoverage.lean
   Imports BalancedSmoothFactorization and InverseHyperbolaBoundary.
   - rise_mark_exists_of_square_lt_cube and fall_mark_exists_of_square_lt_cube
     apply the factorization criterion to the actual losing neighbor.
   In namespace Erdos371.Kloosterman:
   - divisorMarkIndex true (a,b)=a*b, false (a,b)=a*b-1.
   - indexMarks p s n is the fiber of this index map within chosenDivisorMarks.
   - indexMarkMultiplicity is its cardinality.
   - markedIndexCount_eq_sum_multiplicities gives the exact prefix fiber sum.
   - high_winner_has_indexMark: for 1<n<N and N^2<primeWinner(n)^3, the
     multiplicity for n's actual orientation is positive. Thus the coverage
     gap is removed in the range p>N^(2/3), with the strict integer condition
     used in the Lean theorem.
   - Kernel-checked examples: n=27 is rising, winner 7, multiplicity zero;
     multiplicities at rising indices 6 and 20 for winner 7 are 3 and 2.
     Real factorSign is handled by simp/norm_num after kernel-checking the
     two largest-prime-factor values, not by reducing Real equality.

3. Submission/ReciprocalMarkUnweighting.lean
   Imports HighWinnerMarkCoverage; namespace Erdos371.Kloosterman.
   - unmarkedIndexCount counts indices of positive multiplicity.
   - reciprocalIndexMarkWeight p s ab = 1 / multiplicity(index(ab)).
   - sum_reciprocalIndexMarkWeight_fiber: each nonempty fiber contributes
     exactly one, and each empty fiber contributes zero.
   - sum_reciprocalIndexMarkWeight_eq_unmarkedIndexCount: exact finite identity
     for all p,N,s, with no asymptotic assumptions.
   - indexMark_actual_comparison: a mark has index>1, winner p, and its
     indicated actual orientation (p prime).
   - high_winner_multiplicity_pos_iff: for n<N and N^2<p^3, positivity is
     equivalent to index>1, winner p, and that actual orientation.
   - reciprocal_mark_count_eq_actual_count: under p prime and N^2<p^3,
     the reciprocally weighted mark sum is exactly the original comparison
     count over Ico 2 N, with winner p and orientation s.
   - reciprocal_weight_reflection_example: the rise mark (2,3) at p=7 has
     weight 1/3; its reflected fall mark (2,4) has weight 1/2. Hence the
     complete unweighted marked reflection identity cannot simply be reused
     with these weights unchanged.

LIMITS AND STRATEGY AUDIT:
The reciprocal weighting removes multiplicity algebraically, not analytically.
No signed cancellation bound for that weight is proved. It is not an arbitrary
weight on just the retained divisor; it depends on the product's whole fiber.
The existing rectangle/hyperbola equidistribution theorems do not automatically
control it. The sufficient coverage range does not cover all winning primes.
Moreover the existing analytic error is o(p), not o(N/p), and no summed o(N)
error bound over winning primes is established. These are genuine remaining
gaps, so the new exact weighted count is not a proof of Erdős 371.

Before the new coverage lemma, the direct rough-Mobius kernel and the
multiplicative/ergodic reductions were re-examined. No new signed arithmetic
cancellation, full-residue transfer, or natural-endpoint stability estimate
was obtained. The known antisymmetry, parity, and endpoint warnings remain.

## Logarithmic-mass recovery and endpoint-transfer re-audit

No new Lean theorem was obtained in this round. Spec.lean is unchanged and
unresolved; no complete proof or disproof has been submitted.

Revisited reconstruction of the joint prime-factor process from exact total
logarithmic mass and CRT-accessible mixed inclusion moments. The existing
PartitionObstruction, RefinedPartitionObstruction, and StationaryMomentObstruction
already block the abstract recovery step: fixed masses and low-product moment
symmetry do not force symmetry of largest parts. These models are not the
actual prime-factor marginal law and are not counterexamples to Erdos 371.
No extra arithmetic uniqueness theorem for the actual law was proved.

Also reconsidered logarithmic/entropy-style dilation transfer. Replacing a
selected divisible progression at gap p by an unrestricted gap-p average
would still leave the adjacent observable at endpoint N/p. Choosing primes
in a short interval could make those endpoints comparable, but the needed
uniform transfer on that prescribed prime interval is not supplied by the
existing identities. An existential good dilation scale cannot simply be
chosen to land at a prescribed natural endpoint. No natural-density conclusion
or logarithmic-to-natural transfer is being asserted.

The latest genuinely new verified arithmetic results remain the coverage
criterion in BalancedSmoothFactorization/HighWinnerMarkCoverage and the exact
reciprocal-weight count in ReciprocalMarkUnweighting. Cancellation for that
weight, treatment of the complementary prime range, and a summed o(N) bound
remain unproved. No new auxiliary result was substituted for these gaps.

## General packing and separable random-allocation approximation

Spec.lean remains unchanged and unresolved. No signed cancellation has been
claimed. The following new auxiliary modules compile, with saved .olean files;
their checked main theorems use only propext, Classical.choice, and Quot.sound.

- SmoothFactorPacking: packs a positive p-smooth integer m with m²<p^K
  into at most K factors below p; pads to exactly K factors with ones.
- TwoSidedFactorPacking: exact two-sided certificates with losing factors <p
  and winning-cofactor factors <=p. These identify the actual winner; a mere
  product congruence is insufficient outside the two-factor regime.
- PackingCoverageDensity: failure of the K-factor certificate has eventual
  fraction at most 320/K²+epsilon. This is unsigned coverage, not cancellation.
- RandomFactorBins: collision-energy estimate for assigning nonnegative atoms
  of total mass <=1 to K boxes. Atoms <=u-delta imply overflow fraction
  <=1/(K*u*delta).
- RandomFactorProducts: translates the collision estimate to integer products
  via logarithms. Atoms <=N^(u-delta) give small products <=N^u in all but the
  stated fraction of assignments.
- PrimePowerAllocationWeights: assigns distinct whole prime powers to boxes.
  The tuple of box products determines its assignment. The separable weight
  allocationWeight(K,m)=K^(-omega(m)) has product K^(-number of atoms), so all
  assignments together have total weight exactly one. The weight is
  multiplicative on coprime arguments.
- PrimePowerOvershoot: the set of n with some prime-power atom p^v_p(n)>P(n)
  has density zero. Exceptions are covered by bounded smooth numbers and
  integers with a large square divisor; both contributions are controlled.
- PrimeAllocationRetention: defines bounded-box retention for the actual
  atoms of n. If n<=N, all its atoms <=p, and p>=N^v, the loss with box cutoff
  p*N^delta is <=1/(K*v*delta). Divisors inherit the atom bound when their
  parent integer has no prime-power overshoot.
- ComparisonAllocationApproximation: applies retention to the losing neighbor
  and the winning cofactor. For every fixed delta>0 and epsilon>0 a fixed K
  approximates the original comparison sign in mean with eventual error
  <epsilon. All finite error terms are explicit: small indices, overshoot at
  either neighbor, low winning primes, and 2/(K*v*delta).
  density_of_comparisonAllocation_cancellation is CONDITIONAL on the weighted
  signed sum tending to zero for every fixed K>0. That hypothesis is unproved.

The last module's type-level classical-decidability and missing-import issues
were fixed and its printed axiom checks now pass. It does NOT supply the
remaining arithmetic cancellation. The existing unweighted inverse-curve
estimates do not automatically apply to these weights or to the two-sided
product equation, and no summed o(N) estimate over winning primes is known.

## Exact coprime-tuple transport of allocation weights

Two further modules compile and have saved .olean files. Their printed main
axiom checks contain only propext, Classical.choice, and Quot.sound.

1. CoprimeAllocationTuples.lean
   - CoprimeFactorTuple K n b: positive coordinates, pairwise coprime, product n.
   - primeBoxProducts_pairwise_coprime and
     primeBoxProducts_coprimeFactorTuple: every whole-prime-power allocation
     gives such a tuple.
   - A prime divisor of the product lies in a unique coordinate, and its full
     factorization exponent is the exponent in that coordinate.
   - exists_primeAllocation_of_coprimeFactorTuple: converse surjectivity.
     Combined with the earlier injection, this is a genuine bijection.
   - smallCoprimeTuples K M X: a common finite tuple domain, coordinates in
     [1,M], pairwise coprime, and real coordinate bounds <=X.
   - primeAllocationRetention_eq_tuple_sum: for 0<n<=M, the retention is exactly
     the sum over these tuples with product n of the separable product weight.

2. ComparisonTupleExpansion.lean
   - Largest prime factor bounds on a positive product are equivalent to the
     corresponding bounds on every coordinate (strict or non-strict).
   - comparisonAllocationWeight_eq_tuple_sum: exact double tuple-sum formula
     for an actual comparison at 1<n<N. Losing product equals losingNumber(n);
     p times winning-cofactor product equals winningNumber(n).
   - comparison_tuple_prime_bounds: losing entries have P(entry)<p and winning
     cofactor entries have P(entry)<=p.
   - rising_of_tuple_equation / falling_of_tuple_equation: conversely, positive
     tuples with those prime bounds and the respective neighboring-product
     equations identify the actual comparison orientation and winner.

This resolves the change-of-variables issue, not the analytic one. One still
needs a signed estimate for the difference between the two neighboring-product
solution sets with these coefficients. The existing unweighted inverse-curve
bounds give neither this weighted estimate nor its required sum over primes.
Spec.lean remains unchanged, with its original sorry; no settlement is claimed.

## Direct allocation-weight reflection audit

Re-examined the actual signed arithmetic target, the cofactor reciprocity
formulas, and the available inverse-curve estimates. No uniform signed estimate
was obtained. The inverse formulas still impose a prime linear form together
with a distinct smooth linear form. An attempted fetch of the external problem
reference failed because network DNS was unavailable; no external result was
used or claimed.

New verified module: Submission/AllocationReflectionCheck.lean. It compiles,
has a saved .olean, and its printed main axioms are only propext,
Classical.choice, and Quot.sound. This is NOT a disproof of Erdos 371.

- primeAllocationCount K B n counts allocations with integral box bound B.
- primeAllocationRetention_nat_eq_count gives the exact retention as
  count*K^(-omega(n)).
- Kernel-checked counts at K=2, B=14: n=77,66,6,5 have respectively 2,2,4,2
  retained assignments, hence retentions 1/2,1/4,1,1.
- reflectionInflation = log(14/13)/log(78) is STRICTLY POSITIVE and gives
  13*78^reflectionInflation=14, so the example uses allowed positive inflation.
- The rise at n=77 and fall at n=65 both have winner 13. Their losing-side
  factorizations (11,7) and (11,6) are both coprime; they are related by the
  usual reflection b -> 13-b. The equations are 77+1=13*6 and 66-1=13*5.
- comparisonAllocationWeight_reflection_check proves their COMPLETE comparison
  weights (including winning-cofactor retention) are 1/2 and 1/4.
- comparisonAllocation_reflected_pair_not_cancel proves the signed weighted
  pair sum is 1/4, not zero. Thus direct pointwise weight-preserving reflection
  does not follow even after the exact coprime-tuple transport.

The example does not disprove asymptotic cancellation or a more sophisticated
pairing. The missing summed o(N) estimate is still missing. Spec.lean remains
unchanged with its original sorry; no complete proof/disproof has been submitted.

Computation note: Nat.factorization uses padicValNat/Nat.find, so direct kernel
reduction of allocation counts gets stuck. Unfold boxProduct and primePowerAtom
and rewrite <- Nat.primeFactorsList_count_eq before decide +kernel. The finite
counts then verify quickly. Temporary CheckAllocationComputation.lean was removed.

## Uninflated allocation approximation verified

The averaged signed estimate is still unproved. The new unconditional result
removes the artificial positive power inflation from the box cutoff. Four new
modules compile and have saved .olean files; their printed main axiom checks
use only propext, Classical.choice, and Quot.sound.

1. SameIntegerPrimeGap.lean
   - gapLargePrimes N v: primes p>=N^v, p<=N.
   - gapNearbyPrimes N p eta: primes q<p with p<=N^eta*q.
   - sameIntegerPrimeGapEvent N v eta m: such a pair with p*q dividing m.
   - sameIntegerPrimeGapSet indexes this event at m=n+1, n<N.
   - Counts are bounded by N times the reciprocal sum of p*q. A moving prime
     interval bound applies with exponent log(p)/log(N)-eta, uniformly bounded
     below by v/2.
   - sameIntegerPrimeGapSet_eventually_le: for 0<v<=1 and 0<=eta<=v/2,
     eventual exceptional proportion <=128*eta/v^2+epsilon.
   - sameIntegerPrimeGapSet_uniform_rarity: choose a fixed eta>0 for arbitrary
     small upper proportion. This is a ONE-integer divisor estimate, not an
     assertion of independence of neighboring integers.

2. LargeRepeatedAtoms.lean
   - largeRepeatedAtom X n: some prime-power atom of exponent >=2 exceeds X.
   - largeRepeatedAtom_large_square: if B^3<=X, such an atom forces a square
     divisor d^2|n with d>B. Use d=p^floor(e/2) and p^e<=d^3.
   - largeRepeatedAtomSet_ratio_tendsto_zero: for every fixed eta>0, atoms
     exceeding N^eta with repeated exponent have vanishing proportion.
   - divisor_atom_small_or_prime: a divisor's atom is either <=X or just its
     base prime if the parent has no large repeated atom.

3. ComparisonAtomBuffers.lean
   - losing_prime_power_separation: absence of the neighboring log-ratio event
     forces P(loser)*N^eta < winner.
   - prime_divisor_power_separation: absence of the same-integer event forces
     each distinct smaller prime divisor below winner/N^eta.
   - winning_prime_not_dvd_cofactor: no repeated atom above X<winner excludes
     a second occurrence of the winning prime.
   - comparison_atoms_power_buffer: assuming winner>=N^v, eta<=v/2, no adjacent
     near-tie, no large repeated atoms at either neighbor, and no same-integer
     near-tie at the winner, ALL losing and winning-cofactor atoms are bounded
     by winner/N^eta.
   - primeAllocationRetention_buffer_bound and
     comparisonAllocationWeight_zero_loss: at the EXACT winner cutoff, loss
     is <=2/(K*v*eta). No inflation is present.

4. UninflatedAllocationApproximation.lean
   - Finite mean loss <=4/N + low-winner smooth proportion + adjacent near-tie
     proportion +2*repeated-atom proportion +2*same-integer near-tie proportion
     +2/(K*v*eta). Endpoint shifts are included in the 4/N term.
   - comparisonAllocationWeight_zero_uniform_approximation: for every epsilon>0
     there is a FIXED K>0 such that eventually mean(1-W(K,N,0,n))<epsilon.
   - density_of_uninflatedAllocation_cancellation: CONDITIONAL sufficient
     criterion using the signed weighted sums at inflation zero. Its signed
     convergence hypothesis has NOT been proved.

This gives a cleaner compact factor domain for further analysis, but does not
supply cancellation for either product equation, nor a summed o(N) estimate.
The direct reflection audit still applies. Spec.lean has not been modified and
still contains its original sorry. No complete proof/disproof has been submitted.
Temporary CheckPrimeAtomGap.lean was removed. New files have only harmless
unused-variable/unnecessary-sequence linter warnings.

## Unconditional one-box signed limit

New module Submission/SingleBoxCancellation.lean compiles without warnings and
has a saved .olean. Its printed main axioms are only propext, Classical.choice,
and Quot.sound. Spec.lean remains unchanged and unresolved.

- primeAllocationRetention_one: for n!=0, the K=1 retention is precisely the
  indicator n<=X, since the unique box contains every atom.
- comparisonAllocationWeight_one_eq: for n>1, W(1,N,0,n) equals the indicator
  that n+1 is prime. If the winning number is composite, or the winner is n
  rather than n+1, the losing number cannot fit in the single box of size p.
- singleBox_signed_term: on those retained comparisons the sign is +1.
- singleBox_weight_sum_bound: total retained mass <=2+pi(N), with explicit
  treatment of the first two indices.
- singleBox_weight_mean_tendsto_zero and singleBox_signed_cancellation:
  the K=1 unsigned and signed normalized sums both tend to zero, using the
  previously proved density-zero prime count.
- singleBox_mean_loss_tendsto_one: the mean approximation loss at K=1 tends
  to ONE, not zero. Thus the established signed case is much too sparse to
  recover the original comparison density.

This proves one instance of the new signed criterion, not the quantification
over every fixed K>0. No estimate extending the signed limit to the larger K
required by uniform approximation was obtained. In particular the verified
one-box result cannot be substituted for that missing quantification. No
complete proof or disproof has been submitted.

## Averaged cancellation after the one-box case: no extension obtained

Re-examined the K>=2 uninflated sums as prime-weighted shifted divisor sums.
The existing unweighted inverse-curve estimates do not control their moving
factor restrictions and multiplicative coefficients. Reordering the divisor
sum retains a prime linear form coupled to the shifted coefficient; no
applicable uniform estimate was proved or found in the available imports.

The K=1 limit cannot be bootstrapped by positivity or monotonicity: its unsigned
mass tends to zero, whereas the large-K approximation retains nearly all of
the original count. A vanishing bound for the sparse case supplies no signed
control on the added mass. Neither the stronger prime-group energy criterion
nor the total signed criterion was established.

No new Lean theorem was added in this audit. The latest verified analytic
case remains SingleBoxCancellation.lean, explicitly with mean loss tending to
one. Spec.lean remains unchanged with its original sorry. No complete proof
or disproof is available for submission.

## Power-sized lower cutoffs for allocation boxes

Three new modules compile with saved .olean files; printed main axiom checks
contain only propext, Classical.choice, and Quot.sound. Spec.lean is unchanged.

1. PrimeDivisorCountVariance.lean
   - primeDivisorCountIn S n counts selected prime divisors; A is sum_{p in S}1/p.
   - Exact first moment and second-moment upper bound give
     sum_{n<N}(omega_S(n+1)-A)^2 <= N*A+2*A*|S|.
   - For 0<=r<=1 and L<=A/2, the mean of r^omega_S(n+1) is at most
     4/A+8*|S|/(N*A)+r^L.

2. RichPowerPrimeBands.lean
   - Elementary prime-log harmonic bounds give reciprocal mass >=1/4
     in each sufficiently large interval (B,B^2]. Iteration gives J/4
     in (B,B^(2^J)].
   - For any alpha>0 and desired reciprocal mass R, some fixed eta>0 gives
     prime bands S_N contained in [N^eta,N^alpha], with mass >=R and
     |S_N|<=N^alpha+1 eventually.
   - For alpha<1 and 0<=r<1, choose eta sufficiently small to make the
     mean of r^omega_{S_N}(n+1) arbitrarily small, eventually.

3. AllocationSmallBoxes.lean
   - Exact finite allocation avoidance mass for a selected atom set T and
     one box: (1-1/K)^|T|.
   - If all selected primes >=Y, any box below Y avoids those primes.
   - Union bound: smallBoxAllocationMass K Y n <= K*(1-1/K)^omega_S(n).
   - For fixed K>0, a sufficiently small fixed eta>0 makes the mean mass of
     allocations with any box below N^eta arbitrarily small.
   - One harmless unused-variable linter warning remains; all proofs compile.

Temporary CheckPrimeBand.lean and CheckAllocationAvoidance.lean were removed.
These are unsigned structural estimates. They do NOT establish cancellation
of the neighboring product equations. The original conjecture is unresolved.

## Lower box cutoffs transported to the actual comparison weights

Two further modules compile with saved .olean files. Main printed axiom checks
use only propext, Classical.choice, and Quot.sound.

1. ComparisonBoxBands.lean
   - Dividing an integer by a prime outside S preserves its selected-prime
     divisor count, exactly.
   - primeAllocationBandRetention imposes Y<=every box<=X.
   - It is nonnegative, below upper-only retention, and its loss relative to
     upper-only retention is at most smallBoxAllocationMass.
   - comparisonBandAllocationWeight K N eta uses X=winning prime and Y=N^eta
     for both the losing number and the winning cofactor.
   - The product-weight loss is bounded by the sum of the two small-box masses.
   - If S_N lies in [N^eta,N^alpha] and the winning prime exceeds N^alpha,
     the loss is at most K*(r^omega_S(n)+r^omega_S(n+1)), r=1-1/K.
     In particular the cofactor is controlled by the ORIGINAL winning integer;
     no density or average over all cofactors is erroneously substituted.

2. ComparisonBandApproximation.lean
   - The mean loss from adding the lower cutoff is at most
     (2+K)/N + proportion(P(n+1)<=N^alpha)
       +2*K*mean(r^omega_S(n+1)). Endpoint shifts are accounted for.
   - For each FIXED K>0 and epsilon>0, some fixed eta>0 gives eventual
     mean(W_upper-W_band)<epsilon.
   - Combining with uninflated upper approximation: for each epsilon>0,
     fixed K>0 and eta>0 give eventual mean(1-W_band)<epsilon.
   - Harmless unnecessary-sequence and unused-variable warnings only.

This achieves power-sized lower cutoffs on every allocation box without
losing the full comparison mass. It is still an UNSIGNED approximation. No
signed estimate for the retained product equations has been proved. The
conjecture in Spec.lean remains unchanged and unresolved; no submission.

## Exact band-tuple transport and conditional signed criterion

ComparisonBandTuples.lean compiles without warnings, has a saved .olean, and
its main axioms are permitted only.
- bandCoprimeTuples is the common finite coordinate domain with both cutoffs.
- primeAllocationBandRetention_eq_tuple_sum gives exact separable transport.
- comparisonBandAllocationWeight_eq_tuple_sum retains both neighboring-product
  equations, all pairwise-coprimality restrictions, and both box bounds.
- density_of_bandAllocation_cancellation is explicitly CONDITIONAL on the
  signed weighted limit for every fixed K>0 and eta>0. This limit remains
  unproved for the useful K and eta. No new unconditional signed limit was
  obtained from the lower cutoff.

The new lower range does not by itself justify replacing arithmetic weights
by their means, discarding the winning-cofactor equation, or applying an
unweighted inverse-curve estimate. A further Mathlib/import search found no
existing theorem settling the original density or this weighted criterion.

Final audit of this continuation: no signed cancellation theorem extending the
sparse K=1 case was found. The power-sized lower bounds do not uncouple the
winning-cofactor equation, and no valid passage from unweighted modular
inverse estimates to the separable arithmetic weights was established.
All four modules completed in this continuation were rebuilt, with permitted
main axioms only. Spec.lean retains its original SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff
and its original sorry. No proof/disproof has been submitted.

## Prime-inverse scaling audit in the next continuation

Re-examined UpperHalfSmoothSkew before beginning any new prime exponential-sum
formalization. For p near P and q near Q, the inverse-residue interval has
width about N/Q, and the expected count per modulus is about N/P (apart from
prime logarithms). A power saving relative to the full q-range Q is not
therefore automatically o(N/P). Summing absolute per-modulus estimates over
p remains too expensive in the large-product region. No new signed prime-band
estimate was obtained. The external reference fetch again failed DNS.

Also reviewed the dilation/strong-stationarity route. Exact removal of a
small multiplier still samples a divisible progression and changes the
natural endpoint. Restricting selected multipliers to a short relative range
can control endpoint variation only after a suitable common-scale transfer;
no such transfer or entropy theorem was proved here.

## Fixed-marginal strengthening of the finite partition obstruction

Submission/FixedMarginalPartitionPerturbation.lean compiles without warnings,
has a saved .olean, and its main axiom checks use only the permitted axioms.

- kernel(i,j)=weight(i,j)-weight(j,i), from the seven-state partition model.
- Every row and column sum is zero, |kernel|<=2, and its inclusion moment
  vanishes for every pair of observed subsets whose total mass is <=945.
- Its rising mass is -2 and its falling mass is +2.
- exists_biased_coupling_with_fixed_marginal: for ANY strictly positive
  probability marginal mu on these seven states, there exists a strictly
  positive coupling W with EXACTLY that prescribed marginal on both sides,
  and with all low-mass inclusion moments IDENTICAL to those of mu tensor mu,
  but with strictly more falling than rising mass.
- Construction: W(i,j)=mu(i)*mu(j)+epsilon*kernel(i,j), where
  epsilon=(min_i mu(i))^2/4. The positivity and unchanged marginal/moment
  assertions are all proved, not numerically inferred.

This improves the FINITE-model audit: merely fixing an arbitrary positive
marginal on that state space does not restore moment uniqueness. It is NOT
an embedding into the actual continuous prime-factor marginal law, does not
supply an arithmetic counterexample, and is NOT a disproof of Erdős 371.
The independent reference coupling in this theorem can have ties/shared
parts; no arithmetic coprimality or tie-free assertion is added.

No signed arithmetic cancellation or solution of Spec.lean has been obtained.

End-of-continuation status: the new fixed-marginal finite perturbation theorem
was rebuilt successfully. No asymptotic prime-band cancellation, natural
endpoint transfer, or proof/disproof of the actual conjecture was obtained.
Spec.lean is unchanged with its original sorry. No submission was made.

## Fixed lower exponent versus a growing number of boxes

Submission/AllocationBandCountConstraint.lean compiles without warnings, has a
saved .olean, and its main axiom checks are permitted only.
- A positive band retention for n!=0 forces Y^K<=n.
- For 1<n<N and N>1, positive comparisonBandAllocationWeight K N eta n
  forces K*eta<1, using the strictly smaller winning cofactor.
- Thus K*eta>=1 makes the weight zero away from the first two indices; total
  retained mass is at most 2.
- For fixed eta>0 and K(N)->infinity, both the unsigned and signed normalized
  retained sums tend to zero, while the mean approximation loss tends to ONE.

This checks an essential quantifier issue in grouping most boxes to obtain a
weight with base near one. Growing K at fixed eta cannot supply the existing
band approximation: the apparent signed cancellation is just vanishing mass.
It does NOT settle the missing signed case with fixed K and small fixed eta.

## Empty-box tradeoff, including moving lower exponents

Submission/AllocationEmptyBoxTradeoff.lean compiles with a saved .olean and
permitted main axioms only. It sharpens the previous parameter constraint:
- The probability that one prescribed color is empty is exactly
  (1-1/K)^omega(n), including n=0 via the atom-index formulation.
- For Y>1 every band-retained allocation makes that color nonempty. Hence
  bandRetention(K,Y,X,n) <= 1-(1-1/K)^omega(n) <= omega(n)/K.
- Exact selected-prime divisor counting gives
  sum_{n<N} omega(n+1) <= N*primeHarmonic(N).
- For K>0 and N^eta>1, the mean comparison band weight is at most
  2*primeHarmonic(N)/K. The endpoint shift of omega has no extra error,
  since omega(0)=0 and omega(N)>=0.
- Consequently, for arbitrary eventually positive eta(N), if
  primeHarmonic(N)/K(N)->0 (and K(N)>0 eventually), the unsigned and signed
  retained means tend to zero and the mean approximation loss tends to one.

This invalidates the attempted near-constant grouped-weight shortcut while
retaining positive lower cutoffs: in precisely that regime most boxes are
empty, so the band condition discards the comparison mass. Relaxing the
cutoff to allow empty boxes would no longer give the power-sized tuple domain,
and the grouped residual retention would still contain the original moving
prime-factor restriction. No estimate for that remaining signed weight was
proved.

Both modules from this continuation were rebuilt; CheckBandCount.lean was
removed. Spec.lean remains unchanged with its original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No proof or disproof of Erdős 371 is ready, and no submission was made.

## Further direct signed-kernel review

Returned to ReciprocalDiscrepancy, UpperHalfSmoothSkew, and OddCharacterSkew.
The exact opposite-root and odd-character formulas retain the natural endpoint,
but no averaged arithmetic estimate of the needed strength was obtained.
Neither an individual-modulus character bound nor the existing Cauchy energy
estimate supplies the missing signed average over the large prime moduli.
No new theorem was added in this review and no cancellation hypothesis was
promoted to an unconditional result. Spec.lean remains unchanged and unresolved.

## Reflection-contraction review

Rechecked the largest-losing-prime reflection as a possible signed contraction.
PrimeReflection already proves sign reversal, preservation of the winner,
monotonic increase of the loser, and eventual two-periodicity. These facts
are pointwise orbit statements; they do not compare the natural counting
weights of the alternating orbit levels. Noninjectivity remains, and the
verified PrimeReflectionBoundary theorem gives a positive proportion of
endpoint-crossing inputs. No estimate controlling those weighted collision
and boundary terms was obtained, so no signed contraction was asserted.

No new Lean theorem was added in this review. Spec.lean is unchanged with its
original sorry; no proof/disproof is ready for submission.

## Finite information decoupling and product concentration

Two new modules compile without warnings and have saved .olean files:
- Submission/FiniteInformation.lean
- Submission/FiniteProductConcentration.lean
All printed main axiom checks use only propext, Classical.choice, and Quot.sound.
Neither module contains sorry, admit, native_decide, or added axioms.

FiniteInformation introduces finite real-valued probability laws with explicit
nonnegativity and normalization, expectation, relative entropy, product laws,
marginals, and mutual information. It proves:
- Gibbs inequality, with the support condition explicitly required (necessary
  because Real.log is totalized).
- The normalized exponential-tilt identity for relative entropy.
- E_p F <= D(p||q) + log E_q exp(F).
- If E_q exp(tF) <= exp(c*t^2/2), c>0, for every real t, then
  (E_p F)^2 <= 2*c*D(p||q).
- The analogous mutual-information bound for a joint law versus the independent
  product of its actual marginals, under a uniform conditional MGF bound.

FiniteProductConcentration proves:
- Hoeffding's MGF bound for a finite centered variable bounded by B>=0, including
  the degenerate B=0 case, using Real.exp_mul_le_cosh_add_mul_sinh and
  Real.cosh_le_exp_half_sq.
- Exact MGF factorization for finite independent coordinate laws.
- The bound with variance proxy sum_i B_i^2 for coordinate sums.
- Variance proxy 1/m for the average of m>0 centered unit-bounded coordinates.
- average_sq_le_mutualInformation: if the SECOND marginal of a joint law
  P(X,Y) is the independent coordinate product, and G_i(X,Y_i) is centered in
  Y_i for every X and has absolute value at most one, then
    (E_P (sum_i G_i / m))^2 <= 2*I_P(X;Y)/m.
  Independence of X and Y is NOT assumed; their dependence is measured by I.

Scope and remaining gaps:
- This is a genuine finite decoupling tool, not an arithmetic independence or
  entropy-decrement theorem. No estimate I(X_block;Y_prime-band)=o(H/log H)
  has been proved.
- The proposed logarithmic route would also require construction of the joint
  stationary label/residue limit and a justified arithmetic conditional-dilation
  identity, plus a suitable prime-gap symmetry theorem. These are still missing.
- For a fixed stationary process, prime ergodic averages could potentially avoid
  the earlier UNIFORM moving-endpoint low-frequency objection, but would need
  real spectral prime-average limits. No such theorem has been located/proved.
- Even establishing logarithmic symmetry would not prove the target natural
  density. Dilation converts conditional sampling up to N to sampling up to N/p;
  no uniform natural endpoint transfer is available. This gap is not removed by
  the finite information inequalities.

Both new modules were rebuilt successfully. Spec.lean remains unchanged with
its original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No proof/disproof of Erdős 371 is ready, and no submission has been made.

## Finite Shannon entropy and actual finite entropy decrement

Eight new modules compile without warnings, have saved .olean files, and all
printed main axiom checks use only the permitted three axioms:
- FiniteEntropy.lean
- FiniteBlockEntropy.lean
- EntropyScaleSeries.lean
- EntropyDecrement.lean
- StationaryEntropyRecurrence.lean
- StationaryEntropyDecrement.lean
- CyclicResidueEntropy.lean
- FiniteUniformImages.lean

FiniteEntropy:
- Shannon entropy, nonnegativity, pushforward laws and their expectations.
- Entropy decreases under a map and is invariant under an equivalence.
- Mutual information = H(first)+H(second)-H(joint), subadditivity, and the
  upper bounds of mutual information by either marginal entropy.
- Cross-entropy inequality and H(p)<=log(card alphabet).
- Normalized conditional laws, with an explicit harmless default at null atoms.
- Exact disintegration and the Shannon chain rule, including null atoms.

FiniteBlockEntropy:
- Subadditivity for an arbitrary finite family of coordinates.
- Conditional subadditivity, proved using conditional laws and Gibbs inequality.
- Information is unchanged under a bijective relabeling of the second variable.
- block_entropy_decrement: if each coordinate block has entropy at most E and
  information at least I about a shared auxiliary variable Y, then
    H(all blocks) <= H(Y) + number_of_blocks*(E-I).
  All finite distribution hypotheses are explicit.

EntropyScaleSeries:
- Divergence of sum 1/((n+2)*log(n+2)), by Cauchy condensation and harmonic
  comparison (not an assumed analytic fact).
- factorialScale H n = H*((n+1)!)^2, successive ratio (n+2)^2.
- An explicit upper bound log(factorialScale H n) <= C_H*(n+2)*log(n+2).
- Consequently sum 1/log(factorialScale H n) diverges for H>1.

EntropyDecrement:
- Nonnegative decrements from a nonnegative entropy budget are summable when
  the positive errors are summable.
- Therefore decrements are arbitrarily small relative to any divergent
  nonnegative weight sequence.
- factorial_scale_small_information: the explicit recurrence
    E(H_next) <= C*H + (n+2)^2*(E(H)-I(H))
  forces I(H)<epsilon*H/log H at arbitrarily late factorial scales.
- Crucially, exists_factorial_decrement_horizon proves a UNIFORM FINITE horizon,
  chosen solely from the starting entropy budget, C, H0, epsilon. The recurrence
  is needed only within that horizon; no infinite process is required.

StationaryEntropyRecurrence and StationaryEntropyDecrement:
- Block labels are defined by iterating an actual finite probability-preserving
  map S. The auxiliary variable Y intertwines S with a permutation R.
- Exact stationarity and invertible auxiliary shifts supply all blockwise
  entropy and mutual-information hypotheses, proving the recurrence rather than
  merely assuming it.
- stationary_entropy_decrement: the horizon is chosen BEFORE the finite system
  (sample space, law, S, labeling, auxiliary variables). Only the finite set of
  auxiliary variables below that horizon must have log(card)<=C*H and satisfy
  the shift identity. Auxiliary types and permutations can vary with H.

CyclicResidueEntropy:
- Specializes to the uniform law on ZMod N, shift x->x+1, arbitrary finite
  labels, and ACTUAL least-representative residues modulo M.
- If M divides N, the residue map intertwines both cyclic shifts; this is
  proved using ZMod.castHom, not assumed independence.
- cyclic_prime_residue_entropy_decrement uses M(H)=primorial H and Chebyshev's
  proved log(primorial H)<=log(4)*H bound. For fixed H0>1 and epsilon>0 it gives
  a fixed K>0 such that, for EVERY N>0 divisible by
    product_{n<K} primorial(factorialScale H0 n)
  and EVERY finite labeling of ZMod N, some n<K has
    I(label block of length H; n mod primorial H) < epsilon*H/log H.
  Thus the previously wholly missing finite entropy-decrement estimate is now
  proved in this exact cyclic-sampling setting. No limiting process is needed.

FiniteUniformImages:
- Surjective homomorphisms of finite additive groups push the uniform law to
  the uniform law; proved from translation invariance.
- Therefore the modular second marginal of the cyclic label/residue joint law
  is EXACTLY uniform when M divides N.

Remaining work and scope limits:
- Still need CRT/MGF transport from the full residue to a prime-band coordinate
  observable, and the boundary/finite-divisibility conversion to the desired
  noncyclic arithmetic sampling. These have not been asserted as already done.
- Still no prime-ergodic antisymmetric-correlation theorem and no logarithmic
  density-half theorem have been proved here.
- The NATURAL endpoint obstacle is unchanged. Multiplicative invariance after
  conditioning on p|n samples labels up to N/p, not up to N. Finite stationarity
  and the entropy estimate do not give unrestricted natural dilation invariance.
- Considering an entire limiting profile of endpoints t*N only yields controls
  involving t/p; no argument forcing the comparison bias at t=1 was obtained.
  Uniformity on a bounded t-range does not allow t to grow with the selected
  prime scale. No such transfer is silently assumed.

All eight modules were rebuilt successfully. Temporary checks created in this
continuation (CheckFiniteEntropy, CheckEntropyScales, CheckStationaryEntropy,
CheckCyclicEntropy) were removed. Older unrelated check files were left alone.
Spec.lean is unchanged with its original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No proof/disproof of Erdős 371 is ready, and no submission has been made.

## Completed CRT, sampling, prime-count, and natural-average discrepancy transfer

Nine new modules (870 lines total) compile without warnings with saved .olean
files. All printed main axiom checks use only the permitted three axioms:
- ResidueInformationConcentration.lean
- ResidueChoiceDecoupling.lean
- CyclicResidueSampling.lean
- CyclicCorrelationTransfer.lean
- FiniteEndpointTransfer.lean
- CyclicBoundaryTransfer.lean
- BlockPrimeCount.lean
- CyclicPrimeGapTransfer.lean
- NaturalPrimeGapTransfer.lean

ResidueInformationConcentration:
- Uses Mathlib's ZMod.prodEquivPi and proves its coordinates are the actual
  least-representative residues, using preservation of natural casts.
- The full uniform residue modulo M pushes to the independent uniform law on
  any selected pairwise-coprime moduli whose product divides M.
- The resulting MGF/information bound retains I(X;full residue), so no unproved
  data-processing or information-monotonicity step is needed.

ResidueChoiceDecoupling:
- For unit-bounded position arrays F(X,i,j), selection j=-residue_i differs from
  the uniform position average by a centered variable bounded by two.
- Squared expectation of the average selection discrepancy is at most
    8*I(X;full residue)/number_of_selected_moduli.

CyclicResidueSampling:
- Exact identity on ZMod N when p divides N:
    E V(x+val(-residue_p x)) = p*E[1_{residue_p x=0} V(x)].
- The mean uniform position average over j in ZMod p equals E V(x).
- Thus residue selection discrepancy is exactly conditional-minus-unconditional
  cyclic discrepancy. No natural endpoint equality is asserted.

CyclicCorrelationTransfer:
- Explicit block pair arrays for offsets p with 2p<=block length H.
- cyclic_gap_average_sq_le_information bounds the squared prime/modulus-average
  conditional-minus-unconditional pair correlation by 8*I/m.
- Works for arbitrary finite labels and all unit-bounded pair observables C.

FiniteEndpointTransfer and CyclicBoundaryTransfer:
- prefixMean and exact natural endpoint bound
    |mean_N F-mean_M F| <= 2*B*(N-M)/N, for |F|<=B and 0<M<=N.
- Tail agreement and uniform cyclic-to-natural sum identities.
- Exact dilation identity for multiplier-invariant labels:
    p*mean_{n<N} 1_{p|n} C(L n,L(n+p))
      = mean_{m<N/p} C(L m,L(m+1))
  when p divides N. The endpoint is explicitly N/p, NOT N.
- Cyclic versus natural conditioned-gap discrepancy differs by at most
    2*p*(p+1)/N.
- natural_gap_endpoint_error controls rounding to a shorter endpoint by
    2*(p+1)*(N-M)/N.
- stable_cyclic_gap_endpoint_bound explicitly retains N/p after using exact
  multiplier invariance, confirming the previously identified endpoint issue.

BlockPrimeCount:
- Proves 2^n <= centralBinom n <= (2n)^(number of primes <=2n).
- Hence, for H>=8, the number m of primes p with 2p<=H satisfies
    m >= (log 2/8)*H/log H.
  This is proved from central-binomial factorization bounds, not PNT.

CyclicPrimeGapTransfer:
- Combines finite entropy decrement, actual CRT, concentration, sampling, and
  the elementary prime-count lower bound.
- For every finite alphabet, H0>=8, epsilon>0, a fixed K>0 works for every cycle
  length divisible by the product of the relevant primorials and every labeling.
- One factorial scale among n<K works SIMULTANEOUSLY for every unit-bounded pair
  observable C, with prime-average cyclic discrepancy <epsilon in absolute value.

NaturalPrimeGapTransfer:
- Removes the fixed divisibility condition by rounding N to M=Q*floor(N/Q).
- Bounds all rounding and cyclic losses uniformly, by a fixed constant/N.
- natural_prime_gap_transfer is now FULLY PROVED:
  for every finite alphabet A, H0>=8, epsilon>0, there is K>0 such that for every
  sufficiently large N and EVERY label sequence L:N->A (allowed to depend on N),
  some n<K works simultaneously for every |C|<=1, and
    |average_{prime p<=H/2} D_N(p)| < epsilon,
  where H=factorialScale H0 n and
    D_N(p)=p*mean_{j<N}[1_{p|j} C(L j,L(j+p))]
           -mean_{j<N} C(L j,L(j+p)).
  This is an ordinary NATURAL-average DISCREPANCY theorem. It is NOT convergence
  of either correlation separately and is NOT the conjectured density.

Remaining gaps:
- Need to instantiate multiplier-stable finite quantization of the actual
  normalized largest-prime-factor labels and relate the adjacent conditioned
  correlation at N/p to the unconditioned prime-gap correlation at N.
- No cancellation of the latter prime-gap correlation has been proved. Searches
  found no Mathlib Vinogradov prime exponential-sum or prime-ergodic theorem.
- Even logarithmic prime-gap cancellation would still leave the NATURAL endpoint
  obstacle: the proved dilation identity gives N/p. The now-complete discrepancy
  transfer does not identify that average with the adjacent average up to N.
- No logarithmic density-half theorem, natural density-half theorem, or disproof
  has been obtained.

Possible further investigation (NOT proved): averaging gaps k*p over bounded k
could reduce prime-spectral symmetry to an upper bound for primes in short Bohr
arcs, rather than full prime equidistribution. Such an upper bound would itself
need a justified sieve/Diophantine estimate; no uniform estimate is assumed.
Taking k large before selecting the prime scale does not by itself resolve the
order-of-limits issue or the natural endpoint issue.

All nine modules were rebuilt successfully. The four temporary files created
here (CheckResidueChoice, CheckCyclicNatural, CheckPrimeCard, CheckPrimeTransfer)
were removed. Older unrelated check files were left alone.
Spec.lean remains unchanged with its original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No valid settlement is ready, and no submission has been made.

## Actual multiplier-stable prime labels and comparison-sign transfer

Five new modules, 531 lines total, compile without warnings and have saved
.olean files. All printed main axiom checks use only the permitted axioms:
- PrimeLogQuantization.lean
- QuantizedComparisonApproximation.lean
- StableLabelPrimeTransfer.lean
- ShortPrefixQuantization.lean
- ActualPrimeComparisonTransfer.lean

PrimeLogQuantization:
- unitQuantize Q x is the Fin(Q+1) label min(Q, floor(Q*x)).
- Monotonicity, preservation of max, zero below the first threshold, and the
  one-sided error 0 <= x-label/Q < 1/Q for x in [0,1].
- primeQuantLabel Q N n quantizes normalizedPrimeLog N n.
- primeQuantLabel_mul: if N>1, k>0 and k^Q<N, then for EVERY n,
    primeQuantLabel Q N (k*n) = primeQuantLabel Q N n.
  The n=0 case is handled. This is EXACT invariance, not an average assertion.
- Consequently invariance is eventual and uniform over all multipliers k<=B
  for each fixed resolution Q and multiplier bound B.

QuantizedComparisonApproximation:
- orderSkew on ordered labels is +1 above the diagonal, -1 below, 0 on it;
  its absolute value is <=1 and swapping arguments negates it.
- quantFactorSign compares the actual finite prime-factor labels.
- It equals factorSign away from the initial index and the normalized
  near-tie event of width 1/Q.
- Its total absolute error is <=2+2*card(logRatioSet N (1/Q)).
- quantFactorSign_uniform_approximation: for every epsilon>0 there is Q0>0
  such that for all sufficiently large N and EVERY Q>=Q0 the mean absolute
  error is <=epsilon. Quantization ties are controlled by the earlier proved
  near-tie rarity; no negligible-tie assumption is added.

StableLabelPrimeTransfer:
- conditioned_prefix_dilation_error removes the requirement p|N, with error
  <=2*p^2/N. It still has endpoint floor(N/p), not N.
- primeQuantLabel_prime_transfer instantiates natural_prime_gap_transfer for
  the actual labels. For fixed Q, H0>=8 and epsilon>0, some fixed finite horizon
  K works eventually in N, with a selected factorial scale H and
    |average_{prime p<=H/2} [mean_{m<N/p} C(label m,label(m+1))
                           -mean_{m<N} C(label m,label(m+p))]| < epsilon.
  The scale works simultaneously for EVERY unit-bounded pair observable C.
  Every label in this formula uses the same GLOBAL cutoff N.

ShortPrefixQuantization:
- If T<=N<=T^2, the global near-tie event of width 1/Q implies the local
  near-tie event at endpoint T of width 2/Q.
- Hence the global quantized comparison approximates factorSign in mean up
  to T, uniformly in N between T and T^2.
- quantFactorSign_short_prefix_approximation: for epsilon>0, Q0 is chosen
  INDEPENDENTLY of the multiplier bound B. For any B, eventually in N, all
  Q>=Q0 and 0<p<=B satisfy mean_{n<N/p}|factorSign n-quantFactorSign Q N n|
  <=epsilon. Only the eventual endpoint threshold depends on B.
  This resolves the quantifier issue in choosing Q before the entropy horizon.

ActualPrimeComparisonTransfer:
- actual_prime_comparison_transfer is a proved arithmetic statement involving
  the TRUE adjacent comparison sign:
  for H0>=8 and epsilon>0, some fixed Q>0,K>0 work eventually, with a selected
  H=factorialScale H0 n, n<K, and
    |average_{prime p<=H/2} [mean_{m<N/p} factorSign m
        -mean_{m<N} orderSkew(label_Q,N m,label_Q,N(m+p))]| < epsilon.
- density_iff_arbitrarily_fine_quantized_cancellation is an exact reformulation
  of the original conjecture using arbitrarily fine finite-label skew means.
  Its quantifiers include EVERY lower bound Q0; a coarse label with trivial
  zero skew cannot satisfy the reverse implication by itself.

What is still missing:
- No cancellation of the unconditioned prime-gap skew term has been obtained.
- No argument replaces the proved shorter endpoints N/p by N in natural means.
- Therefore the original density theorem, its negation, and even a logarithmic
  density-half theorem remain unproved. The new arithmetic transfer is not
  represented as any of those conclusions.

The five modules were rebuilt successfully. CheckPrimeQuantization.lean was
removed; older unrelated check files were left alone. Spec.lean is unchanged
with its original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No proof/disproof of Erdős 371 is ready, and no submission has been made.

## Uniform auxiliary-gap skew cancellation (continuation)

Four new modules, 629 lines total, compile without warnings and have saved
.olean files. Their printed main axiom checks use only propext,
Classical.choice, and Quot.sound:
- AbelHarmonicSkewKernel.lean
- FiniteRingSkewFourier.lean
- CyclicAuxiliarySkewCancellation.lean
- NaturalAuxiliarySkewCancellation.lean

This continuation attacked the skew-cancellation issue rather than adding
another arithmetic quantization approximation.

AbelHarmonicSkewKernel:
- For 0<=r<1 and |z|<=1, the partial polynomial sum_{k<H} r^k z^k/k
  differs from -log(1-r*z) by an explicit uniformly vanishing remainder.
- The imaginary part of -log(1-r*z) has absolute value <=pi/2.
- The positive coefficient mass tends to -log(1-r), which is arbitrarily
  large as r approaches 1.
- exists_positive_shift_kernel: for each epsilon>0 there is a FINITE
  probability distribution w on nonnegative integers, with w(0)=0, whose
  polynomial sum w(k)z^k has imaginary part <epsilon for EVERY |z|<=1.
  These supporting shifts are arbitrary positive integers, NOT just primes.

FiniteRingSkewFourier:
- Normalized Fourier inversion and Parseval over a finite commutative ring
  carrying a primitive complex additive character. No field assumption is
  required, so this applies directly to ZMod N for arbitrary nonzero N.
- Exact shift-correlation and weighted-shift Fourier identities.
- weighted_skewCorrelation_sq_le: if the imaginary multiplier is <=epsilon,
  the square of the weighted antisymmetric bilinear correlation is at most
  4*epsilon^2 times the two mean-square energies.
- The base gap h is arbitrary. The shifts are k*h, with the auxiliary weights
  w(k); the result is uniform in h.

CyclicAuxiliarySkewCancellation:
- Expands a finite-label pair observable into its indicator correlations.
- An antisymmetric unit-bounded observable on A has weighted cyclic mean
  bounded by epsilon*(card A)^2 under the preceding multiplier hypothesis.
- exists_cyclic_auxiliary_skew_kernel chooses H,w BEFORE the cycle length,
  label sequence, pair observable, and base gap. For every such choice the
  auxiliary-weighted skew correlation is <epsilon.
- Thus averaging AUXILIARY MULTIPLES of prime gaps can be made uniformly
  symmetric without Vinogradov estimates or a prime-ergodic theorem.

NaturalAuxiliarySkewCancellation:
- Removes cyclic wrap-around with the explicit pair-mean error 2*q/N.
- exists_natural_auxiliary_skew_kernel: for each finite A and epsilon>0 there
  are fixed H,w (nonnegative, supported below H, total mass 1, w(0)=0) such
  that for EVERY fixed B, eventually for EVERY label sequence L:N->A,
  EVERY antisymmetric unit-bounded C, and EVERY p<=B,

    |sum_{k<H} w(k) mean_{n<N} C(L(n),L(n+k*p))| < epsilon.

  L may depend on N. The auxiliary kernel is chosen before B.
- conditioned_prefix_dilation_gap records the exact arithmetic identity:
  if q|N and L(q*m)=L(m), then

    q mean_{n<N} 1_{q|n} C(L(n),L(n+q*a))
      = mean_{m<N/q} C(L(m),L(m+a)).

- conditioned_prefix_dilation_gap_error removes q|N with error <=2*q^2/N,
  independent of the auxiliary gap a.

IMPORTANT: what this does NOT prove
- Conditioning only on p|n at gap k*p leaves GAP k after dilation, not gap 1.
- Conditioning on k*p|n instead would give adjacency at N/(k*p), but this
  composite conditioning is NOT supplied by the existing independent-prime
  residue concentration theorem.
- Conditioning on the fixed auxiliary residue modulo k as part of the first
  variable does not fix this: the independent-prime decoupling then leaves
  the unconditioned term STILL conditioned on that residue. After scaling by
  k, the auxiliary smoothing is lost. Do not discard this conditioning.
- The uniform auxiliary-kernel theorem therefore does not prove cancellation
  of the original unweighted prime-gap term, or of the adjacent comparison.
- The natural endpoint N/p remains a separate obstacle.

Additional route audits (not new theorems):
- The narrow library search for Ikehara/Wiener/Tauberian/Vaughan/Vinogradov
  found only the Wiener-Ikehara discussion in PrimesInAP.lean, not an available
  prime exponential-sum or prime-ergodic result.
- Weighting the p-th observable by (B/p)*1_{n<p*X} in a sample up to B*X
  would align the conditioned endpoint with X. But its norm grows as B/p,
  where B bounds the entire entropy-decrement horizon. Choosing the entropy
  error small after B is known creates a quantifier circularity. No uniform
  information estimate resolving this has been proved.
- Fixed-small-prime harmonic stationarity and fixed-residue block independence
  remain unproved. Moving large-prime averages do not imply either one.

All four modules were rebuilt successfully. CheckAbelKernel.lean was removed.
Spec.lean is unchanged with its original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
The original conjecture, its negation, and logarithmic density half remain
unproved in this development. No valid settlement is ready or submitted.

## Exact fixed-multiplier and positive-power invariance still allow natural bias

Six new modules, 783 lines total, compile without warnings and have saved
.olean files. All printed main axiom checks use only propext,
Classical.choice, and Quot.sound:
- ExactMultiplierChirpObstruction.lean
- ExactDilationBias.lean
- FiniteExactDilationBias.lean
- ThreeLabelExactDilationBias.lean
- RadicalExactDilationBias.lean
- ThreeLabelPowerStableBias.lean

These strengthen the earlier APPROXIMATE fixed-multiplier chirp obstruction.
They are auxiliary countermodels, NOT counterexamples to the conjecture.

ExactMultiplierChirpObstruction:
- strippedChirp(t,B,n) multiplies the chirp n^(it) by the conjugate phases
  of all prime powers with p<=B, removing their contribution exactly.
- Its norm is <=1, and it is completely multiplicative.
- strippedChirp_small_multiplier gives EXACT invariance under every positive
  k<=B, at EVERY starting n, including zero.
- The mean stripping cost over 1<=n<=N is at most
    N * sum_{prime p<=B} |chirp(t,p)-1|.
  The proof uses sum_n v_p(n)=v_p(N!)<=N; no unproved average valuation
  estimate or quantitative simultaneous approximation is used.

ExactDilationBias:
- Defines imaginaryBias(f,N) using the adjacent correlation over Icc 1 N.
- Proves the general mean-error bound for two unit-bounded functions and
  the stripping bias error <=4*sum_{p<=B}|chirp(t,p)-1|.
- Uses the earlier countable-torus chirp subsequence to choose, for each B,
  an endpoint N>=max(B,9) retaining imaginary bias >=1/120.
- exists_exact_dilation_stable_biased_family produces N_j->infinity and F_j
  with norm<=1, F_j(k*n)=F_j(n) for ALL 0<k<=j and ALL n, and natural adjacent
  imaginary bias >=1/120 at N_j.

FiniteExactDilationBias:
- Constructs a fixed finite quantizer of the complex closed unit ball by
  compactness, with unit-bounded representatives and uniform approximation.
- Composition preserves all exact multiplier identities.
- exists_finite_exact_dilation_stable_skew_bias has a fixed finite alphabet,
  a fixed unit-bounded antisymmetric pair observable, exact invariance for
  k<=j, and skew bias >=1/240 at every chosen endpoint N_j.

ThreeLabelExactDilationBias:
- pairOrder(a,b) maps a to 0, b to 1, and all other labels to 2.
- Swapping a,b in this projection gives exactly twice the oriented a,b
  transition indicator difference.
- Every finite antisymmetric pair observable is an exact linear combination
  of these THREE-label order-comparison differences.
- Thus some three-label projection detects a uniform fraction of any
  nonzero skew bias. Reversing its order can make that bias negative.
- exists_three_label_exact_dilation_order_bias gives a FIXED THREE-label
  family with exact invariance for every k<=j and order-skew mean <=-delta,
  for a fixed delta>0, at its natural endpoints N_j.
- exists_three_label_exact_dilation_rise_deficit converts this into a rising
  fraction <=1/2-delta (with a rescaled fixed positive delta).

RadicalExactDilationBias:
- radicalChirp retains only one copy of each prime phase above B.
- It is still exactly invariant under k<=B, and now ALSO satisfies
    radicalChirp(t,B,n^r)=radicalChirp(t,B,n) for EVERY r>0.
- It equals strippedChirp unless a prime square p^2, p>B, divides n.
- The already proved large-prime-square count gives a uniform bias-error
  bound by 8 times the convergent reciprocal-square tail above B.
- exists_exact_dilation_and_power_stable_biased_family has both exact
  identities and imaginary bias >=1/240.

ThreeLabelPowerStableBias:
- Provides a reusable three-label projection theorem for any uniformly
  biased unit-bounded complex family, with the projection applied by
  composition so that all existing input identities are preserved.
- MAIN exists_three_label_power_stable_rise_deficit:
  there are delta>0, N_j->infinity, and L_j:N->Fin 3 such that
    * L_j(k*n)=L_j(n) for every 0<k<=j and every n;
    * L_j(n^r)=L_j(n) for every n and every r>0;
    * mean_{1<=n<=N_j} orderSkew(L_j(n),L_j(n+1)) <= -delta;
    * #{1<=n<=N_j : L_j(n)<L_j(n+1)}/N_j <= 1/2-delta/2.

LIMITATIONS / interpretation:
- These are endpoint-dependent auxiliary families, NOT Nat.maxPrimeFac.
- No max-under-multiplication law L(ab)=max(L(a),L(b)) is established for
  the finite label models. Do not claim that they satisfy that law.
- No stability up to a fixed POSITIVE POWER of N_j is established.
- No claim of negligible adjacent ties is established for the three-label
  models. Their order-skew bias itself, not only their ties, is nonzero.
- The new results rule out a natural cancellation theorem based ONLY on
  exact eventual fixed-multiplier invariance, a fixed finite alphabet,
  bounded antisymmetry (or the actual order comparison), and even exact
  positive-power invariance. Additional arithmetic structure is necessary.
- They do not disprove the original conjecture or its logarithmic analogue.

The earlier max-prime reflection and reordered-prime finite obstructions were
also reviewed. No measure-preserving reflection, signed contraction, or
polynomial-range natural-average transfer was obtained. External requests to
erdosproblems.com and GitHub again failed with DNS resolution errors; no new
external result was used.

All six modules were rebuilt successfully. CheckExactChirp.lean and
CheckFiniteBias.lean were removed. Spec.lean remains unchanged with its
original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof of Erdős 371 is ready or submitted.

## Fixed-modulus Abel-prime skew cancellation

Two modules compile without warnings, with main axiom checks using only
propext, Classical.choice, and Quot.sound:
- AbelResiduePrimeDensity.lean
- AbelCyclicPrimeSkew.lean

The first derives, directly from Mathlib's continuous L-series auxiliary
function in PrimesInAP.lean, the fixed-modulus limit
  (s-1) sum_{prime p, p mod q=a} log(p)/p^s
    -> if IsUnit(a) then 1/phi(q) else 0, as s -> 1+.
Higher prime powers are discarded using their summable coefficient/n tail;
nonunit prime residue classes have finite support. The generic positive
summable-tail Abel vanishing lemma is also recorded.

The second sums this limit against any fixed odd real function on ZMod q.
Negation permutes the unit residues, making the limiting weighted sum zero.
It then proves cancellation for every fixed cyclic label process with a real
antisymmetric pair observable, by translating the cycle to show its
correlation is odd in the gap.

LIMITATIONS:
- Weights are (s-1)*log(p)/p^s, not uniform prime weights or log weights 1/p.
- The modulus, process, and observable are fixed before taking s -> 1+.
- There is no uniformity over growing cycles, no irrational-frequency
  estimate, no prime analogue of the uniform auxiliary-integer kernel, and
  no replacement of the natural endpoint N/p by N.
- Thus this supplies only the rational/fixed-periodic part of a prospective
  prime spectral argument. It does not prove the target or its logarithmic
  analogue. Spec.lean remains unchanged and no settlement is submitted.

## Fixed max-multiplicative functions: natural reversal symmetry, and nonuniformity

Five new modules compile without warnings and have saved .olean files:
- FixedPrimeAvoidance.lean
- FixedPrimeAvoidanceApproximation.lean
- FixedPrimeAvoidanceSkew.lean
- FixedMaxMultiplicativeSymmetry.lean
- FixedPrimeApproximationObstruction.lean
All printed main axiom checks use only propext, Classical.choice, Quot.sound.
Namespace Erdos371.FixedPrimeAvoidance. The original target remains unresolved.

Definitions:
- avoid(B,n) is 1 if no prime belonging to the FIXED set B divides n, else 0.
- finiteAvoid(S,n) similarly avoids a finite set S of primes.
- primeCut(B,K) consists of forbidden primes below K.
- reciprocal(B,p) is 1/p on forbidden primes and zero elsewhere.

FixedPrimeAvoidance proves:
- Pointwise domination avoid B <= finiteAvoid(primeCut B K).
- Finite avoidance is periodic and even under reflection through any common
  multiple of its forbidden primes.
- A positive-integer union bound controls total truncation error by N times
  the finite forbidden-prime reciprocal tail. There is no extra prime-count
  error: the number of positive multiples is exactly floor(N/p).
- For summable reciprocal(B), this is bounded by N times the convergent
  infinite-series tail.

FixedPrimeAvoidanceApproximation proves:
- Exact finite-CRT counting discrepancy bounded by the full CRT period.
- Finite-avoidance natural mean is product_{p in S}(1-1/p), bounded above by
  exp(-sum_{p in S}1/p).
- If the forbidden-prime reciprocal sum diverges, a finite truncation can
  have arbitrarily small mean; both the full indicator and truncation error
  are dominated by that truncation. If it converges, the tail union bound
  applies instead.
- MAIN fixed_avoidance_L1_approximation:
    for every FIXED B and epsilon>0 there exists K such that eventually N,
    mean_{n<N}|avoid(B,n)-finiteAvoid(primeCut(B,K),n)| < epsilon.
  K depends on B. No uniformity over moving forbidden sets is asserted.

FixedPrimeAvoidanceSkew proves:
- Finite-avoidance pair skew has exactly zero mean over a common CRT period.
- Quantitative perturbation bound for two unit-bounded indicator pairs:
  total skew error <=2*L1_error_first+2*L1_error_second+2.
- MAIN fixed_avoidance_skew_tendsto:
    mean_{n<N}[avoid(B,n)avoid(C,n+1)-avoid(C,n)avoid(B,n+1)] ->0
  for any two FIXED forbidden prime sets B,C (not necessarily nested).

FixedMaxMultiplicativeSymmetry proves:
- For L:N->N with L(1)=0 and L(ab)=max(L(a),L(b)) for positive a,b,
  L(n)<=t iff every prime divisor p of n has L(p)<=t, for n>0.
  Thus each threshold indicator is a fixed prime-avoidance indicator away
  from n=0.
- Exact level indicators are differences of successive threshold indicators.
- Reversal is preserved by these linear combinations and finite exceptions.
- MAIN fixed_max_multiplicative_skew_tendsto:
  if L has a FIXED FINITE RANGE, then for every real antisymmetric C,
    mean_{n<N} C(L(n),L(n+1)) ->0.
  The observable is automatically bounded on the finite range; no external
  bound is needed. There is NO uniformity in L or its prime cutoffs.

FixedPrimeApproximationObstruction proves:
- For every candidate truncation K, the fixed set B={p:K<p} has an empty
  primeCut(B,K), but avoid(B) has natural mean zero (bounded smoothness).
  Thus the finite-prime L1 truncation error tends to ONE.
- MAIN no_uniform_finite_prime_approximation rules out a K working for all B
  even with tolerance 1/2 and with the eventual endpoint allowed to depend
  on B. This disproves only uniform finite-prime APPROXIMATION, not uniform
  skew cancellation or the original conjecture.
- MAIN fixed_primeQuantLabel_top_density:
  for every FIXED scale parameter X>1 and Q, primeQuantLabel(Q,X,n) equals
  its top value Q on a natural-density-one set. Freezing X therefore gives
  a degenerate one-label asymptotic, unlike the arithmetic diagonal X=N.

This closes the previously mentioned fixed-function max-law symmetry fact
with an explicit proof, but it does not bridge the moving-cutoff limit. In
particular, the theorem cannot simply be applied to L=primeQuantLabel Q N
and then evaluated at the same N. The established nonuniform approximation
obstruction explains why that proof route has no such upgrade as written.
The unconditioned prime-gap skew cancellation and natural endpoint N/p in
ActualPrimeComparisonTransfer remain unresolved. No logarithmic-density-half
claim is made either. Spec.lean remains unchanged with its original sorry
and SHA256 34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.

## Sparse neighboring-threshold reduction, with a Q-uniform endpoint error

Four new modules compile without warnings and have saved .olean files:
- AdjacentThresholdExpansion.lean
- PowerThresholdNeighborSkew.lean
- NeighborSmoothCancellationCriterion.lean
- SmoothSkewSignExamples.lean
All printed main axiom checks use only propext, Classical.choice, Quot.sound.
These are reductions and finite checks, NOT a proof or disproof of the target.

AdjacentThresholdExpansion:
- thresholdStep(t,a)=1_{a<=t}.
- adjacentThresholdSkew(t,a,b)=F_t(a)F_{t+1}(b)-F_t(b)F_{t+1}(a).
- Exact sparse identity, for a,b<=Q:
    orderSkew(a,b) = sum_{t<Q} adjacentThresholdSkew(t,a,b).
  Thus only NEIGHBORING thresholds are needed, rather than Q^2 arbitrary
  pairs of indicator functions.
- quantThreshold and quantNeighborSkew specialize this to primeQuantLabel.
- Proves the exact pointwise and natural-mean expansions of quantFactorSign.
- Records primeQuantLabel_mul_max for all positive inputs, and multiplicativity
  of each zero-one quantThreshold (again for positive inputs).
- density_iff_arbitrarily_fine_neighbor_cancellation is an exact reformulation
  of the previously proved quantized criterion, retaining arbitrarily fine Q.

PowerThresholdNeighborSkew:
- strictPowerCutoff(Q,N,t)=ceil(N^((t+1)/Q))-1.
- For N>1 and t<Q, quantThreshold(Q,N,t,n) is EXACTLY the indicator
    P(n)<=strictPowerCutoff(Q,N,t),
  including n=0. The strict inequality and ceiling-minus-one are important.
- The cutoff is >=1 for Q>0,N>1.
- The top threshold t=Q is constantly one; its neighboring skew telescopes.
- Interior neighboring skew sums equal the previously defined
  smoothCutoffSkew of the two adjacent power cutoffs, minus the single
  quantNeighborSkew endpoint value at n=N. No arithmetic cancellation used.

NeighborSmoothCancellationCriterion:
- neighborSmoothMean(Q,N) is the sum of smoothCutoffSkew(B_t,B_{t+1},N)/N
  over 0<=t<Q-1, with the above moving power cutoffs.
- Exact endpoint identity:
    sum_{n<N} quantFactorSign(Q,N,n)
      = sum_{t<Q-1} smoothCutoffSkew(B_t,B_{t+1},N)
        +1-quantThreshold(Q,N,Q-1,N+1)-quantFactorSign(Q,N,N).
- The final correction has absolute value <=1, independently of Q.
- MAIN quantized_neighborSmooth_error:
    |prefixMean_N(quantFactorSign(Q,N))-neighborSmoothMean(Q,N)| <=1/N
  for EVERY Q>0,N>1. In particular the endpoint error is uniform in the
  number of bins; it is not an accumulated O(Q/N) error.
- MAIN density_iff_fine_neighbor_smooth_cancellation is the exact equivalent
  criterion with neighborSmoothMean and arbitrarily fine Q.
- density_of_neighboring_smooth_skew_cancellation gives a sufficient
  condition: for arbitrarily large fixed Q, every interior neighboring pair
  has zero natural-mean skew along its MOVING power cutoffs. Those arithmetic
  hypotheses remain unproved. Fixed-cutoff symmetry cannot replace them.

SmoothSkewSignExamples:
- Converts smoothCutoffSkew into the difference of two finite pair counts.
- Kernel-checked examples:
    smoothCutoffSkew(5,7,6)=1 and smoothCutoffSkew(5,7,14)=-1.
  Hence there is no uniform FINITE sign even for one fixed pair of ordered
  natural smoothness cutoffs. This does not refute an eventual or asymptotic
  statement. The larger diagnostic checks were not used in any proof.

The actual arithmetic obstruction is still present in each smooth-cutoff
skew: the earlier exact Mobius/prime-band reciprocal-discrepancy kernels
retain their natural prefix restrictions. Existing unsigned sieve bounds
and unweighted inverse-curve discrepancies do not supply signed cancellation
of these kernels. The entropy/prime-gap route also still retains N/p.
No natural- or logarithmic-density-half theorem has been obtained here.
Spec.lean is unchanged with its original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.

## Size-sensitive inverse-rectangle refinement

New module SizeSensitiveInverseRectangles.lean imports SignedInverseRectangles,
compiles without warnings, and has a saved .olean. All four printed main axiom
checks use only propext, Classical.choice, Quot.sound. This is an auxiliary
finite estimate, NOT a solution of Erdős 371.

The earlier smoothing proof replaced both set cardinalities by the full
field size. Keeping them proves:
- smoothedIndicator_fourier_product_size_le:
    FourierL1(smoothed A)*FourierL1(smoothed B)
      <= sqrt(card A * card B)/card J.
- inverseRectangleCount_size_bound: the earlier error cost q/card J is
  replaced by sqrt(card A * card B)/card J, with the same explicit
  translation smoothing errors.
- signed_rectangle_size_bound, for L,M<=p and 0<H<=p:
    signedIntervalDiscrepancy(p,s,L,M)
      <= 4H/p + (3/p)^(1/4)*sqrt(LM)/H.
- signed_rectangle_difference_size_bound: the two main terms cancel exactly,
    |count(true)-count(false)|/p
      <= 8H/p + 2*(3/p)^(1/4)*sqrt(LM)/H.
- signed_rectangle_difference_optimized, for p>=3:
    |count(true)-count(false)|
      <= 10*sqrt(p*(3/p)^(1/4)*sqrt(LM)) + 8.
  The proof uses H=max(1,ceil(sqrt(p*(3/p)^(1/4)*sqrt(LM)))) and verifies
  H<=p and the rounding error. The actual Lean statement uses nested square
  roots, not real-power notation.

Scale audit (algebraic interpretation, not an additional arithmetic theorem):
The optimized error has size p^(3/8)*(LM)^(1/4). Relative to the expected
rectangle count LM/p, a power saving from this estimate requires
LM >> p^(11/6). For rectangles with LM about N this only reaches
p << N^(6/11), not all p<N^(1-delta). Moreover the theorem is for unweighted
inverse rectangles. It does not control prime/rough-Mobius weights, does not
remove divisor-mark multiplicities, and does not give a signed estimate
summed over moduli. No bilinear prime-weighted estimate was obtained in
this review. In particular it cannot be inserted as o(N) in the moving
smooth-cutoff kernel without further arguments.

The sparse neighboring-cutoff criterion and the entropy transfer still have
the same missing arithmetic cancellation. Spec.lean remains unchanged with
its original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof is ready to submit.

## Direct upper-half prime-kernel review

Re-examined CommonEndpointPrimeSkew, PrimeBandProgressions, and
OddCharacterSkew against the newer neighboring-threshold criterion. The
common-endpoint identity already has only a single bounded endpoint error;
there is no missing per-prime endpoint cancellation to recover. All even
characters cancel exactly. The remaining sum is over odd characters with
modulus in the moving prime band and prime endpoints depending on the
cofactor. Neither fixed-modulus Abel limits nor unweighted inverse-rectangle
bounds estimate this growing-modulus, prime-weighted hyperbolic sum.

Also reviewed the full max-multiplicative symmetry result, stationary
symmetry, and the prime-weighted collision criterion. None supplies the
missing uniform reversal. Fixed-function approximation cannot be evaluated
on the moving diagonal, and the energy criterion still needs signed
collision cancellation rather than an unsigned sieve bound.

A search of the available Mathlib and FormalConjecturesForMathlib sources
found no applicable Burgess, large-sieve, Vinogradov prime exponential-sum,
or smooth-number-in-growing-progressions theorem. No new estimate was
proved in this review, and no conditional reduction is being treated as a
solution. No development Lean file or Spec.lean was changed in this round.
The target remains unresolved with its original sorry.

## Global prime-kernel endpoint perturbation and dyadic rectangularization

Two new modules compile without warnings and have saved .olean files:
- PrimeSkewEndpointPerturbation.lean
- DyadicPrimeSkewRectangles.lean
All printed main axiom checks use only propext, Classical.choice, Quot.sound.
These are unconditional finite approximations for the ACTUAL upper-half
smooth-cutoff kernel, not a proof of its cancellation or of Erdős 371.

PrimeSkewEndpointPerturbation:
- endpointTriples (private) indexes prime p, positive cofactor b, and prime q
  with q>C, q<=F(b), and p | bq-1 or p | bq+1.
- If all p>B, C>=B>=2, bF(b)<=M, and M+1<=B^2, then bq determines the entire
  triple at a fixed orientation. Uniqueness is applied to q | bq and to
  p | bq-1 or p | bq+1. Positivity of the subtracted neighbor is checked.
- Enlarging endpoints from floor(N/b) to F(b), where floor(N/b)<=F(b), adds
  at most M-N triples IN TOTAL per orientation. The overhang injects into
  the single interval (N,M]; there is no error per prime/cofactor block.
- MAIN cutoffPrimeSkew_endpoint_bound: the signed error is <=M-N, not twice
  this amount, since each of its two orientation increments lies in [0,M-N].
- Specializes directly to commonEndpointPrimeSkew.
- For a rounding map r with 0<r(b)<=b and bN<=M*r(b), F(b)=floor(N/r(b)) is
  admissible. roundedPrimeSkew groups cofactors by r(b), retaining the actual
  finite fiber and a constant prime endpoint within each block.
- MAIN smoothCutoffSkew_rounding_bound: the smooth skew and the rounded prime
  sum differ by at most M-N+1, including the original endpoint correction.
- cofactorSetOppositePrimeSkew_characters gives the exact odd-character
  factorization for an arbitrary positive cofactor block at a fixed endpoint.

DyadicPrimeSkewRectangles:
- step(k,b)=2^(floor(log_2 b)-k), with natural subtraction in the exponent.
- round(k,b)=floor(b/step)*step.
- Proves positivity for b>0, round<=b, and the finite relative estimate
    2^k*b <= (2^k+1)*round(k,b).
- The rounding is monotone, and its fibers are intervals.
- The number of nonempty blocks on [1,A] is at most
    (floor(log_2 A)+1)*2^(k+1).
- Choosing M=N+floor(N/2^k)+1 proves the required cross-multiplied error bound.
- MAIN smoothCutoffSkew_dyadic_rounding_ratio, for N>0, C>=B>=2 and
  N+floor(N/2^k)+2<=B^2:
    |smoothCutoffSkew(B,C,N)-roundedPrimeSkew(...,round(k,...))|/N
      <= 1/2^k + 2/N.
  This is uniform over ALL primes and cofactor blocks in the sum.
- roundedOddPrimeSkew is the exact sum over blocks and prime moduli of
    (2/phi(p))*sum_{chi odd}
       (sum_{b in block} chi(b))*(sum_{C<q<=N/d, q prime} chi(q)).
  roundedPrimeSkew_characters proves equality with the real rounded sum.
- MAIN smoothCutoffSkew_odd_rectangles_ratio gives the same uniform bound
  directly against this complex odd-character rectangular expansion.

This removes the hyperbolic endpoint as a separate geometric difficulty in
this upper-half regime: k can be fixed large for a prescribed tolerance,
and the remaining number of rectangular blocks grows only logarithmically
with N. It does NOT estimate those prime-weighted rectangular blocks, nor
justify applying a fixed-modulus limit to their growing moduli. The sum over
odd characters and prime moduli still needs genuinely signed cancellation.
The square-root hypothesis remains essential; no claim covers the lower
smoothness cutoffs. The N/p endpoint in the entropy transfer is unrelated
and remains unresolved.

No temporary check file from this round remains. Spec.lean is unchanged
with its original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof is ready to submit.

## Logarithmic-divisor identities reviewed against the rectangular kernel

Reviewed whether the von Mangoldt divisor identity and deterministic total
logarithmic factor mass yield the cancellation needed in the new dyadic
rectangles. They give weighted marginal/cut-flow identities, but not the
ordered prime-band correlation. The existing fixed-marginal partition
perturbation already shows that symmetric low-product inclusion moments,
fixed marginals, and total factor-mass conservation alone do not force
largest-part comparison balance. No implication from these identities to
the new prime-weighted rectangular sum was obtained.

Revisited the prime-winner energy route as well. Its exact increment and
collision formulas continue to retain signed cross terms. The finite
large-prime flow cycle and the earlier pairing obstructions preclude the
simplest acyclicity or exact-label-pairing arguments. No new signed energy
bound was proved. No Lean development file or Spec.lean changed in this
review; the original conjecture remains unresolved.

## Uniform Mangoldt replacement of the dyadic prime kernel

PrimePowerKernelReplacement.lean now compiles, with all six printed main
axiom checks using only propext, Classical.choice, Quot.sound.

- mangoldtPrimeWeight(q)=Lambda(q)/log(q) splits exactly into the prime
  indicator plus a nonnegative properPrimePowerWeight.
- The reciprocal proper-prime-power weights are summable, using Mathlib's
  von Mangoldt nonprime summability in the sole residue class modulo 1.
- primePowerKernelTail(C) is nonnegative and tends to zero as C tends to
  infinity.
- weightedOppositeKernel_bounds: under the upper-half hypotheses, any
  nonnegative q-weight gives an orientation count at most
    M * sum_{C<q<=M} w(q)/q.
  q need not be prime. Uniqueness of the large neighboring prime p and the
  bound on the number of cofactors b eliminate any modulus/block losses.
- mangoldtCutoffSkew_prime_error bounds the SIGNED replacement error by
  M*primePowerKernelTail(C), with no factor two.
- dyadicMangoldtSkew_prime_ratio gives uniform normalized error at most
  3*primePowerKernelTail(C), even with a varying grid precision k.
- smoothCutoffSkew_mangoldt_rectangles_ratio combines the endpoint and
  prime-power errors:
    |smoothCutoffSkew-dyadicMangoldtSkew|/N
      <= 2^(-k)+2/N+3*primePowerKernelTail(C).
- dyadicMangoldtSkew_replacement_tendsto gives the corresponding limit for
  arbitrary moving cutoffs and precision under eventual upper-half bounds.

The only final compile issue was an absolute-value orientation in the
triangle inequality; this has been fixed explicitly in the replacement
bound hypothesis. CheckMangoldt.lean has been removed. There is still NO
estimate proving cancellation of dyadicMangoldtSkew itself. Spec.lean is
unchanged, and the conjecture is not settled.

## Post-replacement endpoint and cancellation review

Rechecked the proposal of restricting entropy-transfer primes to a short
multiplicative interval. Even assuming the corresponding transfer, it only
makes the selected N/p endpoints comparable to each other. The entropy scale
is selected after N is fixed, and cannot be prescribed to reach an arbitrary
target endpoint. This repeats, rather than resolves, the earlier endpoint
obstruction. Changing the sampling length separately at each entropy scale
would change the probability law in the recurrence and is not justified by
pointwise multiplier stability or by one-point smooth-number asymptotics.

The Mangoldt replacement supplies no estimate for the remaining signed
odd-character sums at growing moduli. Fixed-modulus limits cannot be applied
diagonally, and bounding the two orientations separately loses the required
cancellation. No complete proof or disproof was obtained in this continuation.

## Signed short-divisor cancellation in the actual Mangoldt kernel

Four new modules were developed in this continuation:
- OppositeProgressionWeights.lean
- VaughanArithmetic.lean
- ShortDivisorPrimeKernel.lean
- VaughanPrimeKernel.lean

Their main axiom checks use only propext, Classical.choice, Quot.sound.
Unlike a purely formal reformulation, this proves natural-scale cancellation
of the two SHORT-divisor terms in the actual upper-half prime kernel.
It does NOT estimate the long-divisor term or settle the conjecture.

OppositeProgressionWeights:
- oppositeProgressionSign(p,a,v) is zero at v=0, otherwise the difference
  of the indicators p | av-1 and p | av+1.
- For positive p,a its sum on [1,X] has absolute value <=2, uniformly in
  p,a,X. Uses the existing bilinear discrepancy <=1 plus an endpoint;
  the a=1 case is an explicit telescoping identity. No primality needed.
- Abel summation: if all unweighted prefix sums are bounded by K and w is
  monotone OR antitone on (L,X], with 0<=w<=W there, then
    |sum_{L<v<=X} w(v)g(v)| <=3*K*W.
- Thus opposite progressions with such weights have bound 6*W, independent
  of interval length, modulus, and coefficient.

VaughanArithmetic:
- arithmeticTruncate(U,f) is f on n<=U and zero elsewhere.
- Exact convolution identity (mu and zeta are Dirichlet-convolution objects):
    Lambda = Lambda_{<=V} + mu_{<=U}*log
      - mu_{<=U}*Lambda_{<=V}*zeta
      + mu_{>U}*Lambda_{>V}*zeta.
- truncated_convolution_interval reindexes a weighted convolution exactly:
    sum_{C<q<=X} (f_{<=U}*g)(q) H(q)
      = sum_{1<=u<=U} f(u) sum_{C/u<v<=X/u} g(v) H(uv).
- The convolution of functions truncated at U and V is supported at UV.

ShortDivisorPrimeKernel:
- signedWeightedKernel is the difference of the existing weightedOppositeKernel
  orientations. normalizedArithmeticKernel(f) uses weight f(q)/log(q).
- shortLogPrimeKernel is this kernel for mu_{<=U}*log.
- The exact expansion retains mu(u) outside the opposite progression, with
  weight log(v)/log(uv). On uv>C>=1 this is nonnegative, <=1, and monotone.
- MAIN finite bound:
    |shortLogPrimeKernel| <=6*card(P)*card(S)*U.
- A reusable prime/cofactor convergence lemma: if C(N)->infinity, P(N)
  contains only primes <=C(N), and |K(N)|<=A*card(P(N))*floor(N/(C(N)+1))
  for fixed nonnegative A, then K(N)/N->0. Uses the previously proved
  prime-count sublinearity, not a new PNT assumption.
- MAIN shortLogPrimeKernel_tendsto: fixed U gives o(N), with S=[1,N/(C+1)],
  uniformly over ALL endpoints F(N,b). No square-root condition is needed
  for this particular short-term estimate.

VaughanPrimeKernel:
- shortZetaPrimeKernel(U,f) is the normalized kernel of f_{<=U}*zeta.
- Its weight 1/log(uv) is nonnegative, <=2, and antitone for uv>C>=1.
- MAIN finite bound:
    |shortZetaPrimeKernel| <=12*card(P)*card(S)*sum_{u<=U}|f(u)|.
  Fixed U,f therefore gives o(N) in the same prime/cofactor regime.
- vaughanLongFunction(U,V)=mu_{>U}*Lambda_{>V}*zeta.
- mangoldtKernel_vaughan_decomposition is exact when C>=V:
    Mangoldt kernel = shortLog kernel - shortZeta correction + long kernel.
  The correction coefficient is mu_{<=U}*Lambda_{<=V}, supported at UV;
  the direct Lambda_{<=V} term is identically zero above C.
- MAIN mangoldtKernel_vaughan_remainder_tendsto: for every fixed U,V,
  (Mangoldt kernel - long kernel)/N tends to zero. The endpoints F may vary
  arbitrarily, and prime sets P(N) need only be contained in primes <=C(N).
- dyadicVaughanLongKernel instantiates the ACTUAL prime band, cofactor set,
  and dyadically rounded endpoints. Its remainder theorem allows variable k.
- MAIN smoothCutoffSkew_vaughan_approximation: if C(N)->infinity and eventually
  C>=B>=2, N+floor(N/2^k)+2<=B^2, then for fixed U,V and every epsilon>0,
  eventually
    |smoothCutoffSkew(B,C,N)-dyadicVaughanLongKernel(U,V,B,C,N,k)|/N
      <=2^(-k)+epsilon.
  This combines genuine short-term cancellation with the previously checked
  global rounding and proper-prime-power tail estimates.

Remaining gap: no signed estimate for the long-divisor (Type II) kernel.
Taking absolute values of its coefficients does not supply the missing
cancellation; it has ordinary composite support, unlike the summable
proper-prime-power replacement error. The growing prime moduli remain in
this kernel. The upper-half restriction also remains for the approximation
of the original smooth skew; nothing here settles the lower cutoff regime.
No natural-density proof or counterexample has been obtained. Spec.lean is
unchanged with its original sorry. CheckTypeI.lean has been removed.

## Long Vaughan coefficients: the absolute-tail route is obstructed

VaughanLongCoefficients.lean compiles cleanly; its three main axiom checks
use only propext, Classical.choice, Quot.sound.

- truncated_convolution_apply_rough: if U>=1 and minFac(q)>U, the only
  divisor of q <=U is 1, so (f_{<=U}*g)(q)=f(1)g(q).
- MAIN vaughanLongFunction_rough: for U,V>=1, q>0, and
  minFac(q)>max(U,V), the long Vaughan coefficient is exactly
    vaughanLongFunction(U,V,q)=Lambda(q)-log(q).
- MAIN vaughanLongFunction_semiprime: for distinct primes r,s both larger
  than max(U,V), the coefficient normalized by log(rs) is exactly -1.
- MAIN vaughanLongFunction_not_abs_reciprocal_summable:
    NOT Summable (q -> |vaughanLongFunction(U,V,q)/log(q)|/q).
  Proof fixes one prime r>max(U,V), restricts to the injective subsequence
  q=r*s, and obtains the divergent reciprocal-prime series for large prime s.

This is an obstruction to reusing the summable proper-prime-power-tail
argument, NOT a counterexample to Erdős 371 and NOT a signed kernel bound.
The long term has substantial ordinary-composite support. Its required
cancellation across the two residue orientations and growing prime moduli
remains unproved. No lower-cutoff cancellation or natural-endpoint transfer
was obtained. Spec.lean is unchanged with its original sorry. The temporary
CheckLongKernel.lean file has been removed.

## Full-linear modulus cutoff, with a justified subpower diagonal

Two new modules compile cleanly with permitted main axioms only:
- FullLinearRoughCutoff.lean
- DiagonalFullRoughCutoff.lean

The complementary-divisor review did not remove the parity-dependent
coefficient or the input-dependent remaining least prime factor. However,
it led to a stronger unconditional estimate on the small-modulus side:
ALL rough moduli up to N can be removed for a suitably chosen growing
subpower roughness cutoff. The former cutoff was N/log(N)^2.

FullLinearRoughCutoff:
- n.divisors.card <=2^(length n.primeFactorsList), proved by induction on
  a list of prime factors and the cardinality bound for finset products.
- If B>=1, n>0, minFac(n)>B, and n<=(B+1)^K, the prime-factor list has
  length <=K, since every factor is >=B+1. Thus tau(n)<=2^K.
- MAIN roughSmallDivisorSum_bounded_factor_length:
    ||sum_{n<N} roughSmallDivisorSum(B,D,n+1)||
      <=(2^K+1)*roughNumberCount(B,D+1),
  assuming D<=(B+1)^K. This uses the prior per-modulus signed periodic
  discrepancy bound; the sampling endpoint N is arbitrary in this lemma.
- MAIN roughSmallDivisorSum_full_linear_tendsto: for fixed K, B(N)->infinity,
  and eventually N<=(B(N)+1)^K, the small-divisor sum with D=N, divided
  by N, tends to zero. Uses the established uniform density-zero bound for
  growing rough-number cutoffs.

DiagonalFullRoughCutoff:
- rootRoughCutoff(k,N)=ceil(N^(1/(k+1))). Its (k+1)-st power is >=N, and
  it tends to infinity for fixed k.
- Each fixed k therefore gives full-linear small-modulus cancellation.
- Eventually log(rootRoughCutoff(k,N)+1)/log N <=2/(k+1).
- MAIN exists_subpower_full_linear_rough_cutoff constructs B(N) with
    B(N)->infinity,
    log(B(N)+1)/log N ->0,
    sum_{n<N} roughSmallDivisorSum(B(N),N,n+1)/N ->0.
  The diagonal is JUSTIFIED: K(N)=Nat.findGreatest(P(N),N), where P enforces
  simultaneously K<=rootRoughCutoff(K,N), the logarithmic-ratio bound, and
  the normalized small-modulus norm bound <=1/(K+1). Every fixed K is
  eventually admissible, hence K(N)->infinity, and B(N) is the selected root.
  No fixed-function limit is being interchanged with an uncontrolled diagonal.
- MAIN density_iff_full_linear_rough_mixed_tail assumes the two verified
  properties of B and gives the exact density criterion with cutoff D=N.
  Uses the existing Alladi identity, subpower smooth-number sparsity, and
  the uniform one-sided endpoint estimate.
- exists_full_linear_rough_tail_criterion packages the resulting B and the
  equivalence for the original conjecture.

The remaining rough mixed-divisor tail has d>N. Its convergence is NOT
proved. Complementing its divisors does not permit reusing the new small
modulus estimate: the parity coefficient and the least factor of the
complement depend on the input n. The new estimate applies to the original
orientedDivisorTerm, not to arbitrary n-dependent weights. No claimed
settlement follows. Spec.lean is unchanged with its original sorry, and
CheckFullCutoff.lean has been removed.

## Superlinear small-modulus cutoff and sublinear complements

SuperlinearRoughCutoff.lean compiles without warnings; its four main axiom
checks use only propext, Classical.choice, Quot.sound.

- roughSmallDivisorSum_fixed_multiple_tendsto extends the bounded-factor-
  length estimate to D=H*N for fixed positive H. The rough count is evaluated
  at H*N and normalized back by N; the factor H is explicitly retained.
- rootRoughCutoff_multiple_tendsto: for fixed k, B=ceil(N^(1/(k+1))) and
  D=(k+1)*N give a negligible normalized small-modulus sum. Eventually
  D<=(B+1)^(2*(k+1)), providing the fixed factor-length bound.
- MAIN exists_subpower_superlinear_rough_cutoff chooses B(N),H(N) with
    B(N)->infinity, H(N)->infinity,
    log(B(N)+1)/log N ->0,
    eventually H(N)<=B(N)+1,
    sum_{n<N} roughSmallDivisorSum(B(N),H(N)*N,n+1)/N ->0.
  Uses another explicitly constrained Nat.findGreatest diagonal; the
  selected index controls both the root exponent and the multiplier.
- density_iff_rough_mixed_tail_of_small_and_subpower is the general exact
  criterion for ANY modulus-cutoff D satisfying the proved small-sum limit.
- MAIN exists_superlinear_rough_tail_criterion gives the original density
  conjecture equivalently as cancellation of the remaining rough mixed tail
  with d>H(N)*N. This is a criterion, not a proof of that cancellation.
- superlinear_divisor_complement_bound: if R<=N*(N+1), d|R, N>0 and H*N<d,
  then H*(R/d)<=N+1.
- MAIN superlinear_divisor_complement_ratio_tendsto: along H(N)->infinity,
  any such complementary divisors satisfy (R(N)/d(N))/N ->0.

The complement range is now o(N), but the arithmetic obstruction remains:
complementation introduces input-dependent parity and least-factor weights.
The existing signed periodic estimate for orientedDivisorTerm does not apply
uniformly after inserting those weights. No bound for the remaining signed
complementary sum was proved. This is neither a proof nor a disproof of
Erdős 371. Spec.lean is unchanged with its original sorry.

## Exact rough-radical complementary kernel

RoughRadicalComplement.lean compiles cleanly; its five main axiom checks
use only the permitted axioms. The temporary CheckComplement.lean was removed.

- roughRadical B m is the squarefree product of primes >B dividing m.
- rough_moebius_tail_radical passes the large rough divisor sum to divisors
  of this radical exactly. Repeated prime factors require no exceptional set,
  since nonsquarefree divisors have zero Mobius coefficient.
- squarefree_moebius_tail_complement proves the exact complementary formula
  mu(R/e)=mu(R)*mu(e), retaining the global parity factor.
- roughLargeDivisorTail_complement applies this to the actual oriented tail.
- roughRadical_complement_support places complementary indices in
  [1,(N+1)/H] when the original divisor cutoff is H*N and n<=N.
- roughLargeDivisorTail_eq_sublinear_complement and its prefix version give
  an exact explicit sum with input-dependent parity and least-factor colour.
- complementedRoughTail_mixed_remainder_tendsto uses the uniform one-sided
  correction to identify its mean with the mixed tail up to o(1).
- density_iff_sublinear_complement and exists_sublinear_complement_criterion
  package the precise remaining criterion with B,H tending to infinity and
  subpower B, supplied by the justified superlinear-cutoff diagonal.

No cancellation estimate for this complementary kernel has been proved.
Its short index range does not make its input-dependent weights periodic,
so the small-modulus discrepancy bound cannot be reapplied as it stands.
Spec.lean remains unchanged; this is not a settlement of the conjecture.

## Unit complementary index has asymptotic absolute mass one

ComplementUnitMass.lean compiles cleanly with only the permitted axioms in
all three main axiom checks. It imports RoughRadicalComplement and the older
AbsoluteKernelObstruction. The temporary CheckUnitComplement.lean was removed.

- goodRoughPair_product_sq_large: for the existing density-one good pairs,
  (roughPrimePart(B,n+1)*roughPrimePart(B,n+2))^2 > (N+1)^3.
- goodRoughPair_product_dvd_radical: their squarefree rough-part product
  divides roughRadical(B,(n+1)*(n+2)). No equality or unsupported replacement
  of prime powers is used.
- goodRoughPair_radical_large: consequently the radical exceeds every D
  with D^2 <= (N+1)^3.
- roughComplementUnit B D n is exactly the e=1 term in the complementary
  formula, including the outer Mobius factor and the least-factor colour.
  Its norm is 1 if D<roughRadical(B,n*(n+1)), and 0 otherwise.
- subpower_cutoff_add_one_sq_eventually_le: the subpower logarithmic-ratio
  hypothesis implies (B(N)+1)^2<=N eventually.
- MAIN roughComplementUnit_absolute_average_one: if B->infinity is subpower
  and eventually H<=B+1, then the norm of the e=1 term at D=H*N, averaged
  over n+1 for n<N, tends to ONE. The good-pair density-one result supplies
  the lower bound; each term's norm is at most one.
- complementedRoughAbsoluteMass is the sum of absolute values of every
  individual complemented summand, retaining the outer Mobius factor.
- MAIN complementedRoughAbsoluteMass_eventually_lower: if additionally
  H->infinity, this mass divided by N is eventually >=1-epsilon for every
  epsilon>0. The unit index belongs to the complementary interval eventually.
- MAIN complementedRoughAbsoluteMass_not_tendsto_zero rules out o(N)
  absolute mass for these cutoffs, including those supplied by the new
  superlinear small-modulus diagonal.

This is a new obstruction for the ACTUAL superlinear complementary kernel,
not an illicit extension of the older D<=N rectangular bound. It shows that
even the smallest complementary index is not sparse in the input variable.
The e=1 signed term remains an input-dependent rough Mobius parity/colour
correlation, and cancellation between all indices is also unproved.
No new signed estimate, proof, or disproof of Erdos 371 was obtained.
Spec.lean still has its original sorry and unchanged statement/import.

## Exact largest-prime toggle inside the truncated tail

LargestPrimeToggle.lean compiles cleanly. Both main axiom checks contain
only propext, Classical.choice, Quot.sound.

This continuation tested signed cancellation INSIDE each input's divisor
sum, rather than reusing the failed absolute-value estimate.

- subset_tail_toggle_largest: for p the largest element of a finite set s,
  p>=1 and D>=p, write w(t)=subsetMinTerm f t. Then exactly
    sum_{t subset s, prod(t)>D} w(t)
      = -sum_{t subset s\{p}, prod(t)<=D<p*prod(t)} w(t).
  Pair t with insert p t. On nonempty t the least element is unchanged,
  while the parity flips. Both-admitted pairs cancel; only pairs crossing
  the product cutoff survive. Empty t contributes nothing because D>=p.
- squarefree_tail_eq_subset_tail converts the squarefree divisor tail to
  the finite-set form without dropping any weights.
- roughLargeDivisorTail_eq_subset_tail applies that form to the rough
  radical exactly, retaining repeated-prime handling from the earlier module.
- MAIN roughLargeDivisorTail_max_toggle applies the toggle to the actual
  arithmetic tail when D>=maxPrimeFac(n*(n+1)) and the radical exceeds one.
  The surviving subset-products lie in (D/p,D], and p is the largest rough
  prime of the input. This p and the excluded-prime condition are retained.

This is genuine pointwise signed cancellation, but NOT a mean estimate for
the boundary. Its input-dependent largest-prime restriction prevents simply
reusing the fixed-modulus periodic discrepancy bound. Nor is the boundary
proved sparse. No settlement of the conjecture follows; Spec.lean is unchanged.

## Boundary-average review after the largest-prime toggle

Re-examined whether the largest-prime toggle closes the small-modulus argument.
It does not currently supply the needed estimate. For a divisor d of the rough
radical, excluding its largest prime and crossing D is equivalent to requiring
that the largest prime of the input product exceed both P(d) and floor(D/d).
Thus the restriction can be expressed as the complement of a common smoothness
condition on n and n+1, with cutoff depending on d,D rather than the input's
largest prime. This is an algebraic interpretation of the boundary, not a new
proved cancellation theorem. The smoothness weight still moves with the
endpoint. The periodic discrepancy bound for orientedDivisorTerm is not
uniform under this weight; fixed-cutoff reversal does not justify that limit.

Also reviewed adapting the cutoff to a monotone function of the input. Such
cutoffs permit interval-fiber discrepancy estimates on the small-modulus
side, but they do not remove the parity/colour dependence of complementary
terms or bound the moving smoothness-weighted remainder. No claim of a
settlement follows from this variation.

No new Lean theorem or final-file edit was made in this continuation.
Spec.lean retains its original sorry. A genuine signed arithmetic estimate,
not another equivalent expansion, is still required.

## Natural-endpoint transfer recheck

Re-read actual_prime_comparison_transfer, conditioned_prefix_dilation,
natural_prime_gap_transfer, and the stationary entropy recurrence. The
conditioned adjacent endpoint remains N/p. Narrowing the multiplier interval
controls the spread among these shorter endpoints, not their distance from
an arbitrarily prescribed natural endpoint. Choosing a separate sampling
length at each entropy scale is not licensed by the same-law recurrence.

The existing exact-dilation/power-stable biased families are endpoint-dependent
auxiliary models, not the actual prime labels and not max-multiplicative.
They therefore do not rule out using the latter's stronger polynomial-range
stability, but no theorem exploiting that extra structure to close the
natural-endpoint gap was obtained. No prime-gap cancellation estimate was
proved either. No new Lean theorem or change to Spec.lean was made.

## Small prime-insertion increment check

Revisited the elementary insertion recurrence and tested the proposed
constant-per-insertion bound before trying to use it asymptotically.
PrimeInsertionCheck.lean compiles and its printed axiom check is permitted.

At endpoint 49, cutoffPrime 30 has 25 rises and 24 falls, while cutoffPrime
210 has 27 rises and 22 falls. Inserting the next prime 7 therefore changes
the signed prefix count by FOUR. This kernel-checked example refutes a
two-unit insertion bound; it does not disprove every possible constant or
aggregate insertion bound, and does not concern the conjecture's negation.
Exploratory finite computations at further prime insertions also showed
larger increments, but no asymptotic inference from those computations is
claimed. A signed aggregate estimate remains missing. Spec.lean is unchanged.

## Further aggregate prime-wheel discrepancy audit

Reviewed whether an aggregate bound could replace the already-refuted two-unit
per-prime insertion bound. Exploratory exact integer-array computations over
complete primorial periods gave maximum absolute prefix discrepancies 1, 1, 3,
5, 7, 11, 31, and 60 for the first 1 through 8 primes respectively (the periodic
array uses the largest selected divisor also at residue zero). Thus bounds by
2K, or even 4K, do not hold for every finite K-prime wheel. These exploratory
checks were not promoted to Lean theorems. They neither exclude every constant
multiple of K nor refute an ambient-prime-count bound for the actual sequence.

Reconsidered nonnegative multiplicative indicator approximation, damped Mobius
expansions, and natural-endpoint entropy transfer. None supplied the missing
signed estimate: high-product mixed divisors remain outside periodic bounds;
low-prime insertion changes the least-prime colour; and entropy-selected
shorter endpoints cannot be substituted for a prescribed endpoint. No new
uniformity or cancellation theorem was assumed.

No complete proof or disproof was obtained. Spec.lean remains unchanged with
its original sorry; no proof submission has been made.

## Formalized largest-prime boundary as a moving common-smoothness weight

New module Submission/LargestPrimeBoundaryWeight.lean compiles. Both main
printed axiom checks contain only propext, Classical.choice, and Quot.sound.

- maxPrimeFac_divisor_lt_iff: for d|R and R>1, P(d)<P(R) iff the largest prime
  of R is absent from d.primeFactors; the d=1 case is included.
- squarefree_tail_moving_smooth_weight: for squarefree R>1 and D>=P(R),
    sum_{d|R,d>D} leastFactorTerm(f,d)
      = -sum_{d|R,d<=D, max(P(d),floor(D/d))<P(R)} leastFactorTerm(f,d).
  This is proved from the largest-prime toggle, including the exact conversion
  from subsets back to divisors and the natural-number division inequality.
- roughRadical_maxPrimeFac: a nontrivial rough radical has the same largest
  prime as the original nonzero input.
- commonSmoothWeight U n is the indicator that BOTH n and n+1 are U-smooth.
- MAIN roughLargeDivisorTail_moving_smooth_weight: for n>0 and
  D>=P(n(n+1)), the actual rough tail is exactly
    -sum_{d|roughRadical(B,n(n+1)), d<=D}
       leastFactorTerm(sideColour(n),d) *
       (1-commonSmoothWeight(max(P(d),floor(D/d)),n)).
  The theorem handles radical=1 exactly, without an exceptional-set hypothesis.
  It therefore includes repeated prime factors in n(n+1) without discarding
  them or identifying the radical with a prime-power product.

This formalizes an observation previously recorded only algebraically. It does
NOT estimate the mean under the moving smoothness weight. The existing periodic
orientedDivisorTerm discrepancy theorem does not license inserting this weight.
No complete proof or disproof has been obtained; Spec.lean is unchanged.
Temporary CheckBoundary.lean was removed.

## Completed ordinary exponential Tauberian recovery

Three new modules compile cleanly, with saved .olean files and only the
permitted axioms in their main printed checks:
- Submission/ExponentialWindow.lean
- Submission/ExponentialTauberian.lean
- Submission/ExponentialDensityCriterion.lean

This continuation supplied the analytic recovery theorem that the earlier
exponential-smoothing audit had not formalized. It did NOT obtain an arithmetic
exponential-mean estimate.

ExponentialWindow:
- window k r n = 1-(1-r^n)^k.
- For 0<=r<1 this is nonnegative and at most k*r^n.
- If k*r^N=1, its deficit from one on n<N sums to at most r/(1-r).
  The proof uses k*x*(1-x)^k<=1 and a reversed finite geometric sum.
- MAIN prefix_window_error: for EVERY real sequence with |f(n)|<=1,
    |sum_{n<N} f(n) - sum_{n>=0} f(n)*window(k,r,n)|
      <= (1+r)/(1-r).
  Absolute summability and the infinite tail bound are proved, not assumed.

ExponentialTauberian:
- endpointRatio k N = exp(-log(k)/N), with k*r^N=1 for k>1,N>0.
- MAIN prefix_exponential_window_error: normalized error <=2/N+2/log(k).
  This uses exp(t)>=1+t, not a Tauberian axiom or an uncontrolled limit swap.
- Exact finite binomial expansion of window in positive powers of r^n.
- exponentialMean f t = t*sum_{n>=0} f(n)*exp(-t*n).
- MAIN cesaro_zero_of_exponential_zero: if |f(n)|<=1 and exponentialMean(f,t)
  tends to zero as t->0+, then (sum_{n<N} f(n))/N tends to zero.
  For fixed k the window mean tends to zero by the finite expansion. Then
  choose k large and N large, with the uniform approximation bound above.

ExponentialDensityCriterion:
- MAIN density_of_exponential_sign_cancellation applies this theorem to the
  ACTUAL factorSign sequence and concludes exactly the original density
  statement, conditional on exponentialMean(factorSign,t)->0.

IMPORTANT: the condition is ORDINARY exponential smoothing in n. The existing
Dirichlet-Abel prime-residue limits and logarithmic averages do not give this
condition. No arithmetic signed estimate establishes it here. The target
Spec.lean remains unchanged with its original sorry; no proof is submitted.
Temporary CheckTauberian.lean was removed.

## Exponential arithmetic-kernel and energy audit after Tauberian recovery

Re-examined whether ordinary exponential smoothing supplies the signed
arithmetic estimate still missing from ExponentialDensityCriterion. For each
fixed coprime divisor pair, smoothing retains the reciprocal-root dependence.
Swapping the divisor variables changes the signs of BOTH roughBilinearWeight
and the reciprocal-residue discrepancy, so their product is not cancelled by
that swap. No uniform estimate for the growing weighted modulus sum was proved.
The new bounded-sequence Tauberian theorem therefore cannot yet be applied to
factorSign.

Also checked the strongest existing prime-winner energy results for a possible
closing implication. The cofactor log-power results concern primes above
N/(log N)^a, not primes above (log N)^a. The unconditional arbitrary log savings
start at the quadratic N^2 scale and do not imply the near-linear, subpower-loss
energy criterion. No missing hypothesis of those criteria was supplied.

No new Lean theorem was added in this audit. The three exponential modules
from the preceding continuation remain verified, but their actual arithmetic
cancellation input is unproved. Spec.lean and its original sorry are unchanged;
no complete proof or disproof has been submitted.

## Full low-mass inclusion-data audit

Re-read PartitionObstructionWithSmallParts, RefinedPartitionObstruction, and
FixedMarginalPartitionPerturbation to check the precise scope of their tests.
Their moment identities cover EVERY finite inclusion configuration within the
stated mass budget, not merely moments up to some fixed degree. Raising the
moment degree within that budget does not by itself bypass these models.

The seven-state trade can be understood as coalescences of three large parts
versus coalescences of two large parts, with small tails retained. A possible
continuous parameterization and embedding into a Poisson-Dirichlet marginal
was considered, but no such embedding or bounded Radon-Nikodym perturbation was
proved or formalized. Conversely, no uniqueness argument using the actual
continuous marginal law was obtained. The existing finite countermodel must
not be represented as having that actual marginal law or as an arithmetic
counterexample.

No new signed arithmetic estimate, Lean theorem, or change to Spec.lean was
made. The conjecture remains unresolved with its original sorry unchanged.

## Abelian converse and uniform-prefix exponential small-modulus cancellation

New modules ExponentialAbelian.lean and ExponentialRoughCutoff.lean compile
cleanly with saved .olean files. ExponentialDensityCriterion.lean was updated
and rebuilt. All main printed axiom checks use only propext, Classical.choice,
and Quot.sound. No Spec.lean import or statement was changed.

ExponentialAbelian:
- weighted_prefix_identity proves the exact geometric partial-summation
  identity, with summability proved from the bounded sequence hypothesis.
- exponential_mean_affine_bound: if |sum_{n<M}f(n)|<=C+epsilon*M, then for t>0
    |exponentialMean f t| <= C*t+epsilon*(1+t).
- exponential_zero_of_cesaro_zero supplies the Abelian converse.
- exponential_zero_iff_cesaro_zero combines this with the previously proved
  Tauberian direction for every real sequence bounded by one.
- exponential_mean_of_bounded_prefix: a uniform bound C on all signed prefix
  sums implies |exponentialMean f t|<=C*t. No separate bound on individual
  terms is required; the proof derives one and rescales safely by 2*C+1.

ExponentialDensityCriterion now proves density_iff_exponential_sign_cancellation,
an exact equivalence for the actual factorSign sequence. This is still NOT a
proof of either side, and ordinary exponential smoothing must not be confused
with Dirichlet-Abel or logarithmic averaging.

ExponentialRoughCutoff:
- roughPrefixBudget(B,K,D)=((2^K)+1)*roughNumberCount(B,D+1).
- roughSmallDivisorSum_exponential_bound applies the signed prefix estimate,
  via partial summation, to the actual small rough-divisor contribution.
- MAIN exists_subpower_superlinear_uniform_prefix_budget constructs B,H,C with
  B->infinity, H->infinity, B subpower, eventually H<=B+1, C>=0, C(N)/N->0,
  and eventually for EVERY M,
    |sum_{n<M} roughSmallDivisorSum(B(N),H(N)*N,n+1)| <= C(N).
  This is stronger endpoint uniformity than the earlier diagonal that recorded
  cancellation only at M=N. A NEW constrained Nat.findGreatest diagonal
  enforces the explicit budget, factor-length condition, and log condition.
- MAIN exists_subpower_superlinear_exponential_cutoff consequently proves
  vanishing exponential mean of this small-modulus sum at t=1/N.

LIMIT: none of these statements estimates the rough LARGE-divisor remainder
or permits an arbitrary input-dependent smoothness weight inside the periodic
bound. The full arithmetic exponential cancellation remains unproved. The
conjecture in Spec.lean retains its original sorry and is not submitted.
Temporary CheckAbelian.lean was removed.

## Quantitative natural-prefix transfer for bounded odd prime patterns

Five auxiliary modules now compile with saved .olean files:
- BooleanPatternTruncation.lean
- FinitePatternComparison.lean
- PrimePatternInclusion.lean
- PrimePatternReflection.lean
- PrimePatternApproximation.lean
All principal printed axiom checks contain only propext, Classical.choice,
and Quot.sound. Spec.lean remains unchanged and unresolved.

This supplies a genuine new ingredient beyond the earlier complete-CRT
martingale heuristic at log line ~3394:

1. patternDifference is the finite Boolean Moebius transform of an arbitrary
   function on finite active-atom sets. Its inversion is proved, its norm is
   <=2^|T| for a unit-bounded function, and degree <L truncation has pointwise
   error <=(1+3^L)*choose(number_of_active_atoms,L). The proof is valid for all
   L, including L=0; it uses a covering by L-subsets rather than an unproved
   asymptotic expansion.
2. finite_pattern_comparison_factorial compares a weighted sample to arbitrary
   low-degree inclusion masses, with an explicit factorial-moment remainder.
   It does not assume independence of the actual sample.
3. Prime atoms are (p,Bool); false encodes residue 0 and true residue p-1.
   primeAtomModel(T) is product(1/p) if the prime coordinate is injective,
   and zero otherwise. Both colours of the same prime are incompatible;
   their actual inclusion count is proved zero. For all other patterns,
   the existing CRT theorem gives normalized error <=product(p)/N.
   This deliberately coarse error yields a polynomial X^(2L)/N, not the
   sharper X^L/N proposed in the informal sketch. The coarse error suffices.
4. A prime-preserving permutation keeps primeAtomModel invariant. Any globally
   odd observable has ZERO model term at every truncation degree. In
   particular, primeColourFlip(B) flips the colours in a selected prime block.
5. prime_pattern_odd_bound proves
     |mean_N F(activePrimeAtoms(P,n))|
       <= (1+3^L)*lambda^L/L! + (1+3^L+L+1)*Z^L/N,
   with lambda=2*sum_{p in P}1/p and Z>=max(1,sum_atoms 2*p).
6. MAIN exists_small_power_for_pattern_symmetry:
   for every reciprocal-mass bound M and error epsilon>0, there exists a
   fixed delta>0 such that, eventually for EVERY N and uniformly over EVERY
   prime set P with p<=N^delta and lambda<=M, EVERY bounded odd pattern
   observable has natural prefix mean of norm <epsilon. The observable and
   its prime-preserving reflection may both depend on N. No full CRT period
   appears in this transfer bound. Degree L is chosen first; then delta=1/(4L)
   gives a rounding error bounded by a fixed multiple of N^(-1/2).

This is NOT yet the prime-block Bessel argument: block first-colour functions,
their correlations, selection of compatible cutoffs, and signed unit-term
cancellation have not been formalized. In particular it does NOT estimate
factorSign or the whole large-divisor tail. Even signed cancellation of the
unit complementary term would leave the growing e>=2 complementary sum.

The full-tail obstruction was rechecked: applying Bessel separately to each
complementary index and then summing absolute errors incurs an uncontrolled
loss as the range and rough-prime reciprocal mass grow. Fixed finite blocks
can also grow too slowly for the small-modulus budget. Neither issue has
been claimed solved. The new power-band transfer only removes the former
complete-period-to-natural-prefix gap for bounded odd local patterns.
Temporary CheckPattern.lean was removed. No proof/disproof is submitted.

## Moving prime-block witnesses and Bessel selection now formalized

Four further modules compile with saved .olean files and permitted axioms:
- PrimeBlockColour.lean
- FiniteBesselSelection.lean
- PrimeBlockWitness.lean
- PrimeBlockSelection.lean

PrimeBlockColour defines the first active prime's colour in a finite block
(and zero for an empty block), and parity of the number of active primes.
The first colour is bounded by one even for incompatible formal patterns.
A colour flip in the second of two disjoint blocks negates
  parity(A)*firstColour(B)*firstColour(C),
while preserving the other factors. This gives natural-prefix small-power
cancellation for these actual block-pair observables, uniformly in all three
blocks and the sampling endpoint.

FiniteBesselSelection proves, for K bounded witnesses with normalized
cross-correlations <=eta and any bounded target G,
  (sum_i |sum_x G(x)W_i(x)|)^2 <= |X|^2*(K+K^2*eta).
Consequently, if 1/K+eta<epsilon^2, at least one normalized correlation has
norm <epsilon. No lower bound on witness norms is used.

PrimeBlockWitness handles locality and cancellation of common low-prime
parity. The natural witness is
  primeBlockWitness(A,B,n)=parity_of_active_primes(A,n)*firstColour(B,n).
For A subset C, its product with witness(C,D,n) depends only on C\A, B, D:
  witness(A,B,n)*witness(C,D,n)
    = blockPairObservable(C\A,B,D,activePrimeAtoms(P,n)),
provided those three sets lie in P. The much larger common low-prime set A
need not be contained in P or paid for in the reciprocal-mass budget.

MAIN PrimeBlockSelection.exists_small_power_for_block_selection combines
this exact identity with the preceding natural-prefix transfer and Bessel.
Given K, eta, epsilon with 1/K+eta<epsilon^2 and a mass bound M, it chooses
one fixed delta>0. Eventually at every natural endpoint N, for EVERY prime
band P below N^delta with reciprocal mass <=M, EVERY nested family of bases
whose differences lie in P, EVERY family of pairwise-disjoint colour blocks
inside P, and EVERY bounded G, some witness has normalized correlation
<epsilon. All families and G may depend on N. Thus the selection theorem
now has the needed endpoint uniformity and can allow power-growing cutoffs.

Still NOT completed:
- construct sufficiently occupied consecutive power blocks with a uniform
  mass bound chosen BEFORE delta, and connect their witnesses to the actual
  roughComplementUnit including its radical-size indicator;
- obtain signed unit cancellation together with the small-divisor budget;
- estimate the growing e>=2 complementary sum (which remains a separate,
  substantially larger obstruction to the conjecture).
Spec.lean remains unchanged and unresolved. No proof/disproof is submitted.

## Signed cancellation of the actual unit complement completed

Seven new modules compile with saved .olean files; main axiom checks use only
propext, Classical.choice and Quot.sound:
- PrimeBlockArithmetic.lean
- IteratedPrimeBlocks.lean
- OccupiedPowerPrimeBlocks.lean
- RoughUnitWitness.lean
- SignedRoughUnitPowerCutoff.lean
- SignedRoughUnitDiagonal.lean
- SignedComplementUnit.lean

PrimeBlockArithmetic identifies the two residue colours with p|n and p|n+1,
and proves an empty-block bound from the one-integer divisor-count variance:
  empty_count(P,N)/N <= 4/mass(P)+8*card(P)/(N*mass(P)).

IteratedPrimeBlocks uses cutoff(t,J,i)=t^(2^(J*i)) and consecutive blocks
(cutoff_i,cutoff_{i+1}]. Each block has reciprocal mass >=J/4 once log(t)
is large enough. The WHOLE band (t,cutoff_K] has twice reciprocal mass
<=16*2^(J*K) for sufficiently large t. Importantly this mass bound is
independent of the final power exponent; it is chosen BEFORE the exponent
in the small-power pattern-transfer theorem.

OccupiedPowerPrimeBlocks then takes t=floor(N^(alpha/2^(J*K))). It proves
simultaneously:
- t>=N^u for some fixed u>0;
- the top cutoff <=N^alpha;
- the preceding total-band mass bound;
- every one of the K blocks has empty proportion <=16/J+epsilon.
All these statements hold at the same natural endpoint, uniformly in i<K.

RoughUnitWitness defines
  fullRadicalParity(n)=(-1)^card(primeFactors(n(n+1))),
  untruncatedRoughUnit(B,n)=mu(roughRadical(B,n(n+1)))*sideColour(min rough prime).
For n>0, the rough Mobius factor is exactly fullRadicalParity(n) times
naturalBlockParity(primesThrough(B),n). On an occupied block (B,C], the first
block prime is exactly the least rough prime. Hence the untruncated unit
is EXACTLY fullRadicalParity times primeBlockWitness. The prefix mean error
is <=2/N+2*empty_block_count/N, including the exceptional n=0. Repeated
prime factors are handled exactly by the radical.

SignedRoughUnitPowerCutoff.exists_power_cutoff_unit_cancellation:
for every epsilon>0 and upper exponent rho>0, there exists a fixed u>0,
u<=rho, such that eventually at every N one can select an integer B with
  N^u<=B<=N^rho,  |mean_N untruncatedRoughUnit(B,n)|<epsilon.
The selected witness is from the occupied consecutive block family above.

SignedRoughUnitDiagonal uses a NEW constrained Nat.findGreatest diagonal,
not the previously selected arbitrary cutoffs. It simultaneously enforces:
B->infinity, H->infinity, B subpower, H<=B+1, signed untruncated unit mean->0,
and a single nonnegative budget C(N)=o(N) bounding EVERY signed sampling
prefix of roughSmallDivisorSum(B(N),H(N)*N,n+1).

SignedComplementUnit first handles the n versus n+1 prefix shift with error
<=2/N. It then proves the exact pointwise identity
  |roughComplementUnit-untruncatedRoughUnit|=1-|roughComplementUnit|.
The earlier absolute-unit-mass theorem (limit ONE) therefore restores the
radical-size indicator with negligible error. MAIN
  exists_signed_complement_unit_cutoffs
constructs B,H,C with ALL the preceding small-modulus/subpower properties
and signed mean of the ACTUAL roughComplementUnit(B(N),H(N)*N,n+1)->0.

LIMIT: this cancels only e=1 in the complementary-divisor sum. The growing
e>=2 sum remains unestimated; no density-half theorem or disproof follows
from these results alone. The original Spec.lean remains unchanged with its
original sorry. No proof/disproof has been submitted. CheckBlock.lean removed.

## Explicit nonunit complementary criterion

NonunitComplementCriterion.lean now compiles and has a saved .olean. Its main
axiom check uses only propext, Classical.choice, and Quot.sound.

nonunitComplementedRoughTail is the ACTUAL complementary expression with
index set Icc 2 ((N+1)/H), retaining the input-dependent radical, Mobius,
least-prime side colour, divisibility condition, and product cutoff. The
identity complementedRoughTail=roughComplementUnit+nonunitComplementedRoughTail
is proved when H>0 and H<=N+1; the latter follows eventually from the selected
subpower constraints. It is not merely defined by subtraction.

MAIN exists_nonunit_complement_criterion unconditionally constructs B,H with
B,H->infinity and B subpower such that the ORIGINAL density conjecture is
equivalent to mean(nonunitComplementedRoughTail)->0. This uses both the newly
proved actual-unit cancellation and the uniform small-divisor prefix budget.
The right-hand limit is STILL UNPROVED. No equivalence is substituted for a
settlement in Spec.lean.

Further route audit:
- The elementary dyadic identity and failed permanent branch-pruning route
  already occur in Explore/DyadicIterationCheck and the research log. They
  were not rediscovered as a new contraction; cancelled branches can reappear.
- Extending block selection separately to a growing family of complementary
  indices cannot be justified by summing individual Bessel errors. The
  reciprocal divisor mass grows as the lower exponent decreases, and common
  low-prime parity cancellation does not make arbitrary large-factor weights
  local prime-pattern observables.
- A prospective extension to complementary indices e<=B^T for each fixed T
  could use bounded local-pattern moments and blocks with more than T active
  primes. This has NOT been proved. Even if proved with a new diagonal T->infinity,
  it would not automatically reach the full range e<=(N+1)/H: the admissible
  lower power exponent can shrink rapidly with T and the number of blocks.
- The full-tail function has a surviving component independent of low prime
  colours (the largest-prime sign itself). Low-prime orthogonality alone does
  not show that the entire tail is orthogonal across cutoffs.

No new closing estimate has been established. Spec.lean remains unchanged.

## Fixed-degree short complements: completed extension beyond the unit term

This continuation repaired PrimeBlockFactorialMoments.lean and completed a
14-module, approximately 1,629-line extension. Every listed module compiles,
has a saved .olean, and the main transitive axiom checks contain only propext,
Classical.choice, and Quot.sound. There are no admissions in these modules.

Completed modules:
- PrimeBlockFactorialMoments.lean
- PolynomialPatternTail.lean
- LocalPatternSelection.lean
- ShortComplementPattern.lean
- ShortComplementSelection.lean
- ShortComplementArithmetic.lean
- ThinPrimeBlocks.lean
- ShortComplementWitness.lean
- SignedShortComplementPowerCutoff.lean
- SubpowerPolynomialCutoff.lean
- ShiftedPolynomialPatternTail.lean
- ShortComplementIndicator.lean
- SignedShortComplementDiagonal.lean
- SignedShortComplement.lean

MAIN RESULT: SignedShortComplement.exists_signed_short_complement_cutoffs k
For every FIXED natural k, this unconditionally constructs B,H,C such that:
  B -> infinity, H -> infinity, B is subpower, eventually H<=B+1;
  C>=0 and C(N)/N -> 0;
  eventually, for EVERY M, the absolute signed prefix sum of
    roughSmallDivisorSum(B(N),H(N)*N,n+1), n<M,
  is bounded by C(N);
  the signed natural-prefix mean of
    shortRoughComplementAt(B(N),H(N)*N,k,n+1)
  tends to zero.
Here shortRoughComplementAt is the ACTUAL arithmetic expression
  mu(R) * sum_{e|R, e<=B^k, D*e<R} mu(e)*sideColour(n,R/e),
  R=roughRadical(B,n(n+1)), D=H*N.
Thus both the input-dependent Mobius weight and the moving radical-size
indicator have been retained. This is not a formal difference definition.

Intermediate results and important proof details:

1. PrimeBlockFactorialMoments:
   mean choose(card(activePrimeAtoms(P,n)),L)
     <= lambda^L/L! + Z^L/N.
   For prescribed L, all prime sets below N^(1/(4*(L+1))) with lambda<=M
   have the mean <=M^L/L!+epsilon eventually, uniformly in P.

2. PolynomialPatternTail defines
   subsetPolynomial(k,m)=sum_{j<=k} choose(m,j).
   For m>=R>k+1 it is bounded by
     [3^(k+1)*(k+2)/(R-k-1)]*choose(m,k+2).
   This gives uniform integrability with an exponent depending only on k,
   NOT on the clipping threshold R. The shifted version handles n+1 using
   the endpoint N+1 and nonnegativity, not a bounded-observable shortcut.

3. LocalPatternSelection generalizes the old first-colour witness lemma.
   Witnesses are low-prime parity times ANY bounded local pattern F_i.
   F_j must be odd under its own colour flip, which fixes all earlier F_i.
   Common low-prime parity cancels exactly in products.

4. ShortComplementPattern sums over active block subsets E:
   if card(E)<=k and product(E)<=X, then
     (-1)^card(E)*firstBlockColour(block\E).
   It is globally odd under the block flip, fixed under disjoint flips,
   local, and bounded by subsetPolynomial(k,active_block_count).
   A high-count clipping preserves these symmetries.
   short_prime_product_card_le proves the degree cap is redundant for
   e<=B^k when all selected primes exceed B>1.

5. ShortComplementSelection fixes the individual-block mass Mb BEFORE
   choosing clipping threshold and number K of witnesses. It then permits
   any total-band mass M, even one depending on K, before choosing the
   small prime exponent delta. This order avoids a circular K/M bound.
   Selection is uniform in all X_i and all unit-bounded targets G.

6. ShortComplementArithmetic proves exact divisor/subset identification.
   For X=B^k<=C and n>0, every eligible subset lies in the active block
   (B,C]. If that block has more than k active primes, the first prime
   remaining after each permitted deletion is the TRUE least prime of R/e.
   Consequently shortRoughComplement(B,k,n), without the size indicator,
   is fullRadicalParity*low-prime parity*the local short pattern.

7. ThinPrimeBlocks extends occupancy to >k active primes. Assuming J>=8k,
   each iterated block has thin proportion <=16/J+small endpoint error.
   It also gives the individual block mass bound 16*2^J, independent of K.
   The whole-band mass remains 16*2^(J*K).

8. ShortComplementWitness uses the common bounded target
     nonzeroFullParity(n)=if n=0 then 0 else fullRadicalParity(n).
   This prevents an UNBOUNDED local pattern at n=0 being silently dropped.
   The mean discrepancy is <=1/N+2^(k+1)*thin_block_proportion.
   Repeated prime powers are handled by the rough radical throughout.

9. SignedShortComplementPowerCutoff proves:
   for every fixed k, epsilon>0, rho>0 there is fixed u>0, u<=rho, such
   that eventually for every N some N^u<=B<=N^rho has
     |mean shortRoughComplement(B,k,n)|<epsilon.

10. Restoring the size indicator is now PROVED, not a remaining subgap.
    ShortComplementIndicator.shortRoughComplementAt_mean_absolute_error_zero
    works along ANY B->infinity with B subpower and H<=B+1.
    For fixed k, the difference vanishes in mean absolute value.
    The exceptional event is R<=H*N*B^k. Its proportion ->0 because
    (H*N*B^k)^2<=(N+1)^3 eventually and the earlier good-rough-pair theorem
    supplies density-one radicals above that threshold.
    The error is weighted by a subset polynomial, so probability alone is
    NOT used: local-band factorial-moment tails supply uniform integrability.
    The relevant local band is (B,B^k], whose twice reciprocal mass is
    <=16*(k+1), independently of the chosen power-block family and tolerance.

11. SubpowerPolynomialCutoff proves (B+1)^k<=N^delta eventually for EVERY
    fixed k and delta>0, and (B+1)^k/N->0. The final signed theorem retains
    the shift from n to n+1 explicitly: the untruncated endpoint discrepancy
    is <=2*(B^k+1)/N, not a constant/N estimate for an unbounded observable.

12. SignedShortComplementDiagonal is a NEW constrained Nat.findGreatest
    diagonal for each fixed k, simultaneously enforcing its short-sum limit
    and the uniform small-divisor prefix budget. Do not ascribe these new
    properties to older arbitrary cutoff choices.

STATUS AND LIMITS:
- The newly proved fixed-k result is stronger than cancelling e=1 alone.
- It does NOT estimate the remaining range B^k<e<=(N+1)/H.
- The selected cutoffs DEPEND ON k. Simultaneous cancellation for every
  fixed k at a single B,H has not been shown by this theorem.
- A further diagonal with k(N)->infinity would not automatically reach N/H.
  In this construction the lower power exponent can shrink very rapidly
  as k, occupancy, and the required witness count increase.
- Large complementary indices can contain just ONE prime exceeding B^k;
  they cannot be discarded as a high-active-count exceptional event.
- Arbitrary large-factor weights are not local pattern observables.
- The full tail still has a low-prime-colour-invariant component, namely
  the original largest-prime sign. The present local orthogonality method
  does not estimate this component.

Spec.lean remains unchanged with its original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof has been obtained or submitted. CheckPoly.lean
was removed. No new unfinished scaffold remains from this continuation.

## Simultaneous maximal complementary prefixes and a growing window

Ten more modules, 955 lines, now compile with saved .olean files and permitted
transitive axioms only. No admissions occur in them:
- MaximalShortPatternSelection.lean
- ComplementPrefixArithmetic.lean
- ComplementPrefixWitness.lean
- MaximalComplementPowerCutoff.lean
- MaximalComplementPrefixRow.lean
- MaximalComplementDiagonal.lean
- ComplementPrefixIndicator.lean
- UniformComplementCutoffs.lean
- GrowingComplementWindow.lean
- LongComplementCriterion.lean

The preceding warning that the proved cutoffs depend on each fixed degree
has now been overcome for a NEW selected cutoff pair. It is NOT overcome by
attributing simultaneous properties to older arbitrary choices.

Key new quantifier observation:
The old short-pattern selection theorem permits an ARBITRARY endpoint X_i
at EACH block, all at the same N. If every block had some bad endpoint,
choosing those endpoints separately would contradict that theorem.
MaximalShortPatternSelection formalizes this adversarial-choice argument:
one block is good for ALL natural product endpoints X. No union bound in
X, finite-family loss, or new Bessel inequality is required. Orthogonality
already holds for different local patterns in the different blocks.

ComplementPrefixArithmetic introduces independent arithmetic endpoint X:
  untruncatedComplementPrefix(B,X,n)
    = mu(R)*sum_{e|R,e<=X} mu(e)*sideColour(n,R/e);
  complementPrefixAt(B,D,X,n)
    = mu(R)*sum_{e|R,e<=X,D*e<R} mu(e)*sideColour(n,R/e).
They are genuine divisor sums, not definitions by subtraction. At X=B^k
they equal the old shortRoughComplement and shortRoughComplementAt.
For X<=B^k<=C, the subset restriction and first-remaining-colour identity
hold with the SAME degree cap k. Thus witness errors are uniform in X.
ComplementPrefixWitness gives error <=1/N+2^(k+1)*thin-block proportion,
again retaining n=0 through the bounded nonzeroFullParity target.

MaximalComplementPowerCutoff.exists_power_cutoff_maximal_complement_cancellation:
for each fixed k and epsilon,rho>0 there is fixed u>0, u<=rho, such that
at EVERY sufficiently large N some N^u<=B<=N^rho satisfies
  |mean untruncatedComplementPrefix(B,X,n)|<epsilon FOR ALL X<=B^k.

MaximalComplementPrefixRow combines this with the fixed-multiple prefix
budget. MaximalComplementDiagonal uses row degree k and precision index
(k+1)^2. It constructs B,H,K,C with K->infinity, B,H->infinity,
  (K+1)*log(B+1)/log N -> 0,
  C>=0, C/N->0, eventually H<=B+1,
  C bounds EVERY small-divisor sampling prefix,
and eventually uniformly for X<=B^K,
  |mean untruncatedComplementPrefix(B,X,n)|<=1/(K+1).
The exponent-weighted log bound is explicit; B^K is NOT allowed silently
to reach a positive power of N.

ComplementPrefixIndicator.complementPrefixAt_mean_error_uniform:
for ANY growing subpower B and H<=B+1, each fixed k, each epsilon>0,
eventually uniformly in ALL X<=B^k, the shifted mean ABSOLUTE difference
between complementPrefixAt(B,H*N,X,n+1) and its untruncated version is
<epsilon. The same factorial-moment tail and exceptional radical event
R<=H*N*B^k work for every X. The moving condition is not dropped for free.

UniformComplementCutoffs handles the shift uniformly, using the exact
bound |untruncatedComplementPrefix(B,X,n)|<=X+1 and endpoint error
<=2*(X+1)/N. MAIN exists_simultaneous_maximal_complement_cutoffs produces
ONE B,H,C with all subpower/growth/uniform-small-prefix-budget properties
such that, for EVERY fixed k and epsilon>0, eventually ALL X<=B^k have
  |mean complementPrefixAt(B,H*N,X,n+1)|<epsilon.
The original fixed-k dependence is therefore genuinely strengthened.

GrowingComplementWindow then chooses a further increasing degree ONLY
for the already selected B,H (it does not change their cutoffs or budget).
MAIN exists_cancelled_growing_complement_window produces B,H,U,C with:
- B,H,U all tend to infinity;
- B and U are both subpower in N;
- eventually H<=B+1;
- C>=0, C/N->0, and C bounds EVERY small-divisor sampling prefix;
- for each fixed k, eventually B^k<=U;
- for every epsilon>0, eventually uniformly for ALL X<=U,
    |mean complementPrefixAt(B,H*N,X,n+1)|<epsilon;
- PROVED size comparison: U(N)*H(N)/N -> 0.
Thus the cancelled window dominates every fixed B-power but occupies a
vanishing fraction of the full complementary endpoint N/H. It is NOT a
coverage proof for that full range.

LongComplementCriterion defines the actual remaining expression
  complementAfterAt(B,D,U,n)
    = mu(R)*sum_{e|R,U<e,D*e<R} mu(e)*sideColour(n,R/e).
It proves the exact decomposition
  roughLargeDivisorTail = complementPrefixAt + complementAfterAt
for n>0 and D>=1. MAIN exists_growing_long_complement_criterion
unconditionally selects B,H,U as above, with U dominating every fixed
B-power and U*H/N->0, such that the ORIGINAL density statement is equivalent
to vanishing signed mean of complementAfterAt(B,H*N,U,n+1).
The right-hand limit is STILL UNPROVED. This equivalence is not submitted
as a settlement, and the original conjecture is not modified.

Additional route review in this continuation:
- The existing Type-II/Vaughan kernel, prime-winner energy, and inverse-
  hyperbola results were inspected; no new estimate closing their gaps was
  found. Short terms and marked o(p) counts still do not control the true
  long range with all input-dependent weights.
- A possible continuous fixed-marginal partition obstruction was sketched
  using row-versus-column trades of a 3x3 equal-sum matrix. Example rows
    (.39,.35,.26), (.31,.32,.37), (.30,.33,.37)
  and columns have identical one-part intensity but maximum signed profile
  delta_.37-delta_.35. All parts exceed 1/4, so low-mass mixed selections
  cannot see two large parts from each side at once. Crossing trades could
  give a nonzero antisymmetric comparison perturbation. However NO
  continuous/Poisson-Dirichlet embedding, bounded density construction,
  or arithmetic consequence of that sketch was proved. Do not promote it
  to an actual PD countermodel or disproof.
- Remaining e>U may have only one prime greater than U; high degree/tail
  moments of the low-prime block do not make these indices exceptional.
- The surviving low-prime-colour-invariant largest-prime component remains
  untouched. Maximal prefix cancellation is not cancellation of that part.

All ten new modules have complete proofs and no unfinished scaffold remains.
The target Spec.lean is unchanged with its original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof has been obtained or submitted.
Latest observed resources: 47h15m20s used, 48h44m40s left; $555.77 used,
$444.23 remaining (before this final research-log write).


# Exponential moments, smooth long indices, and escaping-prime remainder

Four additional complete modules, with saved oleans and permitted axiom checks:
- PrimeCountExponentialMoment: exact one-integer divisor-subset moment expansion;
  upper bound N*exp((z-1)*sum(1/p)); Cauchy--Schwarz gives the consecutive
  active-prime moment <= (N+1)*exp((z^2-1)*sum(1/p)). No prime-size restriction.
- ExponentialPrimePatternTail: for prime reciprocal mass <= M, uniform tail
  mean[1_{m>=L}*2^m] <= 2*exp(15*M)/2^L; weighted exceptional-set square bound
  and density-zero consequence. These are absolute, not signed, estimates.
- SmoothLongComplement: for B->infinity and U eventually dominating every
  B^k, the long complement restricted to prime factors <=B^a has vanishing
  mean absolute value for each fixed a. Retains all actual size weights and
  works for arbitrary D(N). The proof uses the new exponential count tail.
- EscapingComplementCriterion: selects a further Y=B^A, A->infinity, Y<=U,
  dominating every fixed B-power, with vanishing smooth long absolute error.
  Exactly splits the remaining sum by P(e)<=Y or P(e)>Y. The theorem
  exists_escaping_complement_criterion unconditionally chooses B,H,U,Y such
  that the ORIGINAL conjecture is equivalent to cancellation of
    mu(R)*sum_{e|R,U<e,Y<P(e),H*N*e<R} mu(e)*sideColour(n,R/e).
  This signed cancellation is UNPROVED; the remainder includes single large
  primes and is not made rare by low-prime count tails.

CheckExpMoment.lean (exploratory, incomplete #check list) has been removed.
Spec.lean remains unchanged. No settlement or submission.
Resources at resumption: 47h39m44s used / 48h20m16s remaining;
$561.80 used / $438.20 remaining.

# Weighted selection and actual high-only complementary cancellation

Five new complete modules, 713 lines total, all compiled with saved oleans:
- WeightedComplementSelection.lean
- WeightedUnitDiagonal.lean
- HighComplementAlgebra.lean
- SubpowerOccupiedBand.lean
- HighComplementCancellation.lean
Their main transitive axiom checks contain only propext, Classical.choice,
Quot.sound. No sorry/admit/new axiom/native_decide in these modules.

WeightedComplementSelection:
- weightedComplementPrefix_witness_mean_error multiplies the existing
  pointwise witness error by any |w(n)|<=1.
- exists_power_cutoff_weighted_maximal_complement_cancellation gives
  forall epsilon,rho>0 exists u>0, eventually N, FOR EVERY bounded w,
  EXISTS B between N^u and N^rho such that ALL X<=B^k have small mean
  w(n)*untruncatedComplementPrefix(B,X,n).
- Crucial quantifier order: w is fixed BEFORE choosing B. It can depend on
  N and on arbitrary nonlocal arithmetic data, but not on the selected B.
  This is NOT conditional independence of low colours and high factors.

WeightedUnitDiagonal:
- untruncatedComplementPrefix_one identifies X=1 with untruncatedRoughUnit.
- exists_weighted_unit_subpower_prefix_budget: for one prescribed bounded
  row-weight w(N,n), choose growing subpower B and growing H, H<=B+1, with
  C(N)>=0, C(N)=o(N), C bounding EVERY rough-small-divisor sampling prefix,
  and mean w(N,n)*untruncatedRoughUnit(B(N),n)->0.
- Does not also assert unweighted cancellation, or preservation of the
  earlier B,H,U,Y chosen in EscapingComplementCriterion.

HighComplementAlgebra:
- highDivisorWeight(W,X,n) = sum_{e|R_W,1<e<=X} mu(e).
- highComplementAt(B,D,W,X,n) retains mu(R_B), sideColour(n,R_B/e), and
  the actual D*e<R_B condition, summing over e|R_W,1<e<=X.
- highComplementAt_original_support proves this is EXACTLY the subrange
  of the original R_B-divisor sum with W<minFac(e), when B<=W,n>0.
- If R_B has a prime <=W and D*X<R_B, then
    highComplementAt = highDivisorWeight * untruncatedRoughUnit.
  Deleting a divisor all of whose primes exceed W cannot change minFac R_B.
- If 1<W, N+1<=W^L, and 0<n<=N, both the high weight and the actual high
  complementary sum are absolutely bounded by 2^(2L). Proof bounds the
  number of rough primes by 2L, then counts their squarefree divisor subsets.
- At n=0 both high expressions are exactly zero.

SubpowerOccupiedBand:
- subpower_below_power_cutoff: N+1<=W(N)^L with fixed L>0 and subpower B
  implies every fixed B^k<=W eventually.
- empty_subpower_band_zero: if B->infinity is subpower and W dominates every
  B^k, the empty-prime-band (B,W] proportion tends to zero. Uses the existing
  variance/iterated-band estimate, not a new independence assertion.
- rough_radical_small_proportion_zero: for D(N)^2<=(N+1)^3, the UNshifted
  proportion R_B(n(n+1))<=D tends to zero. Retains the endpoint error when
  transferring the previous shifted radical estimate.

HighComplementCancellation:
- highComplementAt_mean_absolute_error_zero: for any growing subpower B,
  any W with 1<W and N+1<=W^L (fixed L>0), and any D,X with
  (D*X)^2<=(N+1)^3, the mean ABSOLUTE difference from
  highDivisorWeight(W,X,n)*untruncatedRoughUnit(B,n) tends to zero.
  The pointwise error is <=2*2^(2L) times the sum of the empty-band and
  small-radical indicators. Both exceptional sets were proved negligible.
- MAIN exists_high_complement_cancellation: for ANY such W and ANY X with
  X(N)^4<=N eventually, unconditionally choose B,H,C with growing subpower
  B, growing H, H<=B+1, and the full uniform o(N) small-divisor prefix budget,
  such that mean highComplementAt(B,H*N,W,X,n)->0.
  This is genuine signed cancellation of an ACTUAL nonunit subrange, with
  all weights and the size condition restored, not merely an equivalent
  criterion or an absolute upper bound.

LIMITATIONS:
- W is a fixed-positive-power (or larger) cutoff in this theorem, not the
  subpower Y of the earlier escaping-complement criterion.
- The condition is EVERY prime of e exceeds W (W<minFac(e)), NOT merely
  P(e)>W. Mixed low/high complementary divisors remain unestimated.
- Products above the safe X-window remain unestimated too.
- These B,H are chosen for this weight; no simultaneous compatibility with
  the earlier maximal-prefix/escaping cutoffs has been proved.
- The tempting use of arbitrary bounded weights does not solve the full
  tail: its radical cutoff, parity and side colour depend on B itself.

The target is STILL UNRESOLVED. Spec.lean was not edited, has SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff,
and `lake env lean Submission/Spec.lean` still reports the original sorry.
Latest resources: 47h56m22s used, 48h03m38s remaining; $564.73 used,
$435.27 remaining (before this log write). No successful proof submission.

# Mixed low/high rectangles and almost-quadratic rough radicals

Ten new complete modules (1253 lines total), all compiled with saved oleans:
  WeightedPrefixDiagonal.lean
  MixedComplementRectangle.lean
  ThinSubpowerBand.lean
  MixedRectangleError.lean
  MixedRectangleCancellation.lean
  MixedRectangleSupport.lean
  GrowingMixedRectangle.lean
  RoughPartPowerBounds.lean
  RoughRadicalPowerBounds.lean
  LargeWindowMixedRectangle.lean
All printed transitive axiom checks use only propext, Classical.choice,
Quot.sound. No admissions, new axioms, or native_decide in these modules.
No unfinished exploratory file was left by this continuation.

WeightedPrefixDiagonal strengthens the preceding weighted-unit diagonal:
- For one prescribed |w(N,n)|<=1, chosen independently of the selected B,
  exists_weighted_untruncated_prefix_cutoffs selects ONE B,H,C with growing
  subpower B, growing H, H<=B+1, and the uniform o(N) small-divisor prefix
  budget. For EVERY fixed k and epsilon, ALL F<=B^k have vanishing means
  w(N,n)*untruncatedComplementPrefix(B,F,n).
- The earlier exponent-weighted K(N)*logB/logN control is retained internally.
- This still does NOT allow w to depend on the chosen cutoff B.

MixedComplementRectangle defines the ACTUAL sum
  mixedComplementRectangleAt(B,D,W,F,X,n)
    = mu(R_B) * sum_{f|R_B,g|R_W, f<=F,1<g<=X,D*f*g<R_B}
                  mu(f*g)*sideColour(n,R_B/(f*g)),
  R_T=roughRadical(T,n(n+1)).
- small_high_coprime: f>0, f<=W, g|R_W imply gcd(f,g)=1.
- short_rough_prime_card: f|R_B,f<=B^k implies omega(f)<=k (B>1).
- If more than k primes in (B,W] divide n(n+1), a prime <=W survives after
  deleting f<=B^k. Deleting g|R_W then cannot change the least-prime colour.
- mixedComplementRectangleAt_factor: if B^k<=W,F<=B^k and
  D*B^k*X<R_B, the actual expression equals
    highDivisorWeight(W,X,n)*untruncatedComplementPrefix(B,F,n).
- For 1<W and N+1<=W^L, the mixed rectangle is absolutely bounded by
    2^(2L)*2^(active count in (B,B^k]).
  This is a finite estimate, not a signed cancellation assumption.

ThinSubpowerBand:
- thin_subpower_band_zero: for growing subpower B and W dominating every
  fixed B-power, inputs with at most k active primes in (B,W] have density
  zero, for each fixed k. Uses the existing variance/iterated-band estimate.
- shifted_indicator_mean_zero keeps the sample endpoint explicit.
- short_band_exp_exception_zero: the full exponential low-band weight
  2^(active count in (B,B^k]) has vanishing mean on ANY density-zero
  exceptional set. Uses the established exponential moment and Cauchy--
  Schwarz, not independence of that set.
- Generic predicate lemmas take [forall N n, Decidable (Q N n)]. This avoids
  a Classical.propDecidable/decLe elaboration mismatch seen during proof.

MixedRectangleError:
- mixedRectangle_point_error bounds the discrepancy from the factored
  expression by 2*2^(2L)*2^m times the sum of two exceptional indicators:
  the thin (B,W] event and R_B<=D*B^k*X.
- mixedRectangle_mean_error_uniform controls its mean ABSOLUTE value,
  uniformly for all F<=B^k, initially under (D*B^k*X)^2<=(N+1)^3.
  All side colours, Möbius factors, and the actual size cutoff are retained.

MixedRectangleCancellation:
- highWeightedPrefix_shift_error: endpoint error <=2^(2L)*(F+1)/N; the
  initial high weight at n=0 is exactly zero.
- exists_high_weighted_prefix_cutoffs accommodates highDivisorWeight(W,X)
  as the bounded external target and works for all fixed low degrees.
- exists_mixed_rectangle_cancellation: for prescribed W,X with fixed L>0,
  N+1<=W^L, 1<W, and X^4<=N, chooses ONE B,H,C with the prefix budget and
  cancels the actual shifted mixed rectangle uniformly for EVERY fixed k
  and EVERY F<=B^k. This genuinely includes mixed low/high indices.

MixedRectangleSupport:
- small_high_factor_unique: products f*g have unique factorization in the
  indicated separated ranges. The proof uses coprime divisibility, not a
  heuristic about prime patterns.
- mixedComplementSupport is the image of the finite allowed factor pairs.
  It is a subset of R_B.divisors when B<=W and F<=W.
- mixedComplementRectangleAt_original_support rewrites the double sum
  exactly as the original complementary sum restricted to this support.
  There is NO multiplicity overcounting.
- mixedComplementRectangleAt_one equals highComplementAt exactly.

GrowingMixedRectangle:
- exists_growing_rectangle_window applies a constrained diagonal to the
  uniform fixed-degree results without changing B,H.
- exists_cancelled_growing_mixed_rectangle selects a growing subpower U,
  eventually U<=W, dominating every fixed B^k, such that ALL F<=U have
  vanishing mixed-rectangle means. The small-divisor prefix budget persists.
- proper_low_mixed_rectangle_cancellation removes f=1 on the SAME cutoffs:
  rectangle(F)-highComplementAt has zero mean uniformly for 1<=F<=U.
  Thus the proper mixed part is cancelled, not merely its sum with an
  uncontrolled high-only contribution.

RoughPartPowerBounds and RoughRadicalPowerBounds improve the product window:
- smallRoughPartPowerCount(B,q,N) counts (roughPrimePart(B,n+1))^(q+1)<=N^q.
- Its logarithmic deficit bound is
    count*log N <= (q+1)*N + 4*(q+1)*N*log(B+1).
  Its normalized count at N+1 tends to zero for any subpower B and fixed q.
- If both consecutive rough parts exceed the corresponding threshold and
  have no repeated prime above B, their product divides R_B and gives
    (N+1)^(2q)<R_B^(q+1).
- roughRadical_small_power_proportion_zero: for ANY fixed q and ANY threshold
  D(N) with D^(q+1)<=(N+1)^(2q), the shifted proportion R_B<=D tends to zero.
  Uses only the deficit bound and the already negligible large-square set.
  This allows every fixed exponent below 2, rather than only 3/2.

LargeWindowMixedRectangle is the strongest new signed result:
- mixedRectangle_mean_error_of_radical abstracts the absolute-error proof
  to any proved density-zero small-radical event.
- exists_large_window_mixed_rectangle: for fixed L>0 and q>=2, prescribed
  W,X with 1<W, N+1<=W^L, and
    X(N)^(2q)<=N^(2q-3),
  choose ONE B,H,C with growing subpower B, growing H, full small-divisor
  prefix budget, and uniform cancellation for EVERY fixed k and F<=B^k.
- exists_cancelled_growing_large_rectangle additionally selects subpower
  U->infinity, U<=W eventually, dominating every fixed B-power, and controls
  ALL F<=U in these larger high-factor product windows.
- As q may be any fixed integer >=2, the permitted high-factor exponent
  1-3/(2q) can be arbitrarily close to 1. q is FIXED before N tends to
  infinity; no unproved moving-q coverage or full-endpoint conclusion.

REMAINING GAP / QUANTIFIER LIMITS:
- These estimates still require the LOW factor f to be <=U. They do not
  control an unrestricted W-smooth part of the complementary index.
- W is fixed-positive-power or larger in the current statements. B,U are
  subpower. Dominating all B^k does not make U cover all W-smooth divisors.
- The actual high endpoint near N/H has not yet been fully covered.
- B,H,C are selected for the prescribed external W,X weight. Compatibility
  with the prior unweighted maximal-prefix/escaping-complement cutoffs is
  not asserted, nor is uniformity over arbitrary choices of X.
- Hence NO complete proof, disproof, or density-half conclusion follows.

A possible next NEW range estimate (not implemented or proved here):
To remove the high endpoint restriction for fixed L, bound the absolute
reciprocal mass of W-rough squarefree integers in a narrow logarithmic band
near N. A one-dimensional specialization of residue_selberg_upper_bound
with residues {0}, sieve cutoff z<=W, and product cutoff (z+1)^8 should give
rough-count <=2*exp(1)*M/log(z+1)+2*(z+1)^32. Dyadic summation could then
bound the reciprocal mass in [N^(1-delta),N] by O_L(delta)+o(1). Combined
with the elementary <=2^omega(g)*(N/g+1) bound for g|n(n+1), this might
control high endpoint errors (including their short-factor weights via
Cauchy--Schwarz). Neither this particular sieve specialization, its band
consequence, nor full endpoint removal has been formalized in this session.
Even if successful, the unrestricted low factor remains a real obstacle.

Spec.lean remains UNCHANGED and UNRESOLVED with original sorry; SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
`lake env lean Submission/Spec.lean` still warns that erdos_371 uses sorry.
Latest resources: 48h23m12s used, 47h36m48s remaining; $570.87 used,
$429.13 remaining (before this log write). No successful proof submission.

RoughSelbergBound (completed after the preceding entry):
- siftedCount z M counts n<M avoiding every prime <=z.
- siftedCount_selberg_exp: count <= 2*M*exp(-primeHarmonic z)+2*(z+1)^32.
- siftedCount_selberg_bound, for z>=1 and EVERY M:
    count <= 2*exp(1)*M/log(z+1)+2*(z+1)^32.
- One-dimensional specialization of residue_selberg_upper_bound; prime
  residues {0}, product cutoff (z+1)^8, no PNT or omitted rounding errors.
- Compiles; axioms [propext, Classical.choice, Quot.sound].
- No reciprocal-band theorem or endpoint removal is claimed yet.

FULL HIGH ENDPOINT REMOVAL (new checked result, after RoughSelbergBound)

All following modules compile and their main results depend only on
[propext, Classical.choice, Quot.sound]. Saved .olean files are present.

RoughReciprocalBand:
- rough_dyadic_reciprocal_le: rough reciprocal mass of a binary block j is
  <=4*exp(1)/log(z+1)+2*(z+1)^32/2^j.
- rough_band_reciprocal_le: multiplies by the number b+1-a of binary blocks.
- rough_interval_reciprocal_le for 1<=A<=N:
    sum_{m in S}1/m <= ((log N-log A)/log 2+2)*
      (4*exp(1)/log(z+1)+4*(z+1)^32/A),
  when S lies in [A,N] and avoids primes <=z. All errors retained.

RoughDivisorEndpoint:
- consecutive_shifted_root_count_le:
    #{n<N:d|(n+1)(n+2)} <= (N/d+1)*#divisors(d).
  Uses quotient/remainder injection and previous root-count bound.
- For 0<d<=N the normalized count is <=2*#divisors(d)/d.
- For squarefree W-rough d<=N<=W^L, #divisors(d)<=2^L.
- rough_divisor_event_proportion_le: a union of such divisor events is
  bounded by 2^(L+1) times the rough reciprocal mass.

RoughEndpointScale:
- exists_rough_endpoint_scale: for fixed L>0 and N<=W(N)^L, selects a
  FIXED K and a growing z<=W such that N<=(z+1)^K and (z+1)^128<=N.
- Explicitly z=rootRoughCutoff(256*(L+1)-1); log-ratio estimates justify
  every power inequality. No exponent moves with N.

RoughThinEndpoint:
- rough_interval_power_bound combines the finite reciprocal estimate
  with N<=(z+1)^K, (z+1)^128<=N<=A^2.
- rough_thin_endpoint_reciprocals_zero: for A in [1,N], log A/log N ->1,
  and W bounded below by a fixed power, the reciprocal mass of ANY
  finite W-rough set in [A,N] tends to zero.
- The sieve error vanishes because A>=(z+1)^64, reducing it to
  O_K(log(z+1)/(z+1)^32), not by discarding it.

RoughHighEndpointEvent:
- roughEndpointDivisors W A N: squarefree W-rough divisors in [A,N].
- highEndpointCount W A N counts n<N with some divisor of
  roughRadical W ((n+1)*(n+2)) in [A,N].
- highEndpointCount_proportion_zero and highEndpoint_indicator_mean_zero
  establish density zero for this event if log A/log N ->1, for fixed L.

AlmostLinearRadicalThreshold:
- nat_power_eventually_le_of_log_ratio: converts a STRICT limiting
  logarithmic exponent bound into an eventual integer-power bound.
- short_radical_threshold_zero packages the earlier fixed-q estimate.
- exists_almost_linear_radical_threshold: for growing subpower B and
  H<=B+1, and each FIXED low degree k, selects A with 1<=A<=N,
  log A/log N ->1, and negligible event
    roughRadical(B, (n+1)*(n+2)) <= (H*N)*(B^k*A).
- Proof uses X_j=ceil(N^(1-2/(j+4))), checks the fixed j estimate first,
  then selects j by a finite-max diagonal controlling the actual error.
  A may depend on k. It is only an analysis threshold, NOT an external
  weight used in cutoff selection.

FullEndpointRectangleError:
- mixed_high_cutoff_invariant: without a high divisor in [A,N], both
  the actual mixed rectangle and its factored weight are unchanged when
  the high endpoint is reduced from N to A.
- mixed_full_endpoint_point_error compares full error with error at A
  plus 2*2^(2L)*2^(low active count) times the high-endpoint indicator.
- mixed_full_endpoint_mean_error: uniform in F<=B^k, the actual full
  rectangle at g<=N differs in mean absolute value by o(1) from
    highDivisorWeight(W,N)*untruncatedComplementPrefix(B,F).
  Uses the controlled A diagonal, the endpoint density-zero theorem,
  and the previous uniform-integrability lemma for exponential weights.

FullEndpointMixedRectangle (STRONGEST SIGNED RESULT):
- exists_full_endpoint_mixed_rectangle: for prescribed W, fixed L>0,
  1<W, N+1<=W^L, selects B,H,C with all prior uniform small-divisor
  prefix-budget properties, and cancels the actual mixed rectangle with
  HIGH ENDPOINT EXACTLY N for EVERY fixed k and every F<=B^k.
- exists_cancelled_growing_full_rectangle further selects subpower U->infty,
  dominating all fixed B^k and <=W, and gives uniform cancellation for
  all F<=U, again with HIGH ENDPOINT EXACTLY N.
- The external weight highDivisorWeight(W,N) is fixed BEFORE selecting B.
  No hidden dependence of that weight on the selected cutoff was used.

WHAT IS STILL NOT PROVED:
- Unrestricted low factor f>U (W-smooth or mixed); full high endpoint
  removal alone does NOT cancel the entire escaping-complement sum.
- Compatibility with the older unweighted-prefix criterion's cutoffs
  remains a separate issue; no such compatibility is asserted here.
- No proof or disproof of erdos_371 follows yet. Spec.lean is unchanged.

Status at end of continuation:
- The proposed high-factor endpoint removal is now fully checked, as above.
- The unrestricted low factor is NOT covered. U is subpower whereas W may
  be a fixed positive power of N, and domination of all fixed B^k does not
  permit replacing the short low-factor window by the entire low support.
- The final conjecture remains unresolved; no proof/disproof was submitted.
- Spec.lean remains unchanged, with its original sorry and import list.

COMMON CUTOFFS AND THE MIDDLE-PRIME REMAINDER (new continuation)

All modules below compile with saved .olean files. Their main axiom checks
use only [propext, Classical.choice, Quot.sound]. Spec.lean is unchanged.
A request to https://www.erdosproblems.com/371 failed with DNS resolution
error; no online result was obtained or assumed.

1. TwoTargetBessel.lean
   finite_bessel_two_target_selection permits a Bool-valued choice of target
   at EACH witness. Sufficient condition is 4*(1/K+eta)<epsilon^2. Proof uses
   the old absolute-sum Bessel bound for each target and Cauchy--Schwarz;
   arbitrary correlations are NOT assumed independent.
2. TwoTargetPatternSelection.lean
   Two-target version of odd-pattern Bessel selection. The target assignment
   may vary with the witness, while all original locality/flip conditions
   and actual natural-prefix Gram estimates are retained.
3. TwoTargetShortSelection.lean
   Polynomial clipping transfers that selection to fixed-degree short
   complementary patterns, still allowing adversarial target assignment.
4. TwoTargetMaximalSelection.lean
   A SINGLE block is good for BOTH targets and EVERY product endpoint X.
   A hypothetical bad target/endpoint pair in every block is chosen and
   contradicts the preceding adversarial-pair selection theorem.
5. TwoWeightComplementSelection.lean
   exists_power_cutoff_two_weight_maximal_cancellation: arithmetic transfer
   to two prescribed bounded row-weights, with the same selected B and all
   X<=B^k. Every witness and occupancy error remains explicit.
6. TwoWeightPrefixDiagonal.lean
   The row and constrained-diagonal arguments now select B,H,C controlling
   both weights, every fixed short degree, and the uniform sampling-prefix
   budget C=o(N). Weights are still prescribed BEFORE selecting B.
7. JointHighPrefixCutoffs.lean
   exists_joint_untruncated_prefix_cutoffs combines an arbitrary bounded
   weight with weight 1. exists_joint_high_weighted_prefix_cutoffs uses the
   normalized highDivisorWeight(W,X), retaining BOTH its shifted estimate
   and the ordinary unweighted prefix on the SAME cutoffs.
8. JointFullEndpointCutoffs.lean
   exists_joint_full_endpoint_prefixes restores the actual size cutoffs for
   ordinary prefixes and full-high mixed rectangles simultaneously.
   exists_joint_growing_full_cutoffs takes the minimum of the two controlled
   growing degree windows. It selects ONE B,H,U,C with all original small
   divisor-budget properties and uniform cancellation of BOTH:
     complementPrefixAt(B,H*N,F),
     mixedComplementRectangleAt(B,H*N,W,F,N),
   for every F<=U. U is subpower, dominates all fixed B^k, and U<=W.
   This removes the previously recorded cutoff-compatibility gap.
9. UncoveredComplementCriterion.lean
   mixedComplementSupport_has_large_prime: each mixed index has P(e)>W,
   hence e>U when U<=W. Thus it overlaps neither the ordinary prefix nor
   the removed Y-smooth part (Y<=U<=W).
   uncoveredComplementAt retains exactly the original Mobius, side colour,
   and size condition, restricting e>U, P(e)>Y, and e outside the cancelled
   mixed support. exists_uncovered_complement_criterion is an unconditional
   equivalence to the ORIGINAL conjecture using the new COMMON cutoffs.
10. CanonicalLowComplement.lean
   roughRadical_dvd_of_dvd and roughRadical_small_high_product provide the
   canonical factorization e=f*g with g=roughRadical(W,e), f=e/g.
   mixedComplementSupport_iff_canonical identifies the mixed support with
   f<=F, 1<g<=X (for F<=W and e dividing the original rough radical).
   For U<e<=N, exclusion from the full-high mixed support is EQUIVALENT to
     U<e/roughRadical(W,e).
   Actual size-cutoff indices satisfy e<=N when H>=1 and n<=N.
   uncoveredComplementAt_eq_longLow therefore gives the exact canonical
   low-factor version, not just a majorant.
11. SmoothLowComplementCount.lean
   smoothComplementCount_mean_zero controls the actual NUMBER of long
   smooth low factors, stronger than the prior signed-sum absolute bound.
   exists_smooth_complement_count_cutoff chooses Y dominating all fixed
   B-powers, Y<=U, with this count's normalized mean tending to zero.
   smoothLowComplementCount counts indices whose canonical W-smooth part
   is >U and supported in (B,Y]. Injecting into (low factor, high factor)
   bounds it by smoothComplementCount * #divisors(R_W).
   Since #divisors(R_W)<=2^(2L), the count still has zero normalized mean
   with an ARBITRARY attached high divisor, for each fixed L.
12. MiddlePrimeComplement.lean
   canonical_low_prime_small: every prime of e/roughRadical(W,e) is <=W
   for squarefree e. Absence of a prime in (Y,W] then makes that cofactor
   supported entirely in (B,Y].
   middlePrimeComplementAt retains the exact summands with:
     U < e/roughRadical(W,e),
     some prime p with Y<p<=W dividing e,
     D*e < roughRadical(B,n(n+1)).
   longLow_middle_point_error is bounded by smoothLowComplementCount.
   longLow_middle_mean_error_zero proves the corresponding mean ABSOLUTE
   error is zero using the preceding count estimate. This is a new genuine
   range removal; it does not assert cancellation of the middle term.
13. MiddlePrimeCriterion.lean
   exists_middle_prime_complement_criterion is the strongest exact reduction.
   For any prescribed W and fixed L>0 with 1<W and N+1<=W^L, it selects
   B,H,U,Y tending to infinity, B,U subpower, Y<=U<=W, and Y dominating all
   fixed B-powers, such that the ORIGINAL density conjecture is equivalent
   to vanishing of the shifted normalized mean of middlePrimeComplementAt.
   All three removals (ordinary prefix, full-high mixed support, and long
   Y-smooth low factors with arbitrary high attachment) are on these cutoffs.

REMAINING UNSOLVED TARGET:
Write R_B=roughRadical(B,n(n+1)). The remaining mean has summands
  mu(R_B) * sum_{e|R_B, U<e/roughRadical(W,e),
                  exists prime p: Y<p<=W and p|e, H*N*e<R_B}
                 mu(e)*sideColour(n,R_B/e).
No signed cancellation estimate for this middle-band term has been proved.
Neither Y dominating B^k nor U being subpower permits replacing Y by W.
The original conjecture has not been proved or disproved.

Additional unimplemented strategy caution:
For all complementary PRIME indices, a naive untruncated expansion weights
rough-unit observables by the total remaining rough-prime count, not merely
by a bounded local short-band count. In a K-block selection family that
count can grow with K. The existing bounded-target Bessel theorem does NOT
control this automatically; normalization and a growing number of blocks
must not be treated as independent. No unrestricted-degree conclusion follows.

CHECKED DAMPING LEMMAS
----------------------
DampedAlladi.lean defines dampedColour(t,c,P) as the subset-minimum
Alladi sum with each subset weighted by t^card. It proves the exact
maximum-insertion recursion D(P union {p})=t*c(p)+(1-t)*D(P), |D|<=1
for 0<=t<=1 and |c|<=1, and |D-c(max P)|<=2*(1-t), uniformly in #P.
DampedComparison.lean specializes this to the prime-side colour of n(n+1).
At t=1 it equals factorSign for n>1, and its mean absolute approximation
error is at most 2*(1-t)+4/N. density_of_damped_cancellation proves the
original density conclusion IF fixed-parameter natural mean cancellation
is established along parameters t_k in [0,1] tending to 1.
Both modules compile; their main theorems use only propext,
Classical.choice, Quot.sound. No required damped arithmetic cancellation
has been proved. Analytic continuation is only an unimplemented idea,
and cannot help without a nontrivial open set of cancellation first.


QUADRATIC DAMPING: CHECKED SMALL-PRODUCT CANCELLATION AND LARGE-PAIR REMAINDER
---------------------------------------------------------------------------
The original conjecture remains UNRESOLVED. Spec.lean has not been edited.
This continuation checked the previously suggested cross-prime-pair star
observation and carried the quadratic expansion through to its exact mean.

New checked files (all saved .olean files, only permitted axioms):

1. DampedPrimePairs.lean
   large_cross_prime_pair_max: if n>0, n+1<=N, primes p|n, q|n+1,
   and pq>N, then max(p,q)=P(n(n+1)). Any unused larger prime would make
   either n or n+1 exceed N. large_cross_prime_pair_order proves that p<q
   iff P(n)<P(n+1). Defines largeCrossPrimePairs(N,n), retaining every
   such actual cross-prime pair, and largeCrossPrimePairSkew(N,n).
   largeCrossPrimePairSkew_eq / _eq_of_pos give the exact identity
     largeCrossPrimePairSkew(N,n) = #largeCrossPrimePairs(N,n)*factorSign(n).
   largeCrossPrimePairs_variable_weight checks at cutoff 30 that n=8 has
   weight 0 and n=20 has weight 1 (both are rises). No constant-weight
   substitution is justified.

2. DampedCoefficients.lean
   dampedCoefficient(k,c,P) = -sum_{E subset P, |E|=k} subsetMinTerm(c,E).
   dampedColour_degree_expansion gives the exact finite polynomial.
   The zero coefficient is zero; the linear coefficient is sum c(p).
   dampedFactorSign_linear_prefix telescopes exactly to omega(N+1).
   powersetCard_two_min_sum and dampedCoefficient_two express degree two
   as minus the sum of c(p) over p<q in P. All equalities are finite.

3. ShortPrimePairCancellation.lean
   shortPrimePairs(N) consists of unordered distinct prime pairs p<q,
   pq<=N. ordered_prime_product_injective proves product injectivity.
   shortPrimePairs_count_bound:
     #shortPrimePairs(N) <= (B+1)*pi(N)+roughNumberCount(B,N+1).
   Splitting off fixed small prime factors and using small totient ratios
   proves shortPrimePairs_count_zero: #shortPrimePairs(N)/N -> 0.
   shortPrimePairSkew(N,n) sums the ACTUAL signed residue discrepancies
   1_{p|n,q|n+1}-1_{q|n,p|n+1} over these pairs.
   shortPrimePairSkew_prefix_bound bounds any sampling prefix by the
   number of pairs, using the checked discrepancy-at-most-one for EACH
   pair. shortPrimePairSkew_mean_zero and _succ_mean_zero prove genuine
   UNCONDITIONAL signed cancellation on pq<=N (or cutoff N+1).

4. DampedQuadratic.lean
   dampedCoefficient_two_union proves the disjoint two-colour identity.
   With crossPrimeSkew(n)=sum_{p|n,q|n+1} sign(q-p),
   dampedFactorSign_quadratic_coefficient gives
     Q(n) = choose(omega(n),2)-choose(omega(n+1),2)+crossPrimeSkew(n).
   No mean estimate is built into this identity.

5. QuadraticPrimeSplit.lean
   shortPrimePairSkew_eq_cross identifies the actual small-product
   cross-prime portion, with no extraneous ambient-prime terms.
   crossPrimeSkew_split is the exact small+large hyperbola partition.
   dampedFactorSign_quadratic_split combines this with the star identity:
     Q(n)=choose(omega(n),2)-choose(omega(n+1),2)
          +shortPrimePairSkew(N,n)+#largeCrossPrimePairs(N,n)*factorSign(n).

6. PrimeFactorCardEndpoint.lean
   primeFactors_card_log_bound: omega(n)<=log(n)/log(2).
   primeFactors_choose_endpoint_zero and _succ_endpoint_zero show that
   choose(omega(N),k)/N and choose(omega(N+1),k)/N tend to zero for every
   FIXED k. dampedFactorSign_linear_mean_zero proves the linear damping
   coefficient's shifted natural mean tends to zero.

7. QuadraticDampingMean.lean
   Defines quadraticFactorSign(n)=Q(n). The same-side binomial terms
   telescope exactly. quadraticFactorSign_mean_large_pair_error proves
     mean_{n<N} Q(n+1)
       -mean_{n<N} #largeCrossPrimePairs(N+1,n+1)*factorSign(n+1) -> 0.
   BOTH removed means are unconditionally zero: the endpoint binomial
   term and the signed short-product skew. The remaining mean is not
   asserted to vanish. This is a quadratic obstruction to the damping
   strategy, not a settlement of the density conjecture.

8. QuadraticTailAbsoluteObstruction.lean
   Uses the previously checked positive proportion of consecutive pairs
   with BOTH largest prime factors above N^(21/40). Each such pair yields
   an actual cross-prime pair of product>N+1, for all sufficiently large N.
   largeCrossPrimePairs_mean_positive proves eventually
     (1/N) sum_{n<N} #largeCrossPrimePairs(N+1,n+1) >= 1/20.
   quadratic_large_pair_absolute_mean_not_zero proves that the ABSOLUTE
   mean of the exact weighted-sign remainder does NOT tend to zero.
   This disproves only an absolute-tail shortcut, NOT Erdős 371.

Current arithmetic blocker:
Even the quadratic damping coefficient retains an unestimated signed
large-prime-pair mean of positive absolute mass. The telescoping linear
coefficient and the small-product quadratic cancellation do not give an
open interval of fixed-parameter damped cancellation. Analytic continuation
has no established arithmetic starting interval. No such continuation was
formalized or used. The earlier middlePrimeComplementAt signed target is
also still unestimated. Do not submit the original theorem as solved.


SMALL-PRIME OVERSHOOT SIEVE AND UNIFORM INTEGRABILITY (new continuation)
---------------------------------------------------------------------
Status: Spec.lean is unchanged. The original density conjecture remains
UNRESOLVED; no proof or disproof has been submitted.

A review of the existing inverse-residue estimates found no valid way to
apply them to the prime-restricted quadratic remainder at the needed scale.
The unweighted inverse-curve error cannot be silently turned into a
prime-weighted estimate, and summing it absolutely over the large moduli is
too costly. No new signed interior estimate was claimed.

Instead, this continuation obtained a new arithmetic edge estimate. If
p*q>N, p<=X, and q divides the relevant adjacent integer m<=N, the cofactor
a=m/q satisfies 1<=a<p. Hence the q-count is in one invertible progression
modulo p. Summing the one-prime sieve over a<p costs (1+log p)/p, whose prime
sum is O(log X). This retains every marked pair, rather than just counting
the union of their supporting inputs.

New checked files (saved .olean files; main axioms all permitted):

1. PrimeResidueSelberg.lean
   primeResidueSet_selberg_bound: for prime p, r<p, z>=1,
     #{q<L: q prime, q>z, q mod p=r}
       <= 2*exp(2)*L/(p*log(z+1)) + 2*p^8*(z+1)^32.
   Uses the checked progression Selberg sieve and removes p from the
   sieving primes. The modulus factor 1/p and polynomial error are kept.
   prime_linear_congruence_bound applies the same bound to a*q=b mod p
   when a is invertible modulo p; choosing the residue is legitimate even
   though parameters vary.

2. PrimeDivisorOvershoot.lean
   primeDivisorOvershoot(D,p,b) counts (m,q) with 1<=m<=D, q prime,
   q|m, D<p*q, m=b mod p. Its cofactor map (m,q)->(m/q,q) is injective.
   primeDivisorOvershoot_bound, with p*z<=D and p<=D:
     card <= 4*exp(2)*D*(1+log p)/(p*log(z+1))
             +2*p^9*(z+1)^32.
   prime_log_harmonic_weight_bound:
     sum_{p<=X} (1+log p)/p <= 9*log(X+1).
   small_prime_overshoot_total_bound sums BOTH residues 1 and p-1:
     sum_{p<=X} [card(D,p,1)+card(D,p,p-1)]
       <=72*exp(2)*D*log(X+1)/log(z+1)+4*(X+1)^10*(z+1)^32.

3. SmallPrimePairOvershoot.lean
   smallCrossPrimePairs(D,X,n) is the ACTUAL subset of
   largeCrossPrimePairs(D,n) with min(p,q)<=X.
   leftSmallCrossPrimePairs_sum_bound and rightSmallCrossPrimePairs_sum_bound
   inject the two orientations into the preceding overshoot sets, with the
   exact neighboring endpoints and congruences retained.
   smallCrossPrimePairs_finite_bound bounds the SUM of these multiplicities
   for n<D by the same 72*exp(2) main term and full polynomial error.

4. SmallPrimePairTailMean.lean
   Uses the fixed sieve scale z=rootRoughCutoff(511,N).
   smallCrossPrimePairs_normalized_bound, under (X+1)^40<=N,
   (z+1)^128<=N and N<=(z+1)^512, gives
     mean #smallCrossPrimePairs(N,X,n)
       <=36864*exp(2)*log(X+1)/log N + 4/sqrt N.
   The polynomial error is bounded using fourth powers, not discarded.
   smallCrossPrimePairs_eventually_mean_le: if the logarithmic cutoff ratio
   tends to v<1/40, the mean is eventually <=36864*exp(2)*v+epsilon.
   smallCrossPrimePairs_subpower_mean_zero proves mean ABSOLUTE count ->0
   for EVERY prescribed subpower cutoff X that is eventually >=1. No slow
   diagonal or restriction on how X was selected is needed here.

5. QuadraticSubpowerPrimeEdge.lean
   Checks the sampling shift explicitly: cutoff D=N+1 and samples n+1,
   n<N, match the raw prefix of length D because the zero input contributes
   no pair. Division by N versus N+1 is handled by their ratio ->1.
   smallCrossPrimePairs_shifted_weighted_mean_zero allows ANY attached
   uniformly bounded weight, including one depending on X; this is valid
   because the count estimate is absolute (unlike the Bessel selections).
   highMinCrossPrimePairs(D,X,n) retains precisely min(p,q)>X.
   quadraticFactorSign_mean_highMin_error proves
     mean Q(n+1)
       -mean #highMinCrossPrimePairs(N+1,X(N+1),n+1)*factorSign(n+1) ->0
   for every such subpower X. The retained signed mean is not evaluated.

6. LargePrimePairUniformIntegrability.lean
   primeFactors_above_card_bound and highMinCrossPrimePairs_card_bound:
   if N<=Y^K, Y>1, then at every sample n<N the above-Y pair count is <=K^2.
   Combine this bounded count with the small-prime edge at Y=rootRoughCutoff
   (k,N). Its limiting mean is O(1/(k+1)), with k FIXED first.
   largeCrossPrimePairs_uniform_integrability proves:
     for every epsilon>0 there exists a FIXED M such that eventually
       mean [#largeCrossPrimePairs(N,n) * 1_{count>M}] < epsilon.
   largeCrossPrimePairs_uniform_absolute_continuity: for ANY |w(N,n)|<=1
   whose mean absolute value tends to zero, the mean
     #largeCrossPrimePairs(N,n)*|w(N,n)|
   also tends to zero.
   largeCrossPrimePairs_negligible_exceptional_set is the corresponding
   density-zero exceptional-set corollary. This controls the unbounded
   multiplicity, not just its first moment.

Remaining blocker:
These results remove the complete subpower-prime edge and justify attaching
the large-pair multiplicity to negligible exceptions. They DO NOT prove
signed cancellation for the retained prime pairs. Even the quadratic damping
mean remains unestimated. Quadratic cancellation by itself would not settle
the full damping criterion, and no open interval of fixed-parameter damped
cancellation is known here. The earlier middlePrimeComplementAt criterion
for the ORIGINAL conjecture is also still unestimated.


HARMONIC ENDPOINT TRANSFER AND FINITE MIXTURES
---------------------------------------------------------------------
Spec.lean is unchanged. No proof or disproof of Erdős 371 is ready.

New checked files, with saved .olean files:

1. HarmonicDilationTransfer.lean
   logPrefixMean N F = (sum_{1<=n<=N} F(n)/n)/log N.
   harmonic_dilation_sum retains the exact endpoint N/p.
   logConditionedGap_dilation identifies the p-divisibility-conditioned
   gap-p correlation with the adjacent sum up to N/p, using the SAME log N
   denominator, under exact multiplier invariance.
   logConditionedGap_adjacent_bound bounds its difference from the full
   logarithmic adjacent mean by p/log N for fixed p.
   logConditionedGap_adjacent_error_zero allows endpoint-dependent labels
   with eventual exact invariance. No natural-mean endpoint claim is made.

2. FiniteMixtureLaw.lean
   sigmaLaw forms a finite mixture of finite laws, with the component index
   retained. mean_sigmaLaw gives its expectation formula.
   sigmaLaw_map_components preserves stationarity componentwise.
   sigmaLaw_map_common preserves a common pushforward marginal.
   sigma_iterate identifies componentwise iterates.

Next: apply entropy selection ONCE to a mixture of uniform cycles whose
lengths are all divisible by the finite required primorial product. This
should produce one common good scale for their weighted discrepancy.
It is invalid to integrate the existing pointwise existential transfer
without resolving the dependence of its chosen scale on the prefix.

Even a complete harmonic transfer would still need a signed prime-ergodic
estimate, and logarithmic density would not by itself prove natural density.
The original middle-prime complement criterion remains unestimated.


COMMON-SCALE HARMONIC PRIME TRANSFER: COMPLETED
---------------------------------------------------------------------
Spec.lean is STILL unchanged and the original conjecture is UNRESOLVED.
No complete proof, disproof, or submission has been made.

This continuation resolved the harmonic mixture construction described in
the preceding checkpoint. All files below compile with saved .olean files;
their main theorem axiom checks show only propext, Classical.choice, Quot.sound.

1. MixtureCyclicPrimeTransfer.lean
   cyclicMixtureLaw, cyclicMixtureShift, cyclicMixtureResidue describe a
   finite mixture of uniform cycles. Componentwise stationarity and a
   common exactly uniform residue marginal are checked.
   mixture_cyclic_prime_entropy_decrement selects its horizon BEFORE the
   index type, number of components, lengths, law, and labels.
   mixture_cyclic_gap_average_sq_le_information applies residue concentration
   to the JOINT mixture law, not to each component separately.
   mixture_cyclic_prime_gap_transfer selects ONE scale for the weighted
   mixture, simultaneously for every bounded pair observable. The mixture
   weights and labels must be fixed before selecting that scale.

2. HarmonicPrefixMixture.lean
   Exact positive-prefix identity (D=N+1):
     sum_{n<D} F(n)/(n+1)
       = prefixMean D F + sum_{1<=k<D} prefixMean k F/(k+1).
   harmonicPrefixLaw N is a probability law on Fin(N+1). Index zero has
   prefix length N+1 and weight 1/H_(N+1); index i>0 has length i and
   weight 1/((i+1)*H_(N+1)).
   harmonicPrefixLaw_representation identifies its mean of prefix averages
   with the normalized harmonic range average.
   harmonicPrefixLaw_reciprocal_length gives the EXACT identity
     E[1/prefixLength] = 1/H_(N+1).
   Thus fixed O(1/k) component errors cost O(1/H_(N+1)) after mixing.

3. HarmonicPrimeGapTransfer.lean
   harmonicRangeMean D F = sum_{n<D} F(n)/(n+1)/H_D.
   natural_cyclic_round_up_error bounds the discrepancy between a prefix
   k and a longer cycle M by
     [2*(B+1)*T+2*B*(B+1)]/k
   when k<=M, M-k<=T, and the gap is <=B<=M.
   For primorial product Q and finite horizon bound B, uses cycles
     M_i = Q*(prefixLength_i/Q+B+1),
   retaining M_i-prefixLength_i <= Q*(B+1).
   harmonic_range_prime_gap_transfer integrates these errors with the exact
   reciprocal-prefix moment and selects a single scale for the entire
   harmonic range mean. It does not integrate independently selected scales.

4. HarmonicStablePrimeTransfer.lean
   harmonicMean D F = sum_{1<=n<=D} F(n)/n/H_D.
   harmonic_range_Icc_sum_error bounds the UNNORMALIZED difference between
   sum_{n<D} F(n)/(n+1) and sum_{1<=n<=D} F(n)/n by 2 for |F|<=1.
   harmonic_prime_gap_transfer controls the actual Icc harmonic discrepancy.
   harmonic_stable_gap_error uses exact dilation and the common H_D
   denominator; replacing the shorter endpoint D/p by D costs <=p/H_D.
   stable_harmonic_prime_transfer therefore approximates the FULL adjacent
   harmonic mean by a prime-gap average at one selected finite scale.
   This does not claim cancellation of the remaining prime-gap mean.

5. PowerPrefixQuantization.lean
   Extends the checked global-cutoff approximation from N<=T^2 to N<=T^K
   for ANY fixed integer K. The near-tie width is K/Q.
   quantFactorSign_power_prefix_approximation chooses a resolution depending
   on K and tolerance, uniformly in all finer resolutions and all such N,T.

6. HarmonicQuantizedTransfer.lean
   primeQuantLabel_harmonic_prime_transfer specializes the stable harmonic
   transfer to the ACTUAL labels primeQuantLabel Q (N+1). Their invariance
   under every multiplier up to the finite horizon bound holds eventually,
   uniformly for all inputs. No approximate-dilation assumption is hidden.

7. HarmonicComparisonApproximation.lean
   harmonicPrefixLaw_short_length_mass bounds the mixture mass of prefix
   lengths <Y by H_Y/H_(N+1).
   root_harmonic_ratio_eventually_le gives, for Y=rootRoughCutoff k (N+1),
     H_Y/H_(N+1) <= 1/log(N+1)+2/(k+1).
   quantFactorSign_harmonic_range_power_bound: for sufficiently fine Q,
     harmonicRangeMean of |factorSign-quantFactorSign Q (N+1)|
       <= eta+4/(k+1)+2/log(N+1), eventually.
   The early prefixes are charged their full harmonic mass, not discarded.
   quantFactorSign_harmonic_approximation: for every epsilon>0 there is Q0>0
   such that eventually, uniformly for Q>=Q0,
     harmonicMean (N+1) |factorSign-quantFactorSign Q (N+1)| <= epsilon.
   This is NOT inferred merely from a natural-mean error at the endpoint.

8. ActualHarmonicPrimeTransfer.lean
   actual_harmonic_prime_comparison_transfer: for every H0>=8 and epsilon>0
   there are Q,K>0 such that eventually some n<K satisfies
     |harmonicMean_(N+1) factorSign
       - average_{p in halfBlockPrimes(factorialScale H0 n)}
           harmonicMean_(N+1) orderSkew(L_N(m),L_N(m+p))| < epsilon,
   where L_N = primeQuantLabel Q (N+1).
   Unlike the natural transfer, the adjacent mean has the SAME FULL
   endpoint N+1 for every p.

REMAINING BLOCKERS:
- No signed prime-ergodic cancellation estimate for the retained skew
  correlation has been proved. Fixed-modulus Dirichlet-Abel cancellation
  cannot be substituted for this endpoint-dependent process.
- No logarithmic density-half theorem has yet been proved.
- Even a logarithmic density result would not prove the requested natural
  density without additional arithmetic input.
- The earlier middlePrimeComplementAt criterion for the ORIGINAL natural
  density remains unestimated. The harmonic work does not supersede it.

The attempted external reference fetch returned no content; no new external
mathematical result was obtained or used. CheckHarmonic.lean was removed.


FIXED LOCAL PRIME LABELS AND HARMONIC TRANSFER
---------------------------------------------------------------------
Spec.lean remains unchanged. The original conjecture is UNRESOLVED.
No proof or disproof has been submitted.

This continuation replaces moving global labels by a FIXED finite sequence
for the harmonic transfer. It proves the required approximation and
multiplier stability; neither is assumed. All main theorem axiom checks
show only propext, Classical.choice, Quot.sound. Saved .olean files exist.

1. LocalPrimeQuantization.lean
   localPrimeRatio n = log(P(n))/log n, with totalized values at 0 and 1.
   localPrimeLabel Q n = unitQuantize Q (localPrimeRatio n).
   localPrimeRatio_mem_unit holds for all n.
   unitQuantize_boundary_of_ne: different quantizations of x,y in [0,1]
   imply some j in [1,Q] with |x-j/Q| <= |x-y|.
   localPrimeRatio_mul_bound: for k>0 and n>1,
     |localPrimeRatio(k*n)-localPrimeRatio(n)| <= log k/log n.
   Hence that difference tends to zero for each fixed positive multiplier.

2. PrimeLogBoundaryRarity.lean
   normalizedPrimeLog_self_band converts a local logarithmic band into the
   previously checked logPrimeBandEvent.
   prime_log_level_nonatomic: for every a>0 and epsilon>0 there is delta>0
   such that eventually the natural proportion of n>1 satisfying
     |log(P(n))/log n-a| <= delta
   is at most epsilon. Uses the explicit prime-band upper bound with
   u=a-a*r, v=a+a*r, t=1-r and r=min(1/4,epsilon/512).

3. LocalPrimeLabelStability.lean
   localPrimeLabel_perturbation_mean_zero: perturbing localPrimeRatio by a
   unit-valued sequence whose difference tends pointwise to zero changes
   each fixed finite quantization on a density-zero set. All finitely many
   positive quantizer thresholds are covered using their own widths.
   localPrimeLabel_mul_mean_zero: for each fixed Q and k>0,
     prefixMean_N 1_{L_Q(k*n) != L_Q(n)} ->0.
   This is an AVERAGED statement, not pointwise exact multiplier invariance.

4. HarmonicAbelian.lean
   harmonicMean_zero_of_prefixMean_zero: for bounded |F|<=1, natural mean
   cancellation implies harmonic mean cancellation. Uses the positive
   prefix mixture and explicitly charges the finitely many short prefixes.
   No reverse implication is asserted.

5. LocalPrimeLabelMeanPerturbation.lean
   localPrimeLabel_mean_perturbation_zero allows endpoint-dependent y(N,n)
   and assumes only that prefixMean_N |y(N,n)-localPrimeRatio(n)| ->0.
   Quantizer-boundary neighborhoods are controlled arithmetically; the
   remaining changes are bounded by the L1 error times sum_j 1/delta_j.
   Unit bounds are needed only for n<N, not for all inputs in a moving row.

6. LocalGlobalPrimeRatio.lean
   local_global_prime_ratio_mean_bound: for fixed k>0 and N>=2k,
     prefixMean_N |normalizedPrimeLog N n-localPrimeRatio n|
       <= 1/k+log(2k)/log N.
   The prefix n<N/k is paid for; the rest uses N<=2k*n.
   local_global_prime_ratio_mean_zero follows. No independence is used.

7. FixedComparisonApproximation.lean
   prefixMean_succ_error is the exact O(1/N) shift bound, and
   prefixMean_succ_zero also allows endpoint-dependent bounded rows.
   harmonicMean_eventual_upper_of_prefix_upper transfers an eventual
   natural upper bound for a fixed bounded sequence, with arbitrary extra
   harmonic tolerance.
   local_global_prime_label_mean_zero: for each FIXED Q, global and local
   prime labels disagree on a set of vanishing NATURAL mean. This is NOT
   a corresponding harmonic claim for the moving global labels.
   localFactorSign Q n compares localPrimeLabel Q n and Q (n+1).
   local_global_factorSign_mean_error_zero compares this with the previous
   moving quantFactorSign Q N in natural L1 mean.
   localFactorSign_natural_approximation and
   localFactorSign_harmonic_approximation: for every epsilon>0, all
   sufficiently fine FIXED Q approximate the actual factorSign with eventual
   mean absolute error <=epsilon. The endpoint threshold may depend on Q.

8. ApproximateHarmonicPrimeTransfer.lean
   labelDilationDefect p L n = 1_{L(p*n) != L(n)}.
   harmonic_approximate_dilation_error gives the explicit observable-uniform
   bound
     p/H_D +2*harmonicMean_D defect(n)+2*harmonicMean_D defect(n+1)
   between the conditioned gap-p discrepancy and the full adjacent-minus-
   gap-p harmonic mean, D=N+1. BOTH label defects are retained.
   harmonicDilationBudget_zero follows from natural density-zero defects
   and the bounded shift/Abelian lemmas.
   approximate_harmonic_prime_transfer selects a horizon depending only on
   alphabet, tolerance, and H0. It then applies to ANY fixed label sequence
   with natural density-zero defects for every positive fixed multiplier.

9. FixedHarmonicPrimeTransfer.lean
   localPrimeLabel_harmonic_prime_transfer specializes the preceding theorem
   to the actual fixed local prime labels.
   actual_fixed_harmonic_prime_comparison_transfer: for H0>=8, epsilon>0,
   there are Q,K>0 such that eventually some n<K has
     |harmonicMean_D factorSign
       - average_{p in halfBlockPrimes(factorialScale H0 n)}
           harmonicMean_D orderSkew(L_Q(m),L_Q(m+p))| < epsilon,
   where D=N+1 and L_Q(m)=localPrimeLabel Q m is INDEPENDENT OF N.
   This is unconditional TRANSFER, not cancellation of the right-hand mean.

BLOCKERS STILL PRESENT:
- The prime-gap skew correlation of the fixed process remains unestimated.
  Being fixed permits a stationary-limit strategy, but does not by itself
  establish reversibility or prime-ergodic cancellation.
- Existing fixed-cycle Dirichlet-Abel prime cancellation is not a substitute
  for a stationary-process prime ergodic theorem. A narrow Mathlib search
  still finds no ready Vinogradov or prime ergodic theorem, and PrimesInAP
  provides the analytic precursor for Wiener-Ikehara rather than PNT-AP.
- No logarithmic density-half theorem has been obtained yet.
- Even a logarithmic theorem would leave the ORIGINAL natural-density
  problem without further arithmetic input. The middle-prime complement
  criterion and natural prime-gap endpoint issue remain unresolved.

Lean detail: labelDilationDefect uses Classical.propDecidable internally,
while the local Fin-valued label indicator has the concrete Fin decidability
instance. A direct exact/simpa did not identify them; the specialization
uses function extensionality and split_ifs.

NATURAL SIGNED-KERNEL REVIEW AFTER THE FIXED-LABEL TRANSFER
---------------------------------------------------------------------
Spec.lean remains unchanged; no settlement or submission.

Reviewed the prime-winner flow/energy route, cofactor descent, and the
upper-half signed prime kernel rather than extending the harmonic reductions.
No new unconditional signed cancellation theorem was obtained.

The prime-winner flow identity and its nonnegative energy reformulation do
not give an upper bound on the signed cross terms. Local-minimum deletion
is already known not to be a pointwise energy contraction. The previously
considered finite bound E(N)<=N remains unproved; finite numerical checks
are not a substitute for that signed inequality.

Above sqrt(N), the cofactor of a largest prime p is smaller than p, so the
cofactor's smoothness condition is automatic. The remaining comparison is
still the opposite-residue prime-pair discrepancy already isolated in
UpperHalfSmoothSkew and VaughanPrimeKernel. This is not a new cancellation.

A direct character-orthogonality approach to a rectangular subkernel with
cofactor length A and prime length X, modulo p, gives a scale of roughly
sqrt(A*(1+X/p)*pi(X)), before any additional arithmetic cancellation.
For A*X~N and X>=p, this does not reach o(N/p) on a fixed interior
positive-power band p>N^(1/2+delta). Thus it cannot be summed over those
prime moduli to close the gap. No prime-weighted inverse-rectangle estimate
was silently substituted for an unweighted one.

The two short-divisor Vaughan terms still vanish by the checked opposite-
progression estimates. The long-divisor/Type-II term still has ordinary
composite support and remains unestimated. Neither the main middle-prime
complement criterion nor the natural endpoint problem has been resolved.

BOUNDED WIENER--IKEHARA AND FIXED-MODULUS NATURAL PRIME AVERAGES: COMPLETED
------------------------------------------------------------------------
Spec.lean remains unchanged. No proof/disproof of Erdos 371 is ready, and
no submission was made. Target SHA256 still:
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff

This pass implemented the Fourier Tauberian plan from the previous context.
Thirteen new modules (1433 lines total) are checked, admission-free, and have
saved .olean files. The final main-theorem axiom checks report only propext,
Classical.choice, Quot.sound.

1. FourierBoundaryConvolution.lean
   Namespace Erdos371.FourierBoundary.
   boundary_pairing and boundary_convolution_decay:
   bounded integrable approximants f_n converge pointwise to f; their Fourier
   transforms converge pointwise to G and are uniformly bounded on support
   of an integrable test psi whose Fourier transform is also integrable.
   Then
     integral f(t)*F(psi)(t-x) = F^{-1}(G*psi)(x) -> 0.
   Fubini/Fourier duality plus two dominated-convergence arguments are used.
   Actual integrability of BOTH limiting pairings is proved and included
   in the decay theorem; no totalized divergent integral is used.

2. LaplaceBoundaryConvolution.lean
   damped f sigma t = exp(-sigma*t)*f(t), complex-valued.
   Bounded measurable f supported on t>=0 has integrable damped functions
   for every sigma>0, uniformly bounded by the bound for f, and converging
   pointwise to f as sigma_n=1/(n+1)->0.
   closed_strip_convolution_decay:
   a continuous extension F(sigma,xi) to [0,1] x R that agrees with Fourier
   of the damped function for sigma>0 gives band-limited convolution decay.
   Compactness supplies the frequency-side dominating bound.

3. PositiveBandlimitedKernel.lean
   Constructs a smooth even real compactly supported frequency bump phi.
   Its self-convolution psi has Fourier transform |F(phi)|^2, a nonnegative
   nonzero integrable Schwartz kernel. Its integral is proved positive.
   positiveKernel normalizes this kernel to mass 1.
   positiveKernel_scaled_bandlimited: for every R>0, R*K(R*t) is the Fourier
   transform of an integrable compactly supported frequency function.
   The Fourier scaling identity is proved by real change of variables.

4. BandlimitedApproximateIdentity.lean
   The kernel has finite first absolute moment, by Schwartz decay.
   Scaling by R divides this moment by R.
   exists_positive_bandlimited_small_moment: for every eta>0 obtains a
   nonnegative integrable mass-one kernel with first moment <=eta, together
   with its integrable compactly supported frequency test and exact Fourier
   identity. This avoids any unproved positive-kernel approximation claim.

5. PositiveKernelTauberian.lean
   kernelMean K f x = integral K(u)*f(x+u).
   SlowlyDecreasing f means: for every eps>0, some d>0 and T satisfy
     f(x)-f(y)<=eps for T<=x<=y<=x+d.
   one_sided_kernel_bound charges the nonlocal region by
     (2*M/delta)*integral |u|*K(u),
   rather than dropping the kernel tail.
   tendsto_zero_of_small_moment_kernel_means:
   bounded measurable slowly decreasing f tends to zero if it has decaying
   means for positive mass-one kernels with arbitrarily small first moment.
   Future and past shifted centers give the two sides of the squeeze.

6. BoundedLaplaceTauberian.lean
   bounded_laplace_tauberian combines all the preceding steps:
   bounded real measurable half-line f, slowly decreasing, and a continuous
   closed-strip Fourier--Laplace extension imply f(t)->0.
   The transform identity and boundary continuity remain explicit hypotheses.

7. LogarithmicSummatory.lean
   summatory a x = sum_{1<=n<=floor x} a(n).
   expSummatory a t = exp(-t)*summatory a (exp t).
   For nonnegative a with sum_{1<=n<=N}a(n)<=C*N, proves measurability,
   nonnegativity, boundedness, vanishing for t<0, and slow decrease.
   centeredExpSummatory a A subtracts A*1_{t>=0} and has the corresponding
   boundedness/slow-decrease hypotheses. No continuity of the step function
   is assumed. One harmless unused-parameter warning in summatory_bigO.

8. SummatoryLaplaceIdentity.lean
   laplacePoint sigma xi = sigma + 2*pi*i*xi.
   Proves the exact Fourier--Laplace half-line formula, the exp change of
   variables, and
     LSeries(a)(1+z) = (1+z)*Fourier(damped expSummatory)(xi),
   using Mathlib's LSeries_eq_mul_integral_of_nonneg.
   Also proves the half-line unit transform 1/z.

9. BoundedIkehara.lean
   bounded_ikehara and bounded_ikehara_nat:
   for a_n>=0 with a linear summatory bound, if G is continuous on Re(s)>=1
   and agrees with LSeries(a)(s)-A/(s-1) on Re(s)>1, then
     sum_{1<=n<=N}a_n / N -> A.
   The regular Fourier boundary is G(1+z)/(1+z)-A/(1+z).
   All transform identities, nonzero denominators, and continuity are proved.
   This is a COMPLETE bounded Wiener--Ikehara theorem, not a placeholder.

10. NaturalResiduePrimeDensity.lean
    Namespace Erdos371.AbelPrimes (retained for compatibility, despite the
    new theorems being ordinary natural averages).
    residue_natural_mangoldt_limit applies bounded_ikehara_nat to Mathlib's
    residueClass, its continuous auxiliary L-function, and Chebyshev's bound.
    The result is sum_{n<=N,n=a mod q}Lambda(n)/N -> 1/phi(q) for unit a.
    nonnegative_mean_zero_of_summable_div is a general dominated-tsum lemma:
      c>=0 and sum c(n)/n<infinity imply sum_{1<=n<=N}c(n)/N ->0.
    It removes the higher prime powers using Mathlib's existing summability.
    prime_residue_natural_limit gives the log-weighted PRIME sum / N ->
      if IsUnit a then 1/phi(q) else 0.

11. RemovePrimeLogWeight.lean
    remove_log_weight: for arbitrary b_n in [0,1], if
      sum_{n<=N}b_n*log(n)/N -> A,
    then sum_{n<=N}b_n*log(N)/N -> A.
    Uses a FIXED power cutoff N^t for each accuracy, followed by N->infinity.
    The error N^t*log(N)/N vanishes for t<1; no moving-t limit is interchanged.

12. PrimeNumberTheoremAP.lean
    residuePrimeCount a N counts primes <=N in the fixed class a mod q.
    prime_number_theorem_AP proves
      residuePrimeCount(a,N)*log(N)/N -> if unit a then 1/phi(q) else 0.
    prime_number_theorem_initial obtains the full PNT from q=1.
    initialPrimes N = (Icc 1 N).filter Nat.Prime = (N+1).primesBelow.

13. NaturalCyclicPrimeSkew.lean
    prime_periodic_natural_limit: for a FIXED periodic real function g mod q,
      average_{p<=N prime}g(p) -> sum_{unit a}g(a)/phi(q).
    prime_periodic_odd_natural_limit: odd g has zero ordinary prime average.
    halfBlock_periodic_odd_natural_limit specializes to the prime sets used
    by the entropy modules.
    fixed_cyclic_prime_skew_natural_limit: every FIXED cycle and real
    antisymmetric pair observable has zero ordinary prime-averaged skew.
    Unlike AbelCyclicPrimeSkew, this now concerns ordinary prime averages.
    It is NOT uniform in the cycle length or an endpoint-dependent process.

IMPORTANT DEFINITION CORRECTION FOR FUTURE DISCUSSION:
  BlockPrimes.halfBlockPrimes H = (H/2+1).primesBelow.
  It consists of primes <=H/2, NOT primes in the dyadic band (H/2,H].
  All Lean statements have used the actual definition. Avoid calling this
  family a dyadic prime band in mathematical discussions.

REMAINING GAPS (UNCHANGED AT THE CONJECTURE LEVEL):
- Fixed-modulus NATURAL prime averages are now available; do not repeat the
  old claim that only Dirichlet--Abel averages have been proved.
- General stationary-process prime skew still needs irrational-frequency
  prime exponential-sum cancellation (or some replacement). Fixed-period
  PNT-AP cannot be substituted uniformly for growing cycles.
- A stationary-limit construction compatible with the fixed harmonic labels
  has not yet been implemented.
- No logarithmic density-half result for the actual factorSign is proved.
- Even such a harmonic/logarithmic result would NOT imply the conjectured
  natural density. The natural endpoint N/p issue and the unestimated signed
  middle-prime complement criterion remain unresolved.
- No new estimate for the retained long Vaughan/Type-II kernel was obtained.

Lean details from this pass:
- Use `open scoped Topology ContDiff SchwartzMap` for smoothness and Schwartz
  notation. The notation needs a space: `SchwartzMap R C` or `S(R, C)`.
- `Measure.integral_comp_mul_left` and `Measure.integral_comp_div` are under
  MeasureTheory.Measure, not directly MeasureTheory.
- Pointwise function operations under integrals need Pi.sub_apply,
  Pi.add_apply, or Pi.div_apply before rewriting.
- A definition with several explicit arguments may not unfold on partial
  application under Integrable. An explicit `change Integrable (fun t => ...)`
  fixes this for modulate.
- Put a space after an absolute-value closing bar before multiplication;
  otherwise `|*` can tokenize as unrelated notation.
- The unweighted counting indicator lambda needs `(n : Nat)` explicitly;
  otherwise `(n : ZMod q)` can make Lean infer the wrong binder type.
- `one_lt_one_div ht` takes a second hypothesis as an argument, not `.mpr`.
- `isLittleO_log_rpow_atTop` is at the root namespace, not Real.
- Temporary CheckBoundary.lean was removed.

Resources after this pass: 52h07m used, 43h53m remaining; $615.24 used,
$384.76 remaining. No final proof has been submitted.

# UNIFORM ONE-LINEAR PRIME SIEVE: COMPLETED

Spec.lean is unchanged and unresolved. Two new compiled modules:

- OneLinearSelberg.lean: performs Selberg sieving on the progression INDEX,
  not its values. For a>0 and z>=1, the number of prime values a*n+b>z for
  n<M is at most 2*exp(1)*(a/phi(a))*M/log(z+1)+2*(z+1)^32. The error is
  independent of both slope and intercept. Restoring small primes costs z.
  The factor exp(sum_{p|a}1/p)<=a/phi(a) follows from the totient product.
- UniformLinearPrimeSieve.lean: optimizes z=floor((N+1)^(1/64)), obtaining
  linear_prime_count_uniform: all prime values a*n+b, n<N, are at most
  C*(a/phi(a))*N/log(N+1), C=128*exp(1)+2^35+4. Uniform in a,b. Only the
  three permitted axioms occur.

PROPOSED, NOT PROVED: a prime-Bohr upper bound using Dirichlet approximation,
short reduced-residue interval counts, and the new uniform progression sieve.
This would not itself prove prime equidistribution, nor natural density half.

A shorter possible harmonic route was identified on resumption (UNPROVED):
for a harmonic-limit spectral measure sigma of a dilation-stable observable,
positivity on the residue class 0 mod p should give sigma <= p*(x->p*x)_*sigma.
For an irrational atom alpha, the preimages {x:p*x=alpha} for distinct p are
pairwise disjoint. Each has mass >=sigma({alpha})/p, contradicting divergence
of the prime reciprocal sum. Thus irrational atoms would be excluded without
Vinogradov estimates. Continuous-spectrum prime averaging could then follow
from a prime-pair upper sieve, a bounded second moment for its singular series,
and Wiener's lemma. Rational atoms use the completed PNT-AP.
NONE of the measure construction, domination, or spectral application has yet
been proved. This route remains HARMONIC ONLY: natural averages at N/p cannot
be replaced by N, and natural density would still need a separate argument.

# HARMONIC DILATION AND STATIONARY LIMITS: NEW VERIFIED STEPS

The prime-Bohr detour is not needed for the abstract irrational-atom step.
DilationSpectralAtoms.lean proves (only permitted axioms):
- Fibers {y:n*y=x} for different n are disjoint if x has infinite additive
  order, in any additive commutative group.
- A finite measure with mu({x}) <= n*mu({y:n*y=x}) for all n>0 has zero mass
  at every infinite-order x. The fiber masses are summable, so a positive
  atom would make the ordinary harmonic series summable.
- Consequently mu <= n*(nsmul n)_*mu for all n>0 excludes infinite-order atoms.
- Specialization to AddCircle(1): all irrational singletons have mass zero.
This is an abstract measure theorem; a spectral measure of the actual labels
has NOT yet been constructed or connected to it.

HarmonicWindowDilation.lean (compiled, permitted axioms):
- Fixed shifts preserve natural mean-zero bounded sequences.
- Unit-bounded finite-window observables change by at most twice the sum
  of their coordinate defects.
- Exact conditioned harmonic dilation for ANY fixed window, with budget
  p/H_(N+1) + 2 sum_{k<K} harmonicMean(defect_p(n+k)).
- This budget tends to zero under the existing natural mean label stability.
- Nonnegative window means satisfy dilation domination in EVERY simultaneous
  harmonic subsequential limit, with the SAME endpoint subsequence.

HarmonicEmpiricalMeasure.lean (compiled, permitted axioms):
- Fixed-shift harmonic mean error <=2/H_(N+1), and convergence to zero for
  any bounded sequence.
- Genuine harmonic empirical probability measures, an exact integral formula,
  and common subsequence compactness on compact metrizable spaces.

HarmonicWordLimit.lean (compiled, permitted axioms):
- Constructs, for any FIXED finite label sequence satisfying mean dilation
  stability, one harmonic empirical subsequential probability measure on
  the one-sided word space A^N.
- Proves shift stationarity as actual MeasurePreserving, not just a finite
  list of moments.
- ALL fixed-window nonnegative dilation inequalities hold in the SAME measure.
- This resolves the previously missing stationary-limit construction, but
  has not yet proved the Fourier/spectral representation needed for atom
  exclusion, nor continuous-spectrum prime cancellation.

THE CONJECTURE IS STILL UNRESOLVED. Even completion of this harmonic route
would not by itself give natural density. Spec.lean is unchanged.

Two additional compiled spectral foundations (permitted axioms only):
- ToeplitzFourierDensity.lean: nonnegative finite Fourier densities for a
  positive Hermitian Toeplitz sequence c:Z->C. Exact Fourier moments are
  ((H-|k|)_+/H)*c(k); total mass is Re(c(0)) for H>0.
- ToeplitzSpectralMeasure.lean: complete Herglotz representation
  exists_toeplitz_spectral_measure. Compactness of finite measures supplies
  a cluster point, and continuity of every Fourier moment gives
  integral fourier(k) dmu = c(k). No spectral theorem is assumed.
The remaining connection is to stationary word covariances, followed by
finite-window dilation inequalities for Fourier polynomial squared norms.

# ACTUAL FIXED-LABEL HARMONIC IRRATIONAL-ATOM EXCLUSION: COMPLETED

Four more compiled modules, main theorems using only permitted axioms:

- StationaryWordCovariance.lean: constructs integer covariance c(k) for any
  complex coordinate observable of a stationary finite-alphabet word law.
  Proves Hermitian symmetry, c(i-j)=integral f(x_i)*conj(f(x_j)), and Toeplitz
  positivity. Applies the completed Herglotz theorem to produce a genuine
  finite positive spectral measure representing all integer covariances.
- SpectralWordEnergy.lean: arbitrary finite Fourier-polynomial energies equal
  the corresponding word energies at the prescribed nonnegative times.
  Removes unit bounds on nonnegative finite cylinder tests by a fixed finite
  normalization. Transfers cylinder dilation domination to analytic Fourier
  polynomial squared-norm domination.
- FourierAtomTests.lean: bounded normalized geometric Fourier sums have
  squared norms converging to the indicator of a point. DCT extracts point
  masses and fiber masses after any fixed continuous map. Consequently the
  analytic polynomial energy inequality gives EXACT atom-fiber domination.
  No Fejer-Riesz factorization or unproved density argument is used.
- HarmonicPrimeLabelSpectrum.lean: combines these with DilationSpectralAtoms.
  exists_word_spectral_measure_no_infinite_order_atoms and its irrational
  real-circle specialization are proved. Most importantly,
  exists_localPrimeLabel_harmonic_spectral_limit applies to the ACTUAL fixed
  localPrimeLabel Q sequence: for any diverging endpoint sequence, one common
  subsequential word probability law is stationary and every complex
  coordinate observable has a spectral measure with no irrational atoms.
  The word law and endpoint subsequence are chosen BEFORE the observable.

Thus the previously planned prime-Bohr argument is genuinely unnecessary for
this harmonic step, and both stationary construction and irrational-atom
exclusion are now checked for the actual labels.

Still unproved: prime averaging of the continuous spectral part, the resulting
harmonic density-half theorem, and (separately) the requested natural density.
The original natural signed middle-prime criterion remains unestimated.

PrimeDifferenceSieve.lean and UniformPrimeDifferenceSieve.lean now compile:
- Generalizes the two-linear Selberg estimate to prescribed two-root local
  data, then specializes to prime pairs n,n+k for arbitrary k>0.
- Uniform all-prime-pair bound:
    #{n<N:prime n and prime(n+k)}
      <= C*S(2k)*N/log(N+1)^2,
  with C=32768*exp(2)+2^70+64 and S=slopeSieveFactor.
- No k-dependent polynomial error remains after the cutoff optimization.
- The singular factor has the uniform second moment
    sum_{k<N} S(2(k+1))^2 <= N*exp(18).
Both main theorems use only the permitted axioms. This supplies the arithmetic
input proposed for continuous-spectrum prime averaging. Wiener's lemma and
its application remain to be proved.

WienerAtomless.lean now compiles (permitted axioms):
- measureFourier(mu,k) = integral fourier(k) dmu.
- Fourier coefficient squared norms equal integrals of Fourier characters
  of x-y against mu x mu.
- For atomless finite mu the diagonal has product measure zero.
- Bounded geometric means tend to zero off the diagonal; DCT yields
  atomless_fourier_mean_square_zero:
    sum_{k<N} |measureFourier(mu,k)|^2 / N -> 0.
Next: combine this with UniformPrimeDifferenceSieve to prove that ordinary
prime Fourier averages have vanishing L2(mu) norm on the atomless part.

Three further compiled modules (permitted axioms):
- FinitePrimeDifferenceEnergy.lean: exact even-kernel diagonal/positive-gap
  decomposition; exact positive-difference reindexing; prime partner counts
  bounded by the uniform prime-difference sieve. No diagonal is discarded.
- SingularWeightedWiener.lean: bounded Fourier coefficients, shifted Wiener
  mean square, and singularFourierMean(mu,N)->0 for every atomless finite mu.
  Cauchy--Schwarz absorbs S(2k) using its proved second moment.
- AtomlessPrimeFourierAverage.lean: primeFourierAverage(N,x) is the normalized
  sum of fourier(p)(x) over all primes p<=N. Proves
    atomless_primeFourierAverage_L2_zero:
      integral |primeFourierAverage(N,x)|^2 dmu ->0
  for every FIXED atomless finite circle measure mu. Uses the new pair sieve,
  Wiener, and PNT for a coarse eventual normalization bound. The diagonal
  contributes |hat(mu)(0)|/pi(N), and is proved negligible.
This completes the proposed continuous-spectrum prime-averaging step.
Still needed: rational-atom contribution (PNT-AP), assemble prime skew for the
actual harmonic limit, and combine with common-scale entropy transfer.
The original natural-density problem remains a separate unresolved step.

# HARMONIC DENSITY ONE HALF FOR THE ACTUAL LARGEST-PRIME COMPARISON: COMPLETED

The following four compiled modules finish the weaker harmonic theorem.
All main results use only propext, Classical.choice, and Quot.sound.

- PrimeFourierSkewSpectrum.lean: Im primeFourierAverage(N,x)->0 at every
  finite-order circle point by PNT-AP and a ZMod lift of its cyclic orbit.
  A generic L2-to-integrated-imaginary estimate handles the atomless part.
  The torsion subset of the circle is countable and measurable; restricting
  a measure with no infinite-order atoms to its complement is atomless.
  DCT on the torsion part plus the atomless prime L2 theorem proves
  primeFourier_im_integral_zero_of_no_infinite_order_atoms.

- StationaryPrimeSkew.lean: uses pairPhase(a,b,x), with real part 1_{x=a}
  and imaginary part 1_{x=b}, to express any antisymmetric finite observable
  as a finite linear combination of imaginary covariances. Proves
  stationary_prime_skew_zero for every fixed stationary word law satisfying
  all finite-window dilation domination inequalities.

- HarmonicStableSkewZero.lean: selects a common stationary subsequential word
  law FIRST. Its prime-skew cancellation then picks a sufficiently large
  initial scale H0. The existing common-scale entropy transfer supplies a
  finite horizon K. All finitely many prime-gap means converge in the SAME
  law, so the selected scale among those K has small skew. This proves
  harmonic_word_limit_adjacent_skew_zero. Subsequence compactness then gives
  stable_finite_labels_harmonic_skew_zero for any FIXED finite label sequence
  whose fixed-multiplier defects vanish in natural mean.

- HarmonicLargestPrimeHalf.lean:
    localFactorSign_harmonic_mean_zero Q
    factorSign_harmonic_mean_zero
    largest_prime_rises_harmonic_half
  The last theorem states exactly
    Tendsto (fun N => harmonicMean (N+1)
      (fun n => if P(n+1)>P(n) then (1:Real) else 0)) atTop (nhds (1/2)).
  Approximation uses one fixed Q for each tolerance, before taking N->infty.

THIS DOES NOT SETTLE SPEC.LEAN. No harmonic-to-natural Tauberian reversal has
been asserted. The target file remains unchanged with its original sorry.
The original natural signed middle-prime criterion remains unestimated.

Checkpoint after the harmonic theorem:
- 20 new spectral/harmonic modules in this pass, 2141 lines, compiled.
- Re-ran Lean on HarmonicLargestPrimeHalf.lean. Its two main theorems report
  exactly [propext, Classical.choice, Quot.sound].
- Removed temporary CheckSpectral.lean (and earlier CheckSieve.lean).
- Spec.lean SHA256 remains
  34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
- Reviewed the natural middle-prime criterion and ordinary exponential
  criterion again. No new natural signed estimate or Tauberian hypothesis
  was established. The harmonic proof removes N/p using the fixed-p error
  p/H_N; the corresponding natural endpoint loss is not negligible.
- Do not repeat the obsolete statement that harmonic density-half,
  stationary limits, irrational-atom exclusion, or continuous-spectrum prime
  averaging are missing: all four are now checked. Natural density remains
  unresolved, and no proof/disproof has been submitted.
Resources near this checkpoint: 53h31m used, 42h29m remaining;
$636.17 used, $363.83 remaining (some additional checking followed).

## Natural density value is now unique, conditional on existence

Submission/NaturalDensityUniqueness.lean compiles, with its saved .olean.
Both printed main axiom checks use only propext, Classical.choice, Quot.sound.

- harmonicMean_const: exact mean of a constant at every positive endpoint.
- harmonicMean_limit_of_prefixMean_limit: a [0,1]-valued sequence with
  natural mean d has harmonic mean d, by centering and the proved Abelian
  zero-limit theorem. This is the forward implication only.
- largest_prime_rises_density_value: if the actual rise set HasDensity d,
  then d=1/2, using the completed harmonic theorem and uniqueness of limits.
- largest_prime_rises_half_iff_density_exists: the original conjecture is
  equivalent to existence of any natural density for the actual rise set.

EXISTENCE REMAINS UNPROVED. The equivalence and the conditional uniqueness
result are not a settlement and were not inserted in Spec.lean as one.

Additional review: low-product prime-factor moments and fixed marginal data
still leave the signed long-product contribution uncontrolled. The existing
finite partition models already block the abstract moment-recovery shortcut.
Natural entropy transfer still has different endpoints N/p and N; no valid
estimate removing that difference was obtained. No reverse harmonic-to-natural
Tauberian statement has been asserted. Removed CheckNaturalUniqueness.lean.
Spec.lean retains its unchanged statement, import, and original sorry.

## Half is an actual natural-density cluster value: checked

Submission/NaturalDensityCluster.lean now compiles; its .olean is saved.
All three printed main axioms are exactly propext, Classical.choice, Quot.sound.

Generic bounded-sequence lemmas in FiniteInformation:
- eventual_prefixMean_lower_le_harmonic_limit and the upper counterpart:
  eventual one-sided bounds on prefix means pass to a harmonic limit.
  The proof retains the small-prefix mixture mass and the range/harmonic
  endpoint error, both tending to zero.
- exists_late_prefixMean_near_harmonic_limit: at arbitrarily late endpoints,
  the ordinary prefix mean approaches the harmonic limit. Successive prefix
  means differ by at most 2/(N+1), so they cannot jump over an avoided open
  interval around the harmonic limit. Eventual confinement to either side
  contradicts the preceding one-sided bound.
- exists_diverging_prefixMean_limit constructs endpoints D(k)>=k with the
  corresponding ordinary prefix means converging to the harmonic limit.

For the actual largest-prime rise set:
- largest_prime_rises_arbitrarily_late_near_half:
    for every epsilon>0 and M, some N>=M satisfies
    abs(risingCount(N)/N-1/2)<epsilon.
- largest_prime_rises_diverging_endpoints_half:
    exists D tending to infinity with risingCount(D(k))/D(k)->1/2.
  D need not be strictly increasing; divergence is proved explicitly.
- largest_prime_rises_lower_upper_density:
    lowerDensity <= 1/2 <= upperDensity.
- rising_partialDensity identifies the library partial density with the
  existing finite risingCount/N formula.

These are NATURAL cluster/bounding conclusions, not full natural convergence.
They do not eliminate other subsequential limits or settle Spec.lean.

Further attempted arithmetic review in this pass found no new signed estimate:
- The long Vaughan kernel remains, after the already checked short-term
  cancellation. Nonnegative sieve bounds do not compare its two orientations.
- The low-prime complement selection still leaves the colour-invariant
  high-prime component. Having a middle prime in the complementary divisor
  does not force its side colour to be observable in the selected low block.
- Damping still lacks an open interval of natural cancellation. Its uniform
  real-parameter bound does not license analytic continuation from a single
  vanishing coefficient.
- A request to erdosproblems.com/371 again failed DNS resolution.

Removed CheckCluster.lean. Spec.lean is unchanged with its original sorry;
no complete proof/disproof has been submitted.

## Further structural cancellation review (no new estimate)

Re-examined PrimeWinnerEnergyIncrement, PrimeWinnerNonadjacent,
PrimeWinnerFlux, PrimeLoserCollisionEnergy, and the opposite-prime-progression
kernel. No arithmetic estimate closing the natural-density gap was obtained.

- The exact E=N-2*A+2*R identity requires control of the nonadjacent SIGNED
  remainder R. Adjacent matching winners cancel automatically, but this does
  not give R<=A or any sufficient near-linear energy estimate.
- Max-under-multiplication alone cannot give E<=N: the checked reordered-prime
  example already has one group's squared imbalance exceeding N. Its lack
  of the natural prime ordering is essential; it is not a disproof of 371.
- Divisibility spacing and the conservation of label flow leave directed
  cycles. Neither property yields an injective pairing of same-sign and
  opposite-sign collision sets. No such injection was asserted.
- Upper sieve bounds do not compare prime counts in the two opposite
  progressions. Fixed-modulus PNT-AP remains insufficient for the moduli
  growing through the surviving positive-power ranges.
- The elementary Kloosterman fourth moment does not, without an additional
  weighted estimate, control the retained prime/Mobius-weighted kernel.

No new Lean theorem was added in this review. The latest complete result is
NaturalDensityCluster.lean, including the actual diverging-endpoint limit
one half and lower/upper natural-density bounds. Full convergence remains
unproved. Spec.lean is unchanged with its original sorry; no submission.

## Uniform harmonic prime-winner cancellation: checked

Three new development modules compile with only the permitted axioms:
propext, Classical.choice, Quot.sound.

1. HarmonicPrimeWinnerColours.lean
   - maxPrimeFac_mean_dilation_defect_zero converts the checked natural
     density-zero disagreement set to the prefixMean formulation.
   - primeColouredLabel_mean_dilation_defect_zero proves stability of the
     product labels (localPrimeLabel Q n, g (maxPrimeFac n)) for every fixed
     arbitrary Boolean colouring g of the primes (in fact of all naturals).
   - colouredOrderSkew is the antisymmetric finite observable that weights
     the comparison by the colour of its larger endpoint label.
   - colouredOrderSkew_approximation bounds its error against the actual
     winner-weighted sign by the already controlled quantization error.
   - primeWinner_coloured_harmonic_zero: for each fixed g : Nat -> Bool and
     each unit-bounded w : Bool -> Real, harmonicMean (N+1) of
       factorSign n * w (g (primeWinner n))
     tends to zero.

2. FiniteSupportSchur.lean
   - triangular_schur: a direct gliding-hump lemma for finite triangular
     real arrays. Coordinatewise zero limits plus convergence against every
     fixed +/-1 sign sequence force the row l1 norms to tend to zero.
   - triangular_schur_of_sign_tests derives the coordinate limits from the
     sign tests themselves, by comparing a constant test with a single
     coordinate sign flip.
   - The proof constructs increasing bad rows, chooses each row with small
     mass on earlier support, and patches their signs on disjoint blocks.
     The resulting ONE fixed sign sequence contradicts the weak hypothesis.

3. HarmonicPrimeWinnerNorm.lean
   - primeWinnerHarmonicCurrent N p is harmonicMean (N+1) of the signed
     indicator of primeWinner n=p.
   - primeWinner_harmonic_current_test is the exact finite-sum identity for
     any cutoff B>N+2 and any prime weight s.
   - primeWinner_sign_test_harmonic_zero supplies every fixed sign test.
   - primeWinner_harmonic_l1_zero:
       sum_{p<N+3} |primeWinnerHarmonicCurrent N p| -> 0.
   - primeWinner_bounded_weights_harmonic_zero: the harmonic cancellation
     is UNIFORM over arbitrary endpoint-dependent weights w(N,p) with
     |w(N,p)|<=1. Such weights themselves need not be dilation-stable.

IMPORTANT LIMITATION: these are NORMALIZED HARMONIC currents. The l1 norm
of the unnormalized harmonic current is proved only o(log N), not o(1),
Cauchy, or convergent. No reverse Tauberian step is licensed by this result.
Unnormalized l1 convergence, or a suitable uniform smallness estimate on
fixed-ratio endpoint intervals, could suffice but has NOT been proved.

The review of possible bridges found no new natural estimate:
- Finite prime-size quantization plus uniform prime colouring still has
  resolution fixed before N. Recovering n/N would require resolution on
  the order of 1/log N, which is not supplied by these convergence results.
- Arbitrarily sparse bad natural endpoints are compatible with normalized
  harmonic cancellation; the Schur argument does not eliminate them.
- The natural prime-winner energy and signed long-kernel hypotheses remain
  unproved. No implication from harmonic l1 cancellation to them is asserted.

Spec.lean remains unchanged, with its original sorry; the original natural
conjecture is not settled and no complete proof/disproof has been submitted.

## Fixed-prime unnormalized limits, flux, and a Tauberian bridge: checked

New compiled modules (all main axiom checks exactly propext,
Classical.choice, Quot.sound):

1. PrimeWinnerHarmonicLimits.lean
   - smoothReciprocal B n is 1/n on positive (B+1)-smooth integers, zero
     elsewhere. summable_smoothReciprocal follows from Mathlib's finite
     Euler product for reciprocalNatHom.
   - primeWinnerHarmonicTerm p n and primeLoserHarmonicTerm p n are the
     signed terms factorSign(n)/n restricted to the respective prime group.
   - rawPrimeWinnerHarmonic p N and rawPrimeLoserHarmonic p N sum these
     terms over range N. The n=0 term is zero, by real division at zero.
   - summable_primeWinnerHarmonicTerm_norm and the loser counterpart prove
     ABSOLUTE convergence in n for EACH FIXED p.
   - The winner bound is by the reciprocal series on p-smooth n. The loser
     bound uses that either n or n+1 has largest prime at most p and that
     1/n <= 2/(n+1) for n>=1.
   - rawPrimeWinnerHarmonic_tendsto and rawPrimeLoserHarmonic_tendsto give
     limits primeWinnerHarmonicLimit p and primeLoserHarmonicLimit p.
   - NO uniform summability in p is asserted.

2. PrimeWinnerHarmonicFlux.lean
   - primeWinnerLoser_sign_flux is the pointwise label-conservation identity.
   - reciprocal_discrete_derivative is a generic finite summation-by-parts
     formula, retaining the terminal term.
   - rawPrimeHarmonic_flux identifies winner minus loser current at M+2:
       I_p(M+2)/(M+1) - I_p(1)
         + sum_{n<M} I_p(n+2)*(1/(n+1)-1/(n+2)).
   - rawPrimeHarmonic_flux_nonneg and primeHarmonicLimit_flux_nonneg prove
     nonnegative divergence for p>=2, finitely and in the fixed-p limit.
   - This does NOT prove positivity of the currents themselves. Indeed,
     rawPrimeWinnerHarmonic_7_15 = -1/21, checked using exact rational
     computation in the Lean kernel and then casting to R. The only terms
     are +1/6,-1/7,-1/14. Consequently not_rawPrimeWinnerHarmonic_nonneg.
     This is a counterexample to an auxiliary positivity proposal, NOT to
     Erdős 371. No further numerical search of the conjecture was made.

3. RawHarmonicTauberian.lean
   - rawHarmonicSum a N = sum_{n<N} a(n)/n, WITHOUT normalization.
   - sum_from_rawHarmonicSum proves the exact inverse summation identity.
   - prefixMean_zero_of_rawHarmonicSum_tendsto is Kronecker's elementary
     lemma here: convergence of rawHarmonicSum a implies prefixMean a ->0.
     It uses Cesaro convergence of the convergent raw partial sums.
   - rawPrimeWinnerHarmonic_total is the exact finite prime-group sum.
   - rawPrimeHarmonicTail B N sums |rawPrimeWinnerHarmonic p N| over
     B<=p<N+B+1. Labels above the actual support contribute zero.
   - rawHarmonicSum_converges_of_prime_tail_tightness: the now proved
     coordinatewise convergence plus
       forall epsilon>0, exists B, eventually N,
         rawPrimeHarmonicTail B N <= epsilon
     gives convergence of the total UNNORMALIZED harmonic series.
   - density_of_rawPrimeHarmonic_tightness then proves the ORIGINAL
     natural-density conclusion, CONDITIONAL on this tail estimate.

THE TAIL HYPOTHESIS IS STILL UNPROVED. Normalized harmonic l1 convergence
only bounds the total unnormalized mass by o(log N); it does not supply
uniform small tails. Individual absolute convergence and nonnegative
winner-minus-loser divergence also do not supply that uniformity. Signed
circulation terms remain possible. No new arithmetic bound eliminating
them was obtained in this pass.

Removed temporary CheckHarmonicLimits.lean. Spec.lean remains unchanged,
including its original sorry. No full proof/disproof has been submitted.

## Summable moving top-band boundary: checked arithmetic advance

Three additional modules compile. All printed main axiom checks are exactly
propext, Classical.choice, Quot.sound.

1. DyadicBrunBoundary.lean
   - summable_of_nonneg_dyadic_blocks: dyadic blocking for a nonnegative
     sequence, with no monotonicity requirement.
   - dyadicTopPrimePair u n uses k=Nat.log 2 n and requires BOTH largest
     prime factors of n,n+1 to exceed (2^(k+1))^(1-u(k)).
   - dyadicTopPrimeReciprocal u n is 1/n on this event and zero otherwise.
   - dyadicTopPrimeReciprocal_block_bound applies the existing UNIFORM
     two-prime sieve to the block [2^k,2^(k+1)). Its upper bound is
       2*(largePairConstant*(u(k)+1/log(2^(k+1)))^2
          +2^65*(2^(k+1))^(-1/2)).
   - summable_dyadicTopPrimeReciprocal proves reciprocal summability when
     0<=u(k)<=1/8 and sum_k u(k)^2 converges.
   - threeQuarterBandWidth k=(1/8)*(k+1)^(-3/4) satisfies these hypotheses.
   - summable_threeQuarter_top_prime_pairs is the concrete result.
     Its exact threshold is as above. Algebraically its cofactor boundary
     has subexponential size exp((log 2)*(k+1)^(1/4)/8), up to dyadic factors.
     No separate Lean theorem translating it to this asymptotic wording was
     added; the checked theorem uses the exact dyadic threshold.

2. DyadicSeriesTools.lean
   - Exact dyadic partial-sum identity and the reverse nonnegative blocking
     implication (summability of f implies summability of its dyadic sums).
   - nat_log_two_tendsto.
   - partialSums_converge_of_dyadic_prefix_bound: a summable envelope for
     ALL partial sums within each dyadic block gives convergence of the
     ordinarily ordered series. This does not claim unordered/absolute
     summability of its signed terms.
   - reciprocal_derivative_Ico_bound: for 0<=a(n)<=1 and A>0,
       abs(sum_{A<=n<B} (a(n+1)-a(n))/n) <= 1/A.
     The proof retains the exact endpoint and reciprocal-difference terms.

3. DyadicHighWinnerHarmonic.lean
   - dyadicHighWinnerSign u n is factorSign n if the WINNER exceeds the
     exact dyadic threshold, and zero otherwise.
   - primeWinnerLoser_weight_flux is conservation for any real prime-label
     weight g, not just a singleton indicator.
   - dyadicHighWinner_harmonic_prefix_bound bounds every partial dyadic
     block of the signed winner contribution by the full block's nonnegative
     both-high reciprocal mass plus 2^(-k).
   - dyadicHighWinner_rawHarmonic_converges proves convergence of the
     UNNORMALIZED, ordinarily ordered harmonic series under the same
     square-summable-width assumptions as the Brun boundary theorem.
   - threeQuarterHighWinner_rawHarmonic_converges instantiates this with
     the concrete width above. This is an actual uniform arithmetic
     boundary convergence theorem, not a conditional tail-tightness claim.
   - threeQuarterHighWinner_natural_mean_zero follows by the checked
     Kronecker/summation-by-parts theorem.

LIMITATION: winning primes below this moving near-linear threshold still
contribute an unestimated interior series. The new estimates remove only
that top boundary. They do not prove full unnormalized prime-current tail
tightness, near-linear natural energy, or ordinary natural density 1/2.
No cancellation for the interior was obtained in this pass.

Removed CheckDyadicBrun.lean and CheckDyadicSeries.lean. Spec.lean remains
unchanged with its original sorry. No full proof/disproof has been submitted.

## Interior review after the summable boundary theorem (no new estimate)

Reviewed VaughanPrimeKernel, VaughanLongCoefficients,
CommonEndpointPrimeSkew, PrimeWinnerBulkUpper, and MiddlePrimeCriterion.
No additional Lean theorem or signed arithmetic estimate was obtained.

- The new dyadic high-winner theorem removes only its near-linear top band.
  It does not bound the long Vaughan kernel on its remaining composite
  support, nor the equivalent middle-prime complement.
- Absolute bounds for the long convolution lose the required Mobius
  cancellation. Small-divisor periodicity still only proves the existing
  short-term estimates; it does not cover the balanced long-divisor range.
- Character or additive-Fourier Cauchy--Schwarz estimates reviewed here
  retain a modulus-size loss. No valid estimate removing it for the actual
  growing prime moduli was established.
- Changing the entropy source endpoint with the prime scale still requires
  a new recurrence; the checked same-source harmonic recurrence cannot be
  reused for that purpose.
- The existing unconditional full-energy bound remains o(N^2), rather than
  the near-linear or prime-weighted estimate needed for natural density.

The latest checked arithmetic progress remains DyadicBrunBoundary,
DyadicSeriesTools, and DyadicHighWinnerHarmonic. Spec.lean is unchanged
with its original sorry; no complete proof/disproof has been submitted.

## Further interior/reflection review (no new theorem)

Revisited the prime-product reflection and its cofactor description while
looking for a natural-endpoint cancellation mechanism. The required basic
structure is ALREADY in PrimeReflection.lean: sign reversal, preservation
of the larger prime, monotonicity of the smaller prime/product, and eventual
two-periodicity. No new orbit theorem was needed or added.

This does not give a natural pairing: noninjectivity and a positive-density
escaping boundary are already checked in PrimeReflectionBoundary and
WeightedPrimeReflectionBoundary. Recasting the preimages using cofactors
retains opposite-residue prime/smooth conditions; no signed preimage estimate
or valid contraction was obtained.

Also reviewed the long Vaughan term and additive-score interpretation. No
new estimate for the balanced long-divisor range was found. Telescoping
weighted increments do not imply cancellation of their nonlinear signs;
no such implication was asserted.

No new Lean file was added in this review. The latest actual arithmetic
advance remains the summable moving top-band result. Spec.lean is unchanged
with its original sorry. The conjecture remains unresolved in this project.

## Fixed-sequence obstruction to a generic natural upgrade

NEW checked module: Submission/FixedStableBias.lean (265 lines).
All four printed main axiom checks are exactly propext, Classical.choice,
Quot.sound. No admissions or unsafe evaluation were used.

This strengthens the earlier ENDPOINT-DEPENDENT auxiliary countermodels to
ONE FIXED sequence, not a family that changes with the sample endpoint.

- exists_stripped_biased_chirp_eventually permits any prescribed eventual
  endpoint condition while retaining the earlier stripped-chirp bias.
- smoothIccCount_succ_ratio_zero bounds fixed-small-prime exceptional mass.
- biasBand recursively selects disjoint increasing prime bands. In band j,
  fixedBiasedPhase uses the j-th stripped chirp. The endpoint is selected so
  that integers using only earlier primes have sufficiently small proportion.
- fixedBiasedPhase_bias: at the diverging endpoints biasEndpoint(biasBand j),
  its natural imaginary adjacent correlation is at least 1/240.
- fixedBiasedPhase_small_multiplier: multiplication by fixed k changes no
  value outside the fixed smooth set P(n)<=biasBand k. Thus the natural
  mean dilation defect tends to zero for EVERY fixed positive k.
- exists_fixed_finite_stable_skew_bias quantizes this ONE sequence into a
  fixed finite alphabet, with a fixed antisymmetric observable and natural
  bias at least 1/480 on the selected endpoints.
- exists_fixed_three_label_harmonic_natural_gap uses the finite pair-order
  expansion to select ONE fixed three-label projection whose natural order
  skew does not tend to zero. The already checked generic harmonic theorem
  nevertheless gives harmonic skew convergence to zero for that sequence.

Consequently, a generic natural upgrade of stable_finite_labels_harmonic_
  skew_zero is FALSE even for a single fixed three-label sequence. This is
  not merely a failure of uniformity for endpoint-dependent families.

IMPORTANT: this sequence is NOT Nat.maxPrimeFac, and does NOT satisfy its
maximum-under-multiplication identity. This is NOT a disproof of Erdos 371.
It only rules out a proposed generic bridge. No new estimate for the actual
signed interior prime kernel or unnormalized harmonic tail was obtained.
Spec.lean remains unchanged with the original sorry. No proof/disproof of
the original conjecture has been submitted. Removed CheckFixedStable.lean.

Further review after that construction: the reordered-prime energy and
prefix counterexamples were already checked in PrimeWinnerEnergyObstruction
and FullRankingPrefixCheck; no duplicate numerical search was run. The fixed
finite-range max-multiplicative symmetry theorem is also already available,
but is nonuniform in its prime cutoffs. It does not apply to the diagonal
quantized cutoff X=N. The new fixed stable countermodel does not have the
max law, so it neither contradicts that theorem nor estimates the remaining
natural-prime-order case. No sufficient signed estimate was found in this
review. The latest actual new theorem is the fixed-sequence obstruction above.

## Nested positivity and growing multiplier-range review (no new estimate)

Reviewed FixedPrimeAvoidanceSkew, FixedMaxMultiplicativeSymmetry,
AdjacentThresholdExpansion, ActualPrimeComparisonTransfer,
DoublePrimeAveraging, and PrimeLogQuantization. No new signed arithmetic
estimate or Lean theorem was obtained in this pass.

The precise stronger invariance already proved is primeQuantLabel_mul:
for N>1, k>0, k^Q<N, and EVERY n, primeQuantLabel Q N (k*n) equals
primeQuantLabel Q N n. Thus the actual endpoint-dependent quantization has
a positive-power multiplier range; the new fixed stable countermodel does
not refute a theorem exploiting such a quantitative range.

However, using those multipliers in the existing natural transfer still
produces the shorter adjacent endpoint N/p. Moving the source to p*N to
hit a prescribed endpoint changes the sampling law with the prime/entropy
scale. No valid replacement for the same-source entropy recurrence was
found. Double-prime averaging retains the determinant-one cofactor sum;
its unconditional replacement error is not cancellation of that sum.

Nested nonnegative multiplicativity also does not make the existing fixed-
cutoff reversal theorem uniform. The moving cutoff case still retains the
prime-weighted opposite-residue/long-complement kernel. No passage from a
fixed-set limit, an unsigned sieve bound, or an unweighted inverse estimate
to the required signed moving-cutoff limit was asserted.

The low-product partition moment route was also rechecked against the
existing finite fixed-marginal obstruction. No uniqueness result for the
actual continuous prime-factor law, and no new arithmetic input outside
the low-product range, was obtained. Spec.lean remains unchanged and
unresolved; no complete proof/disproof is ready to submit.

## Further growing-range and complementary-divisor review (no new theorem)

Investigated whether the positive-power exact multiplier range permits a
same-target entropy argument through rough-core labels. The existing transfer
still requires either a common source law (with endpoints N/p) or a new
scale-dependent entropy recurrence. No such recurrence was established.
A rough-core graph formulation leaves an oriented determinant-one/S-unit
count; neither a graph expansion estimate nor an appropriate signed operator
bound was proved. This formulation is not itself a cancellation estimate.

Also revisited long complementary divisors, maximal prefix cancellation,
and prime toggling. The existing unit-complement absolute-mass obstruction
and largest-prime-toggle boundary remain relevant. An unrestricted alternating
divisor identity does not justify cancellation after the moving cutoff, and
the already cancelled short window does not cover the full complementary
range. No new signed estimate was obtained, and none of these observations
was promoted to a proof or disproof. Spec.lean is unchanged.

## NEW arithmetic advance: summable moving lower-prime boundary

Three new completed modules compile, with saved .oleans. All printed main
axiom checks are exactly propext, Classical.choice, Quot.sound.

1. RankinPrimeHarmonic.lean
   - prime_neg_rpow_sum_le_primeHarmonic retains the prime harmonic sum
     instead of bounding by the full harmonic sum.
   - smooth_rankin_primeHarmonic_bound, for 1/2<=s<=1:
       #smoothNumbersUpTo(N,B)
         <= N^s * exp(4*B^(1-s)*primeHarmonic(B)).
   - smooth_double_power_rankin_ratio: for j>=1,
       #smoothNumbersUpTo(2^(k+1),2^(2^j))/2^(k+1)
         <= exp(96*(j+1) - (k+1)/2^j*log(2)).
     Uses the earlier elementary double-power upper Mertens bound.

2. DyadicLowPrimeBoundary.lean
   - lowPrimeBandIndex(k) is the greatest j<=k with
       512*(j+1)*2^j <= k+1.
   - lowPrimeBandCutoff(k)=2^(2^j).
   - The index and cutoff are monotone and tend to infinity. For k>=2047,
       j <= log_2(k+1) <= 2*j+12,
       1/(1024*(j+2))
         < log(cutoff(k))/log(2^(k+1))
         <= 1/(512*(j+1)).
     Thus the logarithmic cutoff ratio has order 1/log(k) and tends to zero.
     All displayed finite inequalities and the zero limit are checked.
   - lowPrimeBand_smooth_ratio: for k>=2047 the smooth proportion at the
     upper dyadic endpoint is <=1/(k+1)^2, uniformly in the moving cutoff.
   - summable_dyadicLowPrimeReciprocal: the sum of 1/n over
       P(n)<cutoff(log_2(n))
     is finite. This is absolute reciprocal summability, not just density 0.
   - summable_dyadicLowLoserReciprocal strengthens this to EITHER neighbor:
       min(P(n),P(n+1))<cutoff(log_2(n)).
     Monotonicity of the cutoff and 1/n<=2/(n+1), n>=1, control the shifted
     term. The n=0 division-by-zero term is handled explicitly.

3. DyadicTwoSidedBoundary.lean
   - dyadicInteriorSign retains factorSign exactly when the loser is at
     least this lower cutoff and the winner is at most the previously
     proved threeQuarter upper threshold.
   - dyadicLowNotHighSign handles the overlap correctly; it is supported
     on the low-loser event but outside the high-winner event.
   - Its harmonic series is absolutely summable.
   - dyadic_boundary_rawHarmonic_converges: the UNNORMALIZED ordinarily
     ordered harmonic partial sums of factorSign-interiorSign converge.
     Combines the low-boundary summability with the earlier high-winner
     signed convergence, without double-counting their intersection.
   - dyadic_boundary_natural_mean_zero follows by the checked Kronecker
     lemma. It does not assert any mean limit for interiorSign.

LIMITATION: no signed estimate for the intervening comparison pairs was
proved. These bounds remove genuine moving arithmetic boundaries, but the
original natural-density theorem remains unresolved. Spec.lean retains
its original sorry and unchanged SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof/disproof has been submitted. Removed CheckLowRankin.lean
and CheckLowIndex.lean. No temporary incomplete scaffold from this pass remains.

## Interior Vaughan/factorization review after the two-sided boundary (no estimate)

Reviewed VaughanPrimeKernel, VaughanArithmetic, ComparisonBandTuples, and
BalancedBilinear. The new boundary theorems do not supply a bound for the
surviving long convolution. Regrouping its Mangoldt factor with zeta gives
logarithmic mass minus a finite small-divisor contribution, but summing the
resulting bounded progression errors over the long Mobius index still loses
an uncontrolled factor. No signed average over that index was proved.

Also checked the logarithmic-weight removal idea against the previous audit:
Lambda*zeta=log yields weighted marginal/cut-flow identities, not the needed
ordered prime-band correlation. Removing 1/log(q) introduces the already
unestimated cofactor-weighted sums. The exact tuple representation retains
both product equations and the arithmetic weights; an unweighted inverse
rectangle estimate cannot be substituted for a weighted one.

No additional theorem was added in this pass, and no sufficient interior
cancellation estimate was obtained. The newest actual arithmetic results
remain RankinPrimeHarmonic, DyadicLowPrimeBoundary, and DyadicTwoSidedBoundary.
Spec.lean is unchanged with its original sorry. No complete proof/disproof
has been submitted.

## Fixed stable obstruction strengthened to summable harmonic defects

NEW checked module: Submission/FixedStableSummableDefects.lean (134 lines).
Imports FixedStableBias and PrimeWinnerHarmonicLimits. Namespace
Erdos371.ExactMultiplierChirpObstruction. Saved .olean; all three printed
main axiom checks are propext, Classical.choice, Quot.sound.

- fixedBiasedPhase_comp_defect_harmonic_bound: for every map g:Complex->A,
  every fixed k>0, and every n, the absolute harmonic dilation defect of
  g composed with fixedBiasedPhase is bounded by smoothReciprocal(biasBand k,n).
- fixedBiasedPhase_comp_summable_harmonic_defects: those absolute harmonic
  defects are summable for EVERY fixed positive multiplier and every g.
- maxPrimeFac_comp_summable_harmonic_defects proves the corresponding
  property for every relabelling of the ACTUAL maxPrimeFac sequence, with
  smoothReciprocal(k,n) as the majorant. This uses maxPrimeFac(k)<=k and
  maxPrimeFac(k*n)=max(maxPrimeFac(k),maxPrimeFac(n)).
- exists_fixed_three_label_map_nonzero extracts ONE g:Complex->Fin 3 whose
  composition with fixedBiasedPhase has ordinary order-skew mean not
  tending to zero. The map is not reselected at each endpoint.
- exists_fixed_three_label_summable_defects_natural_gap packages ONE fixed
  three-label sequence with all of:
    * absolute harmonic summability of every fixed-multiplier defect;
    * natural mean-zero dilation defects for every fixed multiplier;
    * harmonic order-skew mean tending to zero;
    * ordinary order-skew mean NOT tending to zero.

This turns the prior informal summable-defect warning into a checked theorem.
It rules out upgrading the generic harmonic theorem merely by adding
absolute harmonic summability of the fixed-multiplier defects. The constructed
labels do NOT have the max-under-multiplication law and are NOT Nat.maxPrimeFac.
It is not a disproof of Erdos 371. No positive-power multiplier-range claim
or quantitative O(log k) bound on its total harmonic defect is established.

Continued reviews of the positive-power multiplier route and the balanced
interior determinant-one/Vaughan expansions produced no new sufficient signed
estimate. The natural entropy transfer still retains the endpoint N/p; a
new same-target recurrence was not proved. Low-product moment and unweighted
inverse-rectangle estimates were not promoted to the required weighted or
nonlinear conclusions. Another external status request failed with DNS error.

Spec.lean remains unchanged, SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff,
with its original sorry. No complete proof/disproof is ready or submitted.

## Infinite prime-seven harmonic current is rigorously negative

NEW checked module: Submission/PrimeSevenHarmonicCurrent.lean.
Imports PrimeWinnerHarmonicFlux; namespace Erdos371. No admissions or unsafe
evaluation. Both printed main axiom checks are propext, Classical.choice,
Quot.sound. Saved .olean.

Main new arithmetic result:
  primeWinnerHarmonicLimit_seven_neg :
    primeWinnerHarmonicLimit 7 < -1/5000
and consequently
  not_primeWinnerHarmonicLimit_nonneg :
    NOT (forall prime p, 0 <= primeWinnerHarmonicLimit p).

This concerns the INFINITE fixed-prime current, not just the already known
negative partial sum at N=15. It invalidates the possible repair that all
individual currents become nonnegative after taking their fixed-prime limits.

Certification, fully checked in Lean:
- M = 2^17 * 3^10 * 5^7 * 7^6 = 71137851402240000000.
- The sum of divisors of M is 311223981113330718888, proved from coprime
  multiplicativity and prime-power geometric sums (not by scanning 1..M).
- The finite reciprocal divisor sum is sigma(M)/M.
- The reciprocal sum over all positive 7-smooth integers is exactly 35/8,
  by the finite Euler product.
- sevenBoxTail(n) is 1/n on 7-smooth n not dividing M, zero otherwise.
  Its sum is exactly 908018401517/15682947840000000.
- A finite kernel certificate checks all 18*11*8*7 = 11088 exponent tuples.
  If n and n+1 both divide M and one is divisible by 7, then n belongs to
    {6,7,14,20,27,35,48,49,63,125,224,2400,4374}.
- Retaining precisely the harmonic winner-seven terms for which both n and
  n+1 divide M gives sum -90077/214326000.
- The omitted term is bounded above by
    sevenBoxTail(n) + 2*sevenBoxTail(n+1).
  This uses P(n),P(n+1)<=7 and 1/n<=2/(n+1), with n=0 handled separately.
  Hence ALL omitted terms contribute at most 3 times the exact tail mass.
- The resulting rational upper bound is strictly below -1/5000.

No complete Størmer/Pell/S-unit enumeration is assumed. The finite box need
not contain every consecutive 7-smooth pair: the Euler-product remainder
rigorously accounts for any others. An initial exact rational diagnostic at
p=7 tested this specific limiting-positivity hypothesis; it was not a blind
numerical search for a counterexample to the density conjecture.

Also rechecked prime-weighted energy. Its diagonal and endpoint are already
proved negligible in PrimeLoserPrimeWeightedCollisions. Improving those alone
cannot bound the retained signed off-diagonal mass. No sufficient new signed
bound for growing prime labels was found.

IMPORTANT: negative fixed-prime harmonic current does NOT disprove Erdos 371.
It supplies no nonzero natural-density bias. It only rejects the individual
limiting-current positivity shortcut to unnormalized tail tightness. That
uniform tail bound, the prime-weighted energy bound, and the original density
conjecture remain unresolved. Spec.lean is unchanged with its original sorry.
No valid complete proof/disproof is ready or submitted. CheckSeven.lean removed.

## Averaged-reflection continuation after the prime-seven result (no new estimate)

Reviewed AllocationReflectionCheck, HighWinnerMarkCoverage, the marked inverse
hyperbola chain, ComparisonAllocationApproximation, and the previous reciprocal
mark unweighting results. Averaging several admissible marks does not by itself
remove their nonuniform multiplicities. Pointwise normalization changes the
weights under reflection; no weighted cancellation estimate for the resulting
kernel was proved.

Also considered symmetrizing the reflection graph into a finite reversible
transition kernel. Uniform stationarity alone does not imply unweighted sign
balance when the probability of taking a sign-flipping edge varies by state.
The needed approximately constant accepted row mass (or an equally strong
control of its sign correlation) remains unproved. It was not assumed from
coverage, reversibility, or the presence of self-loops.

No new sufficient signed arithmetic estimate or Lean theorem resulted from
this review. The positive-power multiplier strategy still needs a valid
same-target natural transfer or another new mechanism. The recently checked
PrimeSevenHarmonicCurrent module remains an auxiliary arithmetic obstruction,
not a density disproof. Spec.lean is unchanged with its original sorry; no
complete proof/disproof is ready or submitted.

## Fixed-ratio harmonic-window continuation (no new estimate)

Reviewed RawHarmonicTauberian, HarmonicWindowDilation,
HarmonicQuantizedTransfer, DyadicTwoSidedBoundary, and the earlier dyadic
comparison identities. Fixed-prime convergence and the two discarded moving
boundaries do not estimate the surviving signed interior sum on [N,c*N].
No uniform short harmonic-window cancellation was proved.

Important qualification: cancellation over factor-TWO windows alone is not
an adequate generic Tauberian hypothesis. A bounded sequence can have a
harmonic primitive periodic in log(N), hence zero increments at scale two,
while retaining nonzero ordinary-mean oscillations. Control over an appropriate
richer family of ratios (or an additional arithmetic exclusion of this
phenomenon) would be required. No implication from a single-ratio hypothesis
was asserted or inserted into Lean.

No new sufficient signed arithmetic estimate or Lean theorem was obtained.
Spec.lean remains unchanged with its original sorry. No valid complete
proof/disproof is ready or submitted.

## Odd logarithmic moment continuation (no new estimate)

Rechecked LogarithmicCubicMoment, LogarithmicSignedReduction,
CompleteMixedMass, and FixedMarginalPartitionPerturbation. The exact cubic
identity still leaves the mixed term X^2*Y-X*Y^2. Pure-power increments
telescope, but the mixed term does not. Logarithmic divisor identities and
cofactor substitutions did not supply its signed mean cancellation; a
cofactor substitution reexpresses the correlation rather than contracting it.
No passage from low-product inclusion moments to the nonlinear comparison
was used. No new sufficient arithmetic estimate or Lean theorem resulted.
Spec.lean remains unchanged with its original sorry; no complete proof or
disproof is ready or submitted.

## Uniform logarithmic total harmonic dilation-defect budget

NEW checked module: Submission/QuantitativeSmoothReciprocal.lean (213 lines).
Imports RankinSmoothBound and PrimeWinnerHarmonicLimits. Namespace Erdos371.
Compiles without warnings at the default heartbeat limit; saved .olean.
All three printed main axiom checks use exactly propext, Classical.choice,
and Quot.sound. No admissions or unsafe evaluation.

Main results:
- nat_neg_rpow_tsum_condensed_bound: for s>1,
    sum_{n>=0} n^(-s) <= (1-2^(1-s))^(-1).
  This follows from the finite Cauchy condensation bound, the ordinary
  p-series convergence theorem, and a geometric-series limit.
- reciprocal_one_sub_exp_neg_le: for x>0,
    (1-exp(-x))^(-1) <= 1+1/x.
- primeEulerFactor_comparison: for prime p and d>0,
    (1-1/p)^(-1)
      <= exp(d*log(p)/(p-1)) * (1-p^(-(1+d)))^(-1).
- primeEulerProduct_rpow_le_tsum: for s>1, the finite smooth Euler product
  is bounded above by the full positive p-series.
- primeEulerProduct_le_log: for B>1,
    prod_{p<B}(1-1/p)^(-1) <= exp(4)*(1+log(B)/log(2)).
  Take d=1/log(B), compare factors, and use the existing elementary
  sum_{p<B} log(p)/(p-1) <=4log(B), then the condensation bound.
- smoothReciprocal_hasSum identifies the smooth reciprocal sum with the
  finite Euler product.
- smoothReciprocal_tsum_le_log: for B>0,
    sum_n smoothReciprocal(B,n) <= exp(4)*(1+log(B+1)/log(2)).
- maxPrimeFac_label_harmonic_defect_le supplies the uniform pointwise
  smoothReciprocal(k,n) majorant for every g:N->A and k>0.
- maxPrimeFac_label_total_harmonic_defect_le_log: for every g:N->A, k>0,
    sum_n norm(labelDilationDefect(k,g o maxPrimeFac,n)/n)
      <= exp(4)*(1+log(k+1)/log(2)).
  The summability needed for comparing real tsums is proved from the
  pointwise majorant, not assumed. No countermodel module is a dependency.

SIGNIFICANCE AND LIMITS:
This strengthens fixed-k absolute summability to a uniform O(log k) budget.
It does NOT prove that this quantitative hypothesis gives a generic
harmonic-to-natural bridge. No such implication is asserted. In particular,
it bounds changes under multiplication, not changes of an adjacent ordinary
mean from endpoint N to N/p. The existing smooth-number counting estimate
already gives natural defect control for a growing multiplier range; the
same-target entropy recurrence remains missing.

Revisited the weighted inverse-congruence sums after this estimate. The
available Kloosterman bounds apply to unweighted/Fourier-controlled tests;
no new control of the retained Mobius or reciprocal fiber-multiplicity
weights was found. The long Vaughan kernel is still unestimated. No weighted
conclusion was inferred from an unweighted rectangle estimate.

Spec.lean remains unchanged with its original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof is ready or submitted. CheckQuantEuler.lean
was removed. The original natural-density conjecture remains unresolved.

## Sharp total harmonic dilation budget and exact Euler product

NEW checked module: Submission/SharpHarmonicDilationBudget.lean.
Imports QuantitativeSmoothReciprocal; namespace Erdos371. Saved .olean.
Compiles without warnings. All four printed main axiom checks use exactly
propext, Classical.choice, Quot.sound. No admissions or unsafe evaluation.

Define maxPrimeHarmonicDefect(k) as the sum over n of the absolute harmonic
label-dilation defect for the unrelabeled Nat.maxPrimeFac sequence.

- mem_smoothNumbers_iff_maxPrimeFac_lt: for B>1, n is B-smooth iff
  n is nonzero and maxPrimeFac(n)<B. Handles the junk values at 0 and 1.
- maxPrimeFac_harmonic_defect_eq_smooth: for k>1, the harmonic defect at n
  is EXACTLY smoothReciprocal(P(k)-1,n), not merely bounded by it.
- maxPrimeHarmonicDefect_eq_product: for k>1,
    D(k) = prod_{p<P(k)} (1-1/p)^(-1).
- log_maxPrimeFac_le_total_harmonic_defect:
    log(P(k)) <= D(k),
  using the harmonic sum through P(k)-1 as a subseries.
- total_harmonic_defect_le_log_maxPrimeFac:
    D(k) <= exp(4)*(1+log(P(k))/log(2)).
- prime_log_le_total_harmonic_defect: for each prime p, log(p)<=D(p).
- not_total_harmonic_defect_sublogarithmic:
    NOT Tendsto (D(k)/log(k)) atTop (nhds 0),
  using arbitrarily large primes.

Consequently a uniformly sublogarithmic improvement of the total defect
bound is impossible, even for the actual largest-prime-factor labels. This
only concerns the defect budget; it does not refute a potential theorem
using the O(log k) bound together with further arithmetic structure. It
also does not contradict exact small-multiplier stability of the moving
primeQuantLabel family.

Reconsidered same-target transfer through positive-power stability and
rational multipliers. No same-target entropy recurrence was proved.
Conditioned dilation still changes N to N/p; rational dilation would
require a new control of residue-conditioned, differently scaled pairs.
It was not inferred from the max law. No new sufficient signed arithmetic
estimate resulted. Spec.lean remains unchanged with its original sorry;
no complete proof/disproof is ready or submitted.

## Signed odd-character/cofactor continuation: no new estimate

Revisited CommonEndpointPrimeSkew, OddCharacterSkew,
OppositeProgressionWeights, and the existing dyadic rectangularization.
The principal and all other even characters are already absent. The
cofactor Gram identity already gives exact diagonal energy on short
initial intervals. An optimal diagonal-size prime-character second moment
still loses too much after absolute summation over moduli above sqrt(N).
No new signed cross-modulus cancellation was obtained.

Considered completing the cofactor character sum to inverse-prime
exponential sums and then a bilinear Kloosterman-fraction treatment.
The required uniformity in the Fourier frequency and in the short cofactor
range was not proved. Neither the existing unweighted inverse-rectangle
bound nor a hypothetical individual character-sum estimate was used as a
substitute. This review produced no new Lean theorem and no sufficient
arithmetic estimate. Spec.lean is unchanged with its original sorry.
No complete proof or disproof is ready or submitted.

## Uniform reciprocal tails and simultaneous harmonic-current head errors

TWO NEW checked modules, saved .olean files, no warnings, default heartbeat
limits. All printed main axiom checks use exactly propext, Classical.choice,
Quot.sound. No admissions or unsafe evaluation.

A. Submission/UniformSmoothReciprocalTail.lean (341 lines)
Imports QuantitativeSmoothReciprocal; namespace Erdos371.

- primeEulerFactor_below_one_comparison: for 0<d<=1/2,
    (1-p^(-(1-d)))^(-1)
      <= (1-1/p)^(-1)*exp(4*d*log(p)*p^d/p).
- primeEulerProduct_below_one_comparison: the finite product at 1-d is
  at most its value at 1 times exp(16*d*B^d*log(B)). This retains the
  logarithmic Euler-product prefactor instead of using the older coarse
  exp(4*B^d*primeHarmonic(B)) bound.
- smoothRpow(B,s,n) and smoothRpow_hasSum give the smooth p-series for
  EVERY s>0; the full all-integer p-series need not converge.
- smoothReciprocalTail(B,N) is sum_{n>=N} smoothReciprocal(B,n).
- smoothReciprocalTail_rankin_bound bounds it by N^(-d) times the finite
  Euler product at exponent 1-d.
- smoothReciprocalTail_parameter_bound: for B,N>0 and 0<d<=1/2,
    tail <= N^(-d)*exp(4)*(1+log(B+1)/log(2))
              *exp(16*d*(B+1)^d*log(B+1)).
- smoothTailExponent(B)=log(2)/(32*log(B+1)) is positive and <=1/32.
  Its extra Euler-product loss is <=2.
- smoothReciprocalTail_uniform_bound: for B,N>0,
    tail <= 2*exp(4)*(1+log(B+1)/log(2))
              *exp(-log(2)*log(N)/(32*log(B+1))).
  This is UNIFORM in both cutoff and endpoint.
- harmonicLabelDefectTail(k,N,L) sums the absolute harmonic dilation
  defects at n>=N.
- maxPrimeFac_harmonicLabelDefectTail_le bounds that tail by the smooth
  reciprocal tail at B=k for every g:N->A, L=g o maxPrimeFac, k>0.
- maxPrimeFac_harmonicLabelDefectTail_uniform_bound gives the preceding
  explicit bound uniformly in k,N and in the relabelling g.
- smoothReciprocalTail_large_u_bound: if u>=1024,
    u*log(B+1)=log(N), log(u)<=4*log(B+1), B,N>0,
    tail <= exp(4)*(1+log(B+1)/log(2))*exp(-u*log(u)/16).
  Choose d=log(u)/(8*log(B+1)). The optimizing exponent stays <=1/2 by
  the explicit range hypothesis. This is not an assumed Dickman asymptotic.

B. Submission/UniformPrimeCurrentHead.lean (105 lines)
Imports UniformSmoothReciprocalTail; namespace Erdos371.

- real_tsum_tail_ite_eq_nat_add relates the indicator and shifted tail
  conventions for a summable real sequence.
- primeWinnerHarmonic_error_le_tail bounds each fixed-prime limit error
  by its absolute harmonic tail.
- sum_primeWinnerHarmonicTerm_norm_le_smooth: at each n,
    sum_{p<=B} norm(primeWinnerHarmonicTerm(p,n))
      <= smoothReciprocal(B,n).
  Exactly one winner label can contribute; there is NO factor B.
- primeCurrentHeadError(B,N) is
    sum_{p<=B} norm(primeWinnerHarmonicLimit(p)-rawPrimeWinnerHarmonic(p,N)).
- MAIN primeCurrentHeadError_le_smoothReciprocalTail:
    primeCurrentHeadError(B,N) <= smoothReciprocalTail(B,N).
  Finite-sum/tsum interchange is justified by absolute summability.
- primeCurrentHeadError_uniform_bound and primeCurrentHeadError_large_u_bound
  specialize the new quantitative tail estimates to this simultaneous l1
  approximation. They are uniform over the growing head cutoff B whenever
  the explicitly displayed right-hand sides are small.

IMPORTANT LIMITATION:
These are bounds on the SMALL-LABEL HEAD errors, not on the complementary
large-label currents. They do not establish rawPrimeHarmonicTail tightness
in RawHarmonicTauberian, do not bound the signed interior kernel, and do not
bridge harmonic cancellation to natural density. No such implication was
inserted or claimed. Spec.lean is unchanged with its original sorry. No
complete proof or disproof is ready or submitted.

Lean note: specifying f explicitly in summable_nat_add_iff when f is a norm
of a prime-current term avoids expensive metavariable reduction. Likewise,
first give hs.of_norm the explicit type Summable(primeWinnerHarmonicTerm p)
before using its sum_add_tsum_nat_add theorem. This eliminated the temporary
need for a larger heartbeat limit. CheckCurrentHead.lean and
CheckCurrentSum.lean were removed.

## Explicit moving-cutoff simultaneous prime-current convergence

NEW checked module: Submission/MovingPrimeCurrentHead.lean.
Imports UniformPrimeCurrentHead and DyadicSeriesTools; namespace Erdos371.
Saved .olean, no warnings, default heartbeat limit. Both printed main axiom
checks use exactly propext, Classical.choice, Quot.sound.

- double_power_current_head_bound: if N>0 and
    64*(j+1)*2^j*log(2) <= log(N),
  then
    primeCurrentHeadError(2^(2^j)-1,N) <= exp(4)*(1/2)^j.
  It specializes the uniform reciprocal-tail estimate. All real logarithms,
  casts, and the natural subtraction in the cutoff are explicitly checked.
- currentHeadBandIndex(k) is the greatest j<=k with
    64*(j+1)*2^j <= k.
  Its budget is proved for k>=64, and the index tends to infinity.
- movingCurrentHeadCutoff(N) is
    2^(2^(currentHeadBandIndex(log_2 N)))-1.
- movingCurrentHeadCutoff_tendsto proves this explicit cutoff tends to
  infinity (it is NOT fixed before taking the endpoint limit).
- movingCurrentHeadError_eventual_bound supplies the geometric bound
  exp(4)*(1/2)^(currentHeadBandIndex(log_2 N)) at all sufficiently large N.
- MAIN moving_prime_current_head_error_tendsto_zero:
    Tendsto [N |-> sum_{p<=movingCurrentHeadCutoff(N)}
       norm(J_p(infinity)-J_p(N))] atTop (nhds 0).
  This is UNNORMALIZED simultaneous l1 convergence for the moving head.

The result does NOT control the complementary sum over larger prime labels.
No inference to rawPrimeHarmonicTail tightness or natural density was made.
Explorations of using the stronger invariance under arbitrarily large smooth
multipliers did not give a same-target natural transfer: the necessary
residue-conditioned pair laws still have different endpoint scales.
No sufficient signed estimate was proved in this continuation.

Spec.lean remains unchanged with the original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof is ready or submitted.

## Per-prime incidence budgets and unnormalized full-vector l2 convergence

TWO NEW checked modules, saved .olean files, no warnings, default heartbeat
limits. Main printed axiom checks use exactly propext, Classical.choice,
Quot.sound. No admissions or unsafe evaluation.

A. Submission/PrimeCurrentAbsoluteBudget.lean
Imports SharpHarmonicDilationBudget and PrimeWinnerHarmonicFlux.
Namespace Erdos371.

- primeLabelReciprocal(p,n) = 1/n when P(n)=p, zero otherwise; proved
  nonnegative and summable, using the smooth reciprocal majorant.
- primeLabelReciprocal_mul_prime: for prime p,
    primeLabelReciprocal(p,p*n) = (1/p)*smoothReciprocal(p,n).
- primeLabelReciprocal_tsum gives the EXACT mass
    sum_{P(n)=p} 1/n = (1/p)*prod_{q<=p}(1-1/q)^(-1).
  Reindexing by multiplication by p is justified with an injective map
  whose image contains the support.
- primeWinnerLoser_label_incidence: the max/min label incidences equal
  the incidences of the two endpoint labels, with multiplicities.
- primeWinnerLoserHarmonicTerm_norm_bound:
    norm(winnerTerm(p,n))+norm(loserTerm(p,n))
      <= primeLabelReciprocal(p,n)+2*primeLabelReciprocal(p,n+1).
- primeWinnerLoserHarmonic_abs_tsum_bound: for prime p, the total of
  both absolute harmonic incidence series is at most
    (3/p)*prod_{q<=p}(1-1/q)^(-1).
- primeWinnerLoserHarmonic_abs_tsum_log_bound sharpens this to
    3*exp(4)*(1+log(p+1)/log(2))/p.
  Unlike the older smooth-set bound, this retains the factor 1/p.
- The norms of the winning-prime LIMIT and EVERY finite raw winning
  current are bounded by this same full incidence mass.

B. Submission/PrimeCurrentL2Convergence.lean
Imports PrimeCurrentAbsoluteBudget; namespace Erdos371.

- For positive n, primeWinner(n) is prime (use P(n*(n+1))). Thus all
  harmonic winner terms, raw currents and limits at nonprime labels are
  zero; the n=0 division-by-zero term is handled separately.
- Explicit constant C=3*exp(4)*(1+8/log(2)) is positive.
- The logarithmic per-prime budget is <= C*p^(-3/4). This follows from
  log(x)<=4*x^(1/4), p+1<=2p, and a basic real-power comparison.
- rawPrimeWinnerHarmonic_uniform_rpow_bound and
  primeWinnerHarmonicLimit_uniform_rpow_bound hold at ALL labels, with
  the former uniform in the endpoint N.
- harmonic_prime_current_l2_error_bound:
    norm((J_p(N)-J_p(infinity))^2) <=4*C^2*p^(-3/2).
  The majorant is summable over all natural labels, not only primes.
- summable_primeWinnerHarmonicLimit_sq proves the limiting current
  vector is square summable.
- MAIN harmonic_prime_current_l2_convergence:
    Tendsto [N |-> sum'_p (J_p(N)-J_p(infinity))^2] atTop (nhds 0).
  This is UNNORMALIZED strong l2 convergence of the FULL current vector,
  obtained by dominated convergence from the already checked coordinate
  limits. It is not only a finite-head or normalized-harmonic assertion.

LIMITATIONS:
No l1 summability or l1 convergence of the currents is proved. The constant
weight 1 on all primes is not an l2 test, so the full-vector l2 theorem
cannot be substituted for unweighted raw-harmonic convergence or for the
rawPrimeHarmonicTail hypothesis in RawHarmonicTauberian. The required
natural-density cancellation is still unresolved. Spec.lean is unchanged
with its original sorry; no complete proof/disproof is ready or submitted.
CheckPrimeMass.lean was removed.

## Exact summable divergence and reciprocal-rate full l1 divergence convergence

TWO NEW checked modules, saved .olean files, no warnings, default heartbeat
limits. Printed main axiom checks use only propext, Classical.choice,
Quot.sound. No admissions or unsafe evaluation.

A. PrimeHarmonicDivergenceMass.lean
- reciprocalFluxStep(n)=1/(n+1)-1/(n+2), nonnegative, with sum 1.
- primeDivergenceTerm(p,n)=1_{P(n+2)=p}*reciprocalFluxStep(n).
- primeDivergenceMass(p) is its tsum, nonnegative and zero for p<=1.
- Exact limiting flux: J_p(infinity)-L_p(infinity)
    =primeDivergenceMass(p)-primeLabelIndicator(p,1).
- primeDivergenceMass_hasSum: the masses sum to 1 over all labels.
- Explicit large-label tail <=1/(B-1), B>=2; the same bound holds
  for the l1 tail of J_p(infinity)-L_p(infinity).

B. PrimeHarmonicDivergenceConvergence.lean
- The endpoint point-mass A_M(p)=1_{P(M+2)=p}/(M+1) has total 1/(M+1).
- The nonnegative reciprocal remainder R_M(p) after n<M also has
  total 1/(M+1), by finite-sum/tsum interchange and telescoping.
- primeHarmonicFluxError(M,p) is
  [J_p(M+2)-L_p(M+2)]-[J_p(infinity)-L_p(infinity)].
- Exact identity: fluxError=A_M-R_M.
- MAIN primeHarmonicFluxError_l1_bound: sum_p norm(fluxError)<=2/(M+1).
- MAIN primeHarmonicFluxError_l1_tendsto_zero gives unnormalized l1
  convergence of the FULL DIFFERENCE VECTOR at a reciprocal endpoint rate.

This controls divergence, not winner or loser currents separately. A
shared signed circulation can have large total with zero divergence.
No winner-current l1 tail estimate or natural density is deduced.
Spec.lean is unchanged with its original sorry. CheckFluxMass.lean removed.

### Follow-up review after divergence convergence

Rechecked natural_prime_gap_transfer and conditioned_prefix_dilation: narrowing
prime multipliers still leaves shorter endpoints N/p. No same-target transfer
was established. Considered the full actual marginal law as extra information
beyond the finite low-mass inclusion countermodels. No reconstruction theorem
was obtained, nor was an absolutely continuous perturbation of the actual
Poisson-Dirichlet marginal proved. The finite countermodels were not promoted
to either claim. Reviewed dyadic subdivision and growing multiplier stability;
no new signed contraction or arithmetic estimate was proved. In particular,
the checked full l1 convergence of divergence is not substituted for winner
current tail tightness. Spec.lean remains unchanged and unresolved.

## Two multiplicatively independent harmonic windows: exact natural criterion

FOUR NEW checked modules, saved .olean files, no warnings, default heartbeat
limits. Printed main axiom checks use only propext, Classical.choice,
Quot.sound. No admissions or unsafe evaluation.

A. HarmonicWindowTauberian.lean
Imports RawHarmonicTauberian; namespace Erdos371.
- rawHarmonicSum_window identifies the difference with an Ico sum.
- harmonic_window_unweighting_error: for 0<L<=U and |f|<=1,
    |sum_{L<=n<U} f(n)-L*(H(U)-H(L))| <= (U-L)^2/L.
- prefixMean_harmonic_window_bound and the scaled version give
    |mean_{aN} f| <= (b/a)|mean_{bN} f|+(b/a)|H(aN)-H(bN)|
                        +(a-b)^2/(ab).
- prefixMean_grid_eventual_upper removes the restriction to integer-grid
  endpoints, with a vanishing relative endpoint error.
- MAIN prefixMean_limsup_le_of_harmonic_window: if a>b>0 and the
  UNNORMALIZED harmonic increments H(aN)-H(bN) tend to zero, then
    limsup_N |mean_N f| <= (a-b)/b.
- MAIN prefixMean_zero_of_narrow_harmonic_windows: arbitrarily narrow
  cancelling integer-ratio harmonic windows force ordinary mean zero.
  Neither convergence of H itself nor l1 prime-current tightness is required.

B. TwoRatioHarmonicTauberian.lean
Imports HarmonicWindowTauberian.
- irrational_log_two_div_log_three proved from unique prime divisibility:
  a rational log ratio would give 2^den=3^num, contradicting parity.
- GoodHarmonicMultiplier(H,a) means a>0 and H(aN)-H(N)->0; proved closed
  under multiplication using the actual scaled endpoint.
- harmonicPeriodLogGroup(H) consists of log(a)-log(b) for good positive
  integer multipliers. It is an additive subgroup, with negative powers
  represented by a denominator, not by an invalid integer substitution.
- If 2 and 3 are good, the subgroup is dense, using Mathlib's checked
  dense_addSubgroupClosure_pair_iff and the proved irrationality.
- narrow_good_harmonic_multipliers finds b<a with (a-b)/b<epsilon.
- MAIN prefixMean_zero_of_two_harmonic_windows: for |f|<=1,
    H(2N)-H(N)->0 AND H(3N)-H(N)->0 imply mean_N f->0.
- density_of_two_harmonic_windows specializes the conditional criterion
  to the original largest-prime comparison. BOTH hypotheses are unproved.

C. HarmonicWindowConverse.lean
Imports TwoRatioHarmonicTauberian.
- rawHarmonicSum_shifted_prefix_identity derives an exact Abel formula
  from the existing positive-denominator harmonic prefix identity.
- Fixed endpoint shifts have error <=k/N and hence vanish.
- vanishing_prefix_harmonic_window bounds a fixed-ratio weighted window
  of any sequence tending to zero, retaining its shorter lower endpoint.
- MAIN harmonic_window_zero_of_prefixMean_zero: natural cancellation
  implies H(aN)-H(N)->0 for EVERY fixed positive integer a.
- MAIN prefixMean_zero_iff_two_harmonic_windows gives the exact equivalence
  for every unit-bounded real sequence. A single ratio is not substituted.

D. InteriorWindowCriterion.lean
Imports HarmonicWindowConverse and DyadicTwoSidedBoundary.
- dyadicInteriorSign_abs_le.
- density_iff_interior_prefixMean_zero uses the already proved natural
  boundary error, in both directions.
- MAIN density_iff_two_interior_harmonic_windows: the UNCHANGED original
  conjecture is equivalent to the ratio-two and ratio-three UNNORMALIZED
  harmonic window limits for dyadicInteriorSign.
- dyadic_boundary_harmonic_window_zero: full and interior window sums
  differ by o(1) for EVERY fixed positive integer ratio. This follows
  from convergence of the discarded boundary's raw harmonic series.

IMPORTANT LIMITATIONS:
This is an analytic reduction, NOT a new signed arithmetic cancellation
estimate. Neither of the two interior window hypotheses is proved. It is
weaker than demanding convergence of the entire raw harmonic primitive or
winner-current l1 tightness, but its equivalence to natural cancellation
means it is not supplied by the known normalized harmonic theorem.
Rechecked the signed prime-incidence/energy and divisor-cycle formulas:
unsigned bounds and summable divergence still leave the shared signed
circulation unestimated. No sufficient new arithmetic estimate resulted.
Spec.lean retains the original sorry and checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof is ready or submitted.

Temporary CheckWindowTauber.lean, CheckDenseWindow.lean, and
CheckWindowConverse.lean were removed.

## Sublogarithmic absolute mass of the limiting prime currents

NEW checked module: LimitingPrimeCurrentMass.lean. Imports
UniformPrimeCurrentHead; namespace Erdos371. Saved .olean, no warnings,
default heartbeat limit. Main printed axiom checks use only propext,
Classical.choice, Quot.sound. No admissions or unsafe evaluation.

- rawPrimeWinnerHarmonic_eq_normalized identifies the raw current at N+2
  with harmonic(N+1)*primeWinnerHarmonicCurrent(N,p), including the zero term.
- rawPrimeWinnerHarmonic_head_norm_bound compares any contained finite head
  with the full normalized harmonic l1 mass.
- harmonic_power_log_bound controls harmonic((B+1)^K+1)/log(B+1) by
    K+(1+log 2)/log 2, uniformly for B>0.
- raw_prime_current_power_head_sublogarithmic: for each FIXED K>0,
    sum_{p<=B} norm(J_p((B+1)^K+2))/log(B+1) -> 0.
- prime_current_power_head_error_bound: uniformly for B>0 and all K,
    headError(B,(B+1)^K+2)/log(B+1)
       <= (4 exp(4)/log 2)*exp(-log(2)*K/32).
  This uses the verified smooth reciprocal tail estimate and keeps the
  exponent K fixed before taking B->infinity.
- limitingPrimeCurrentAbsPrefix(B)=sum_{p<=B} norm(J_p(infinity)).
- MAIN limiting_prime_current_mass_sublogarithmic:
    limitingPrimeCurrentAbsPrefix(B)/log(B+1) -> 0.
  Choose a fixed K making the uniform head-error constant small, then use
  normalized harmonic l1 cancellation at polynomial endpoints. There is
  no unjustified exchange of the endpoint and prime-cutoff limits.

The signed opposite-residue kernel was also reviewed again. The cofactor
Gram identity and character second moments still lose too much after
absolute summation over large prime moduli. No cross-modulus saving was
proved. The unweighted inverse-rectangle bounds were not applied to the
uncontrolled arithmetic weights. No new estimate for the long Vaughan
term or either signed interior harmonic window was obtained.

LIMITATIONS: the new limit-mass theorem is o(log B), not O(1), summability,
or l1 tail tightness. Sparse nonvanishing window imbalances are not ruled
out by a sublogarithmic cumulative bound. It does not imply either window
hypothesis of density_iff_two_interior_harmonic_windows. Spec.lean remains
unchanged with its original sorry and checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof is ready or submitted. CheckLimitMass.lean
was removed.

## Chirp obstruction excluded on every fixed positive-power multiplier range

FOUR NEW checked modules, saved .olean files, no warnings, default heartbeat
limits. All printed main axiom checks use only propext, Classical.choice,
Quot.sound. No admissions or unsafe evaluation. Namespace Erdos371.HigherChirp.

A. HigherLogDifference.lean (imports PolynomialMultiplierChirpExclusion)
- ascendingProduct(r,x)=prod_{j<r}(x+j), positive for x>0.
- reciprocalDifferenceKernel(r,x)=r!/ascendingProduct(r+1,x).
- Exact reciprocal difference K_r(x)-K_r(x+1)=K_(r+1)(x).
- positiveLogDifference(0,x)=log(x+1)-log(x), and
    positiveLogDifference(r+1,x)=D_r(x)-D_r(x+1).
- positiveLogDifference_integral:
    D_r(x)=integral_{t=0}^1 r!/prod_{j<=r}(x+t+j) dt, x>0.
  All interval-integrability requirements are proved.
- MAIN positiveLogDifference_bounds:
    r!/(x+r+1)^(r+1) <= D_r(x) <= r!/x^(r+1), x>0.

B. HigherChirpPhase.lean (imports HigherLogDifference)
- unitPhase(x)=exp(i*x), unit norm, imaginary part sin(x), subtraction
  becomes multiplication by the conjugate phase.
- unitPhase_higher_difference_bound: if n>0 and all r+2 consecutive
  multipliers n+j, 0<=j<=r+1, have |chirp(t,n+j)-1|<=eta, then
    |exp(i*t*D_r(n))-1| <= 2^(r+1)*eta.
  Proved recursively; no unproved high-order derivative estimate is used.
- unitPhase(1) != 1, using positivity of sin(1).

C. HigherChirpScale.lean (imports HigherChirpPhase)
- chirpDifferenceBase(r,N)=Nat.nthRoot(r+1,r!*N).
- The base tends to infinity, and
    base^(r+1) <= r!*N < (base+1)^(r+1).
- MAIN higher_chirp_phase_tendsto_one:
    N*D_r(chirpDifferenceBase(r,N)) -> 1.
  Lower/upper ratio bounds both tend to one. This is for ALL integer
  parameters N->infinity, not merely perfect powers.
- nthRoot_cast_le_rpow and chirpDifferenceBase_rpow_bound.
- MAIN chirpDifferenceBase_polynomial_range: if 1/(r+1)<delta, then
    base(r,N)+r+1 <= N^delta eventually.

D. AllPolynomialChirpExclusion.lean (imports HigherChirpScale)
- MAIN chirp_polynomial_multiplier_separation: for every delta>0, there
  exists eta>0 such that for EVERY sufficiently large N there is k with
    0<k, k<=N^delta, and |chirp(N,k)-1|>=eta.
  Choose r with 1/(r+1)<delta; the higher-difference phase approaches
  exp(i), while uniformly near-one multiplier values would force it near 1.
- MAIN no_uniform_polynomial_multiplier_invariance: the same separation
  prevents uniform multiplier invariance on this range along ANY diverging
  sequence of parameters.

SCOPE: This genuinely strengthens the previous SQUARE-ROOT-range exclusion
in PolynomialMultiplierChirpExclusion. It does NOT prove natural skew
cancellation for arbitrary polynomially stable finite labels, does not
supply a same-target natural entropy transfer, and does not settle Erdos371.
No claim that all auxiliary fixed-stable countermodels are chirps is made.
No claim about mean approximation of stripped chirps is inferred from this
uniform multiplier separation.

Natural endpoint review: splitting into residue-conditioned dilations still
changes N to N/p. A hypothetical entropy recurrence with a sampling law that
varies at each scale was not used as if it followed from the existing
same-law stationary recurrence. No such new recurrence was proved. The two
signed interior windows remain unestimated. Spec.lean is unchanged with its
original sorry and checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof/disproof is ready or submitted.

Removed CheckHigherChirp.lean, CheckNthRootChirp.lean, CheckHigherScale.lean.
Lean notes: fully qualify Finset.prod_le_prod when Filter is open. The general
squeeze theorem is tendsto_of_tendsto_of_tendsto_of_le_of_le' (or the Tendsto
field squeeze'), not a standalone squeeze'. Use eventually_const_lt for a
lower bound from a neighborhood limit. Put whitespace/parentheses around
`< m N`; otherwise `<m` can parse as matroid notation. Nat.nthRoot size lemmas
are available transitively from Analysis.SpecialFunctions.Pow.NthRootLemmas.

## Stationary low-mass obstruction extended to all finite patterns

NEW checked module: StationaryPatternObstruction.lean. Imports
StationaryMomentObstruction; namespace Erdos371.StationaryPatternObstruction.
Saved .olean, no warnings, default heartbeat limit. Main printed axiom checks
use only propext, Classical.choice, Quot.sound. No admissions or unsafe evaluation.

This checks whether using more than two sites could bypass the existing
stationary finite-moment obstruction. It does not construct an arithmetic
counterexample and does not settle the conjecture.

- transitionReal(i,j)=2+splitValue(i)*mergeValue(j), with the two direction
  functions supported on disjoint state sets. Their pointwise product is zero.
- pathContinuation recursively sums the actual transition weights with each
  successive state restricted to the corresponding finite observation set.
- observationPathMass sums over the first observed state as well.
- pathContinuation_affine: every continuation is a+ b*splitValue(i).
- merge_weighted_continuation: multiplication by mergeValue kills the split
  term even with an arbitrary observation set inserted.
- observationPathMass_two_cons: if
    sum_A splitValue * sum_B mergeValue = 0,
  then mass(A::B::L)=2*card(A)*mass(B::L), for any remaining pattern L.
- CompatibleObservations asks only for that adjacent annihilation identity.
- compatible_path_mass: for any nonempty compatible list of observation sets,
    pathMass = 2^(length-1) * product of observation-set cardinalities.
- observation_classes_compatible derives the annihilation identity from the
  existing exact low-mass two-point moment factorization, retaining arbitrary
  tail-type conditions on both states.
- low_total_mass_compatible: the full observed-mass budget <=966 ensures the
  needed condition for every adjacent pair of a pattern of ANY finite length.
- MAIN low_mass_patterns_factor gives the exact product formula for all such
  finite patterns, not merely two-point moments at every gap.
- total_path_mass(k): the unrestricted length k+1 path has total 7*14^k.
- MAIN normalized_low_mass_patterns_factor: after dividing by the actual
  total path mass, every admitted finite pattern has exactly its independent
  uniform-state probability, product(card observations)/7^length.
- The preexisting largest_comparison_biased theorem still gives rising mass
  41 versus falling mass 43 in the adjacent transition table.

Arbitrary gaps can be represented by inserting unrestricted zero-mass
observations. This is a finite Markov-path identity; no new infinite-process
construction or claim of the actual Poisson-Dirichlet marginal is made.
The model still has diagonal mass 14, does not satisfy the actual arithmetic
max/dilation laws, and is NOT a counterexample to Erdos371. Consequently,
this result only rules out recovering comparison symmetry from these
stationarity and finite low-mass pattern identities alone. No sufficient
new signed arithmetic estimate was obtained. The two signed interior
harmonic-window limits remain unproved.

Spec.lean is unchanged, with its original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof is ready or submitted.

## NEW direct arithmetic bounds in relative natural windows

Read PositiveComparison.lean first: positive lower PREFIX proportions were
already proved. No duplicate prefix theorem was created. Revisited the
same-target entropy issue; the existing identity still changes N to N/p,
and no valid scale-dependent entropy recurrence was obtained. Also checked
that complementary small-part observations do not bypass the existing
merge/split partition obstruction: absence of further parts is not a
low-budget inclusion observable. No PD uniqueness argument was established.

Three NEW complete modules compile, with saved .oleans, no warnings, and
all main axiom checks exactly propext, Classical.choice, Quot.sound:

1. WindowLargePrimeLower.lean (imports TwoBandLargePrimeLower)
   - largePrimeDivisorSet_eq_high: for B>=1 the divisor union is exactly
     the set P(n+1)>B, including the endpoints/junk values correctly.
   - largePrimeDivisorSet_card_le_band: for L<=M<=B^2,
       count(P(n+1)>B,n<L) <= L*sum_{B<p<=M} 1/p.
   - filter_card_range_add_Ico: exact prefix/window count decomposition.
   - largePrime_window_ratio_ge_reciprocal: for B>1, 0<M, L<=M<=B^2,
     and L<=(1-theta)M,
       count(P(n+1)>B,L<=n<M)/M
         >= theta*sum_{B<p<=M}1/p - log4/logB.
     This uses one common prime band and does NOT subtract two lower bounds.
   - MAIN largePrime_power_window_eventually_ge: for fixed 1/2<v<1,
     theta>=0 and epsilon>0, eventually for ALL L<=M with
     L<=(1-theta)M,
       count(P(n+1)>M^v,L<=n<M)/M >= theta*(1-v)-epsilon.
     No prime number theorem is used; weighted-prime harmonic bounds suffice.

2. PositiveWindowComparison.lean (imports WindowLargePrimeLower,
   PositiveComparison)
   - A shift by one changes an interval predicate count by at most one.
   - The interval high-factor count is at most interval rises plus the
     full-prefix bothLargePrimeSet count; likewise for falls, with +1.
   - MAIN rising_falling_positive_window_proportions: for 0<theta<=1,
     exists delta>0 such that eventually for ALL L<=M with
     L<=(1-theta)M, both riseCount([L,M))/M and fallCount([L,M))/M >=delta.
     The proof chooses u=theta/[8*(largePairConstant+1)] and
     delta=theta*u/4, so it is an explicit positive quadratic-in-theta bound.
   - MAIN rising_falling_positive_integer_windows: for EVERY fixed pair of
     naturals a<b, both orientations have positive lower proportions on
     [a*N,b*N), normalized by N, uniformly for all sufficiently large N.

3. SignedWindowComparison.lean (imports PositiveWindowComparison)
   - Exact weighted signed/unsigned decomposition into rise and fall sums.
   - Cardinality/M bounds below the harmonic weight of any filtered
     positive interval [L,M).
   - MAIN signed_harmonic_window_strict_bound: for 0<theta<=1, exists
     delta>0 such that eventually for all 0<L<=M with L<=(1-theta)M,
       |sum_{L<=n<M} factorSign(n)/n|
         <= sum_{L<=n<M}1/n - 2*delta.
   - MAIN signed_natural_window_strict_bound: same quantifiers, allowing
     L=0, with
       |sum_{L<=n<M} factorSign(n)|/M <= (M-L)/M - 2*delta.

SCOPE: These are genuine bounds for the ACTUAL comparison, uniform over
relative windows, not auxiliary countermodels or merely conditional
reductions. They strengthen the earlier positive-prefix result but remain
NON-SHARP. They do not imply that either of the two interior harmonic
windows tends to zero, and they do not prove natural density one half.
Neither signed interior window has been estimated by o(1). No raw-current
tail tightness or signed collision cancellation approaching one half was
proved. The conjecture in Spec.lean is unchanged and unresolved.

Removed temporary CheckWindow.lean. Spec.lean SHA256 remains
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof is ready or submitted.

## Dyadic and growing-log-window continuation: no closing estimate

Re-read DyadicIterationCheck, DyadicHarmonicCancellation,
DyadicSeparatedBias, PrimeInsertionCheck, HarmonicStableSkewZero,
FixedHarmonicPrimeTransfer, and MixtureCyclicPrimeTransfer.

The new positive relative-window bounds do not control the signed conditional
between-event contribution in the dyadic identity. In particular they do
not repair the already checked failure of permanent branch pruning: cancelled
children can produce nonzero signed descendants. No contraction was asserted.

Considered extending the harmonic proof to averages on [L,M] with M/L->infinity.
The cyclic-mixture entropy theorem is genuinely uniform over mixtures, but
its application to shifted harmonic windows requires a new common-window
transfer and empirical-limit argument. The existing prefix theorem was not
used as if it already provided that uniformity. No such extension was proved.
Even normalized cancellation on all growing logarithmic windows would not
alone prove natural cancellation: bounded raw harmonic sums still permit
fixed-log-scale oscillations. The needed fixed-ratio unnormalized windows
at multipliers 2 and 3 remain a separate target.

No new Lean theorem or signed arithmetic estimate was obtained in this review.
The latest completed actual arithmetic advances remain WindowLargePrimeLower,
PositiveWindowComparison, and SignedWindowComparison. Their bounds are strict
but non-sharp. Spec.lean remains unchanged with its original sorry; no complete
proof/disproof is ready to submit.

## Nested-indicator and long-Vaughan continuation: no new estimate

Reviewed SmoothCutoffSkew, SmoothSkewCutoffStability, UpperHalfSmoothSkew,
NestedMultiplicativeSkew, FixedPrimeAvoidanceSkew, VaughanPrimeKernel,
ShortDivisorPrimeKernel, PrimePowerKernelReplacement, KloostermanFourthMoment,
InverseRectangleSmoothing, and the prior size-sensitive inverse bounds.

- The nested nonnegative multiplicative structure does not supply a checked
  uniform moving-cutoff theorem. Coalescing logarithmic cutoffs already have
  cancellation; distinct interior exponents still leave the signed band kernel.
  The fixed forbidden-set theorem and the residue-class diagnostic example
  were not mistaken for the needed uniform result or a disproof.
- Explored using the unweighted cofactor variable inside the long Vaughan
  convolution before Cauchy--Schwarz. Completing a remaining variable modulo
  p loses the short-interval factor needed above sqrt(N). Recovering that
  factor requires control of weighted inverse-product fibers. Neither the
  elementary Kloosterman fourth moment nor the unweighted inverse rectangle
  theorem supplies it for the Mobius/Mangoldt coefficients. No such weighted
  estimate was proved.
- Growing Vaughan truncation parameters do not by themselves remove the long
  term: making U*V exceed the endpoint destroys the available short-term bound.
  Absolute long-coefficient estimates still lose Mobius cancellation.

No new theorem or sufficient signed arithmetic estimate resulted. Spec.lean
remains unchanged with its original sorry. No complete proof/disproof is ready.

## NEW completed theorem: uniform growing-log-window harmonic half

This continuation completed the previously unproved translated-window
extension; it is NOT merely an audit or a conditional reduction. Nine new
modules compile, with saved .oleans, no warnings, and all printed main
axiom checks exactly propext, Classical.choice, Quot.sound. No admissions,
extra axioms, unsafe evaluation, or changes to Spec.lean.

Notation (namespace Erdos371.FiniteInformation):
  shiftedHarmonicRaw A M F = sum_{k<M+1} F(A+k+1)/(A+k+1).
  shiftedHarmonicMass A M = sum_{k<M+1} 1/(A+k+1).
  shiftedHarmonicMean A M F = raw/mass.
Thus the positive interval is [A+1,A+M+1], inclusive, and the lower endpoint
may be arbitrary, including A=0. Mass is strictly positive for every A,M.

1. DecreasingPrefixMixture.lean (imports HarmonicPrimeGapTransfer)
- General finite Abel identity for arbitrary real weights w.
- decreasingPrefixLaw is a genuine probability law for nonnegative weights
  decreasing through index N, with positive total mass W.
- Exact positive mixture representation of the weighted prefix mean.
- Exact reciprocal-length moment: E(1/componentLength)=w(0)/W.
- decreasing_weight_prime_gap_transfer: a common finite entropy horizon
  works for all such weights and labels; the explicit error is D*w(0)/W.
  The constant and horizon are chosen before weights, length, or labels.

2. ShiftedHarmonicAverages.lean
- shiftedHarmonicRaw is exactly the difference of positive raw prefix sums.
- Linearity, positivity, unit bounds, positive prefix mixture representation.
- Uniform nonnegative Abel bound: if S_F(t)<=eta*t+C for all t and F>=0,
    shiftedMean(A,M,F)<=eta+(eta+C)/mass(A,M), for C>=0, eta>=0.
- MAIN shiftedHarmonicMean_zero_of_nonnegative_prefix_zero: a unit-bounded
  nonnegative sequence of natural mean zero has shifted harmonic mean zero
  along EVERY interval sequence with mass->infinity, however slowly.
- shiftedHarmonicMean_shift_bound: unit observables have fixed-shift-by-one
  error <=4/mass, uniform in both endpoints.

3. ShiftedHarmonicDilation.lean
- Exact prefix conditioned dilation, retaining floor(T/p).
- MAIN shiftedHarmonic_dilation_bound: the translated-window conditioned
  dilation error is <=2*p/mass. BOTH endpoint losses are included.
- shiftedWindowDilationBudget includes the finite collection of label
  defects, one per window coordinate.
- shifted_harmonic_window_dilation_error, shiftedWindowDilationBudget_zero,
  shifted_harmonic_window_dilation_le. The budget vanishes under the same
  natural mean-zero fixed-multiplier defect hypothesis as the prefix theorem.

4. TranslatedCyclicBoundary.lean
- translatedNaturalGapDiscrepancy uses the ACTUAL condition q|(S+n).
- translatedCycleLabel(S,M,L,x)=L(S+val(x-S)). Rotation is essential: it
  preserves that actual residue condition when q divides the cycle length M.
- Exact rotated cyclic-prefix identity, including the residue calculation.
- translated_natural_cyclic_round_up_error is independent of the origin S.
  No false assumption q|S is used, and no mismatched conditioning survives.

5. ShiftedHarmonicPrimeTransfer.lean
- translated_decreasing_weight_prime_gap_transfer extends the common-scale
  finite mixture theorem to arbitrary interval origins, using the rotated
  cycle labels. The same selected scale works across the WHOLE mixture.
- MAIN shifted_harmonic_prime_gap_transfer: for any finite alphabet and
  epsilon, a common finite horizon works on all interval sequences of
  mass->infinity, uniformly in endpoint-dependent labels and bounded pair
  observables. This estimates conditioned-minus-unconditioned discrepancy.

6. ShiftedHarmonicWordLimit.lean
- shiftedEmpirical is a genuine probability measure on the word space.
- Exact integral representation and common weakly convergent subsequence.
- MAIN shifted_word_limit_measurePreserving: every such limiting word law
  is stationary, proved as equality of actual measures.
- MAIN shifted_word_limit_dilation_cylinder: simultaneous cylinder dilation
  domination for all fixed positive multipliers and finite windows.

7. ShiftedStableSkewZero.lean
- shifted_pair_dilation_error and the common-scale
  shifted_approximate_harmonic_prime_transfer connect adjacent correlations
  and prime gaps on the SAME translated harmonic window.
- shifted_word_limit_adjacent_skew_zero combines the new window transfer
  with the already proved stationary prime-skew spectral theorem.
- MAIN stable_finite_labels_shifted_harmonic_skew_zero: every fixed finite
  label sequence stable in natural mean under each positive multiplier has
  zero harmonic skew mean on EVERY sequence of intervals with mass->infinity.
  No lower-endpoint rate or minimum rate of mass divergence is imposed.

8. GrowingWindowLargestPrimeHalf.lean
- shiftedHarmonicMean_eventual_upper_of_prefix_upper handles nonnegative
  errors bounded by 2, preserving a nonzero limiting upper bound.
- localFactorSign_shifted_harmonic_approximation transfers the previously
  proved natural mean approximation by FIXED finite labels to these windows.
- MAIN factorSign_growing_harmonic_window_zero:
    mass(A_j,M_j)->infinity implies shiftedMean(A_j,M_j,factorSign)->0.
- MAIN factorSign_uniform_long_harmonic_windows:
    for every epsilon>0, exists R>0, for ALL A,M,
      mass(A,M)>=R implies |shiftedMean(A,M,factorSign)|<epsilon.
  This genuine uniformity follows by a contradiction/choice of bad windows
  with masses >=j+1, not by subtracting two nonuniform prefix limits.
- MAIN largest_prime_rises_growing_harmonic_half gives actual harmonic rise
  proportion tending to 1/2 along every interval sequence of growing mass.

9. GrowingWindowLogEndpoints.lean
- Exact harmonic-number difference for the interval mass.
- shiftedHarmonicMass_log_ratio_bound:
    |mass(A,M)-log((A+M+2)/(A+1))|<=1.
- MAIN largest_prime_rises_growing_ratio_half: if
    (A_j+M_j+2)/(A_j+1)->infinity,
  the ACTUAL harmonic rise proportion on [A_j+1,A_j+M_j+1] tends to 1/2.

SCOPE AND REMAINING GAP:
This improves the previously checked prefix harmonic half theorem to
uniformity over all intervals of growing logarithmic length. The extension
uses the actual prime comparison, not an auxiliary model. However fixed-ratio
windows such as [N,2N] have bounded harmonic mass and are NOT covered. Uniform
normalized cancellation on long logarithmic windows does not imply natural
cancellation. The already checked fixed stable countermodels also fall under
this new generic finite-label theorem, while their natural biases persist;
therefore no generic natural upgrade is claimed. The two unnormalized signed
interior windows at multipliers 2 and 3 remain unproved. No winner-current
l1 tail tightness or sharp signed collision estimate was obtained.

Removed CheckShiftedWindow.lean. No unfinished scaffold remains from this
batch. Spec.lean is unchanged with its original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof of the original conjecture is ready to submit.

## Continuation: multiplicatively syndetic near-half natural endpoints

Completed and saved .olean files for two modules, 265 lines total:
- LogWindowPrefixMeans.lean (125 lines)
- SyndeticNaturalHalf.lean (140 lines)

The pending sum_congr elaboration issue in the former was repaired. All
compilation checks pass, and largest_prime_rises_syndetic_near_half depends
only on propext, Classical.choice, and Quot.sound.

PrefixMean lemmas:
- Unit bound, exact multiplication/sum identity, and step identity.
- Exact shifted-harmonic telescoping identity for f versus prefixMean(n+1,f).
- Uniform error <=6/mass between shifted means of f and its ordinary
  prefix profile g(n)=prefixMean(n,f).
- Transfer of zero means to the prefix profile along growing-mass windows.
- Local window monotonicity and finite_prefix_gap_side: if g stays outside
  [-epsilon,epsilon] and its jumps are <epsilon, its sign cannot change.

New theorem largest_prime_rises_syndetic_near_half:
  For every epsilon>0, there exist fixed natural C>=2 and T>=1 such that
  for every N>=T, there is M in [N,C*N] with
    |risingCount(M)/M - 1/2| < epsilon.

Proof uses the UNIFORM long-window theorem directly, rather than selecting
bad endpoint sequences. Prefix-window cancellation follows from the 6/mass
error. Choose C so log(C) is larger than the required window mass. The
ordinary prefix profile has successive jumps tending to zero. If a whole
interval [N,C*N] avoided the epsilon-neighborhood, the finite no-crossing
lemma would put it on one side; local weighted monotonicity then contradicts
smallness of its harmonic mean.

SCOPE: This strictly strengthens the earlier arbitrary-late cluster-point
result. It still does NOT imply natural-density convergence: a bounded
oscillation on the log-endpoint scale can have syndetically recurring zeros.
No fixed-ratio signed window limit, current tail tightness, or sharp energy
estimate has been obtained. The uniform long-window statement cannot be
silently upgraded to unnormalized cancellation on [N,2N].

Reaudited comparable-prime/double-prime transfer before this batch. Making
p and q comparable relates the shorter endpoints N/p and N/q to each other,
not either to the original endpoint N. Varying source endpoints according
to the selected entropy scale changes the sampling law. No valid same-target
natural recurrence was found.

Spec.lean remains unchanged with original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof is ready to submit.

Follow-up exact-max / spectral review after the syndetic theorem:
Re-read FixedMaxMultiplicativeSymmetry, NestedMultiplicativeSkew, the fixed
stable/radical countermodels, and StationaryPrimeSkew/HarmonicPrimeLabelSpectrum.
The actual initial-segment prime condition is stronger than generic nested
multiplicative indicators, but no uniform moving-cutoff estimate follows from
the fixed-label theorem. A possible Mellin-weighted extension of the harmonic
spectral argument would at most rule out specified log-frequency obstructions;
no proof was obtained that it controls continuous log-scale fluctuations, or
that it yields the unnormalized fixed-ratio windows. No such extension is
claimed as a theorem. Natural transfer still has endpoint N/p; no valid
same-target recurrence was identified. The original conjecture remains open
within this development.

## NEW arithmetic continuation: polynomially growing separated Vaughan cutoffs

Completed three modules with saved .olean files:
- GrowingVaughanShortTerms.lean
- PowerSeparatedVaughan.lean
- PowerSeparatedPrimeKernel.lean
All main theorem axiom checks use only propext, Classical.choice, Quot.sound.

1. GrowingVaughanShortTerms:
- truncated_moebius_mangoldt_abs_le_log: |(mu_{<=U}*Lambda_{<=V})(q)|<=log q.
  This follows from positivity of Lambda, |mu|<=1, and zeta*Lambda=log.
- Sum of absolute short convolution coefficients <=UV log(UV).
- shortZetaPrimeKernel_log_bound keeps the inverse logarithm:
    |shortZeta(T,f)| <= 6*#P*#S*sum_{u<=T}|f(u)|/log(C+1).
  This improves the older bound with a constant inverse-log majorant.
- If U,V>=1 and UV<=C, the two signed short terms together satisfy
    |mangoldtKernel-longVaughanKernel| <=12*#P*#S*UV.
  There is NO logarithmic loss: log(UV)/log(C+1)<=1.
- For S=[1,floor(N/(C+1))], normalized error is at most
    12*#P*UV/(C+1).
- Growing-cutoff remainder theorem under vanishing of this explicit budget.
  Moduli need only be positive; no primality estimate is used for short terms.

2. PowerSeparatedVaughan:
- If #P<=N^a, C>=N^b, U<=N^u, V<=N^v, the cardinality budget is
    <=N^{-(b-a-u-v)}.
- Finite normalized short error <=12*N^{-(b-a-u-v)}.
- Define vaughanPowerCutoff(gamma,N)=floor(N^gamma); its divergence is checked.
- If a>=0, gamma>0, a+2*gamma<b, BOTH cutoffs can be this explicit power,
  yielding a checked o(N) difference between Mangoldt and long kernels.
- Positive moduli bounded by N^a satisfy the required cardinality bound.

3. PowerSeparatedPrimeKernel:
- The actual signed PRIME kernel satisfies the finite normalized bound
    |primeKernel-longVaughanKernel|/N
      <=primePowerKernelTail(C)+12*N^{-(b-a-u-v)}.
  Hypotheses retain the real upper-half uniqueness condition N+1<=B^2,
  primes p>B, B<=C, and EVERY original cofactor endpoint b*F(b)<=N.
- cutoffPrimeSkew_polynomial_vaughan_remainder_tendsto gives o(N) difference
  for BOTH cutoffs floor(N^gamma), not merely a nonquantitative diagonal.

This is a genuine improvement over the prior fixed-U,V short-term theorem.
Power separation D/C allows growing divisor ranges, and keeping the inverse
logarithm avoids an unnecessary log loss. It does NOT remove the long term.
The surviving variables with mu and Lambda coefficients can both exceed a
fixed positive power of N. Existing unweighted inverse-rectangle estimates
cannot simply be applied to these weighted variables. Character/Cauchy
bounds were rechecked and still lose a power in the upper-half modulus range;
no signed bilinear dispersion estimate was obtained. Taking UV beyond the
entire endpoint would kill the long term but is incompatible with the proved
short-term budget in the needed range.

Removed CheckGrowingVaughan.lean. Spec.lean remains unchanged with original
sorry. No complete proof/disproof is available for submission.

## Growing Vaughan long term: absolute reciprocal mass remains positive

Completed GrowingVaughanAbsoluteMass.lean (saved .olean). Main axioms are
exactly propext, Classical.choice, Quot.sound. This is a checked obstruction
to an absolute-value shortcut, NOT a disproof of Erdős 371.

Definitions:
  vaughanAbsoluteReciprocalWindow(U,V,C,N)
    = sum_{C<q<=N} |vaughanLongFunction(U,V,q)/log(q)|/q.

Main growing_vaughan_absolute_mass_positive:
  Eventually in B, SIMULTANEOUSLY for all 1<=U,V<=B,
    vaughanAbsoluteReciprocalWindow(U,V,B^2,B^4) >= 1/64.

Proof retains distinct unordered prime pairs in (B,B^2]. The elementary
weighted-prime harmonic estimate gives reciprocal band mass >=1/4. Its
reciprocal-square diagonal tends to zero. The exact pair identity gives
unordered distinct-product mass >=1/64. Prime factorization makes the map
(r,s)->r*s injective for r<s. All such products lie in (B^2,B^4], and the
previous exact semiprime identity gives normalized long coefficient -1.

Corollary polynomial_vaughan_absolute_mass_not_zero:
  For every 0<gamma<=1/4, with BOTH cutoffs floor((B^4)^gamma), the above
  absolute reciprocal window mass does NOT tend to zero. These truncations
  grow polynomially, so this is stronger than the older fixed-cutoff
  nonsummability obstruction.

Revisited signed loser collisions, weighted energy, and bilinear row
identities. The exact signed collision formula still needs opposite-sign
fraction tending to half; the checked positive local-minimum contribution
alone is insufficient. No valid contraction or signed long-kernel estimate
was obtained. The new absolute-mass lower bound must not be mistaken for a
lower bound on the signed arithmetic kernel: the latter can still cancel.

Removed temporary CheckLongMass.lean. Spec.lean remains unchanged and still
contains the original sorry. No proof or disproof is ready to submit.

## NEW signed arithmetic continuation: removing the long core-product head

Completed VaughanProductHead.lean with saved .olean; main axiom checks use
only propext, Classical.choice, Quot.sound.

Define vaughanCore(U,V)=mu_{>U}*Lambda_{>V}. Its pointwise absolute value is
at most log(q), by |mu|<=1, Lambda>=0, and zeta*Lambda=log.

General logarithmic_divisor_head_bound:
  If |f(d)|<=log d, 1<=T<=C, then the signed kernel for f_{<=T}*zeta is
  bounded by 6*#P*#S*T, uniformly in all cofactor endpoints. This uses
  cancellation in the free complementary variable, retaining the coefficient
  f(d) outside that progression. The log(T)/log(C+1) ratio is <=1.

Define vaughanProductTailKernel by replacing vaughanCore with
  vaughanCore - (vaughanCore)_{<=T}
before convolution with zeta. The identity
  longVaughanKernel - productTailKernel = shortZeta(T,vaughanCore)
is exact.

Main vaughanLong_product_head_bound:
  |longVaughanKernel-productTailKernel|<=6*#P*#S*T,
  UNIFORMLY in the original truncation parameters U,V.
For S=[1,floor(N/(C+1))], normalized bound is 6*#P*T/(C+1).

Main vaughanLong_polynomial_product_head_zero:
  If #P<=N^a, C>=N^b, a>=0, and 0<tau<b-a, the core-product cutoff can be
  T=floor(N^tau), with power-saving error <=6*N^{-(b-a-tau)}.
  U,V may be arbitrary moving parameters. This cancels a portion INSIDE
  the long term, potentially beyond the already removed separate short heads.

Main cutoffPrimeSkew_polynomial_product_tail_remainder_tendsto composes this
with the previous prime-power replacement and polynomial Vaughan reduction.
The actual signed prime kernel and the resulting large-core-product kernel
have difference o(N), under the explicit upper-half and separated-range
hypotheses. It does NOT assert that either kernel has mean zero.

Also re-read the full high-endpoint mixed-complement rectangle results.
Those already reach high-factor endpoint N; the missing low-factor component
is larger than the selected subpower window. Letting the fixed high-threshold
exponent vary is not a justified way to make that low-factor restriction
exhaustive. No parameter diagonal was substituted for that missing estimate.

The remaining signed core-product kernel still has uncontrolled Mobius
weights. No new dispersion estimate, energy contraction, or natural density
convergence was proved. Removed CheckCriticalHead.lean. Spec.lean remains
unchanged with its original sorry; no full proof/disproof can be submitted.

## Exact smooth-part annihilation inside the long Vaughan coefficient

Completed Submission/VaughanSmoothAnnihilation.lean, with saved .olean.
The main theorem's axiom check is exactly propext, Classical.choice,
Quot.sound. No squarefreeness assumption is used.

- coprime_of_small_rough: a positive d<=T is coprime to r if every prime
  divisor of r exceeds T.
- small_divisor_of_mul_rough: under that roughness assumption, a divisor
  d<=T of m*r must divide m.
- truncated_moebius_zeta_zero_of_divisors: if 1<m<=T, m|n, and all positive
  divisors d<=T of n divide m, then (mu_{<=T}*zeta)(n)=0. This groups the
  ENTIRE small divisor set as the divisors of m and uses mu*zeta=delta.
- vaughanLongFunction_moebius_zeta: exact identity
    Long(U,V) = (delta-mu_{<=U}*zeta)*Lambda_{>V}.
- MAIN vaughanLongFunction_small_times_rough:
    1<m<=T and every prime divisor of r>T => Long(T,T,m*r)=0.
  For every nonzero long Mangoldt factor v, coprimality splits the prime
  power divisor between m and r. Since v>T>=m, it must divide r. The
  complementary factor contains m, and its truncated Moebius sum is zero.
- MAIN vaughanLongFunction_smoothPart_zero:
    1<smoothPrimePart(T,q)<=T => Long(T,T,q)=0.
  This applies the generic identity to the canonical smooth/rough product.

This is genuine signed divisor grouping, not an absolute bound or a
pointwise-smallness claim. Rough composites remain, as do numbers whose
T-smooth part exceeds T. No bound making the surviving signed kernel o(N)
was obtained. The earlier absolute-mass obstruction still applies.

Revisited full marginal prime-factor laws versus low-budget joint inclusion
identities. The finite fixed-marginal and stationary obstructions are still
not actual Poisson-Dirichlet models, and no reconstruction theorem or valid
PD perturbation was proved. Absence of further factors cannot be assumed to
be a low-budget inclusion observable. Also revisited the natural endpoint
transfer and graph-current circulation routes; no new estimate closes their
previously recorded gaps. In particular, no generic implication from uniform
long harmonic windows to fixed-ratio window cancellation was asserted.

Spec.lean remains unchanged with the original sorry and checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No proof or disproof of the conjecture has been obtained or submitted.

## Exact rough-factor dependence of the long Vaughan coefficient

Completed Submission/VaughanRoughGrouping.lean with saved .olean. All three
main printed axiom checks use exactly propext, Classical.choice, Quot.sound.
No admissions or unsafe evaluation.

For positive m,r and all prime divisors of r greater than U:
- truncated_convolution_mul_rough rewrites the truncated divisor convolution
  at m*r as a sum over d<=U dividing m, with complementary argument (m/d)*r.
- truncated_zeta_mul_rough shows (f_{<=U}*zeta)(m*r)=(f_{<=U}*zeta)(m).
- truncated_log_mul_rough shows
    (f_{<=U}*log)(m*r)=(f_{<=U}*log)(m)+(f_{<=U}*zeta)(m)*log r.
For r rough above max(U,V), double_truncated_zeta_mul_rough similarly
removes r from (f_{<=U}*g_{<=V}*zeta)(m*r).
These identities do NOT require that m be small, smooth, or coprime to r.

MAIN vaughanLongFunction_mul_rough, with A_U=mu_{<=U}*zeta:
  Long(U,V,m*r)=Long(U,V,m)+Lambda_{>V}(m*r)-Lambda_{>V}(m)
                 -A_U(m)*log r.
This follows by evaluating the exact Vaughan identity at m*r and m and
retaining every term. It is not an asymptotic estimate.

MAIN vaughanLongFunction_smooth_rough_formula applies this to canonical
m=smoothPrimePart(max(U,V),q), r=roughPrimePart(max(U,V),q), q>0.

For m,r>1 and coprime, vonMangoldt_mul_coprime_zero proves Lambda(m*r)=0.
Then vaughanLongFunction_mixed_rough removes that direct Mangoldt term.
MAIN vaughanLongFunction_mixed_rough_normalized:
  Long(U,V,m*r)/log(m*r) = -A_U(m)
    +[Long(U,V,m)-Lambda_{>V}(m)+A_U(m)*log m]/log(m*r).
Thus the dependence on r of a genuine mixed coefficient is logarithm-affine
before normalization, and constant plus inverse-log afterward. Its roughness
restriction remains; it was NOT dropped from any signed progression sum.

For m=1 the direct Mangoldt term survives. In particular the formula does
not turn the prime-counting problem into an unweighted estimate. No bound
for the remaining signed rough/cofactor contribution has been proved.
Reconsidered inverse-residue spectral bounds and the full max-multiplicative
law; no valid same-target natural transfer, spectral contraction, or uniform
weighted inverse-product estimate was obtained. Local averaging results
for individual multiplicative indicators were not assumed to imply the
needed adjacent-correlation symmetry.

Removed CheckRoughGrouping.lean. Spec.lean is still unchanged with its
original sorry and checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No full proof/disproof is ready or submitted.

## Fixed-ratio window and current-energy rate audit

Re-read PrimeCurrentL2Convergence, PrimeCurrentAbsoluteBudget,
UniformPrimeCurrentHead, MovingPrimeCurrentHead, InteriorWindowCriterion,
PrimeWinnerWeightedEnergy, PrimeWinnerSubpowerEnergy, PrimeWinnerEnergyLogSavings,
and PrimeWeightedEnergyFromSubpower. No new closing estimate was obtained.

The full raw-current l2 convergence is a dominated-convergence result with
majorant C*p^(-3/2) for squared errors. It does not supply the rate needed
after Cauchy--Schwarz over a positive-power-sized prime head. The uniform
l1 head estimate is a smooth reciprocal tail; its existing vanishing regime
is subpower, not an almost-full positive-power head. The unconditional
energy savings are arbitrary logarithmic savings at quadratic scale, not
the near-linear subpower-loss energy hypothesis in the sufficient criterion.
These quantifier/rate gaps were not bypassed by selecting moving parameters.

Also reconsidered signed-flow cycle decompositions and ordered prime-label
weights. Equality of winner/loser divergence does not eliminate signed
circulations, and no energy contraction was proved. Local averaging of a
single smooth indicator was not used as an unproved symmetry theorem for
its values in the two opposite cofactor progressions.

No new Lean helper was needed for this audit. Spec.lean remains unchanged
and unresolved with its original sorry. No proof or disproof was submitted.

## Per-prime signed-count pairing investigation

Revisited whether a uniform bound on individual unweighted winner-group
imbalances could imply the already checked subpower-loss energy criterion.
A bound |J_p(N)|<=C_epsilon*p^epsilon would suffice but was not proved;
a more natural square-root-cofactor bound with subpower losses would also
suffice. Neither was inferred from fixed-prime S-unit finiteness.

The earlier Pell audit was read before proceeding. Pell doubling still
need not reverse the comparison sign; its p=7 failure was not overlooked.
No new arithmetic involution or signed S-unit pairing was obtained.

EXACT-INTEGER DEVELOPMENT DIAGNOSTIC ONLY, NOT A LEAN CERTIFICATE:
/tmp/prime_group_diagnostic.cpp and /tmp/prime_group_first.cpp sieve largest
prime factors through 20,000,000 and accumulate signed winner groups, to
test the specific tentative boundary-divisor bound |J_p(N)|<=tau(p^2-1).
The diagnostic gives p=173, N=620032, J=33, tau(p^2-1)=32. Thus that
simple candidate should not be used. Further diagnostic examples include
p=563, N=17009920, |J|=67 and tau=32. No asymptotic bound is inferred from
these finite tests, and no numerical search for a counterexample to the
original conjecture was made. The diagnostic outputs have not been promoted
to Lean theorems. No new Lean helper was added in this round.

Spec.lean remains unchanged with its original sorry; no proof or disproof
has been obtained or submitted.

## NEW unconditional consequence: positive lower density of near-half endpoints

Completed Submission/PositiveDensityNearHalfEndpoints.lean (saved .olean).
Both main axiom checks use exactly propext, Classical.choice, Quot.sound.
No admissions or unsafe evaluation.

- rising_proportion_endpoint_bound:
    |risingCount(K)/K-risingCount(M)/M| <= 2*(K-M)/K, 0<M<=K.
- rising_proportion_short_interval:
    If the proportion at M is within epsilon/2 of half, L>4/epsilon,
    and M<=K<=M+floor(M/L), then the proportion at K is within epsilon.
- nearHalfEndpointCount(epsilon,X) counts those GOOD ENDPOINTS K<X.
- MAIN nearHalfEndpointCount_eventually_positive_proportion:
    For every epsilon>0, there exists delta>0 such that eventually X,
      nearHalfEndpointCount(epsilon,X)/X >= delta.
  Choose C,T from the existing syndetic near-half theorem at epsilon/2.
  With D=4*C and Q=floor(X/D), select M in [Q,C*Q]. The entire interval
  [M,M+floor(M/L)] is good and lies below X. Its size gives the explicit
  lower bound delta=1/(2*D*L)=1/(8*C*L), once X>=D*T.
- nearHalfEndpoint_partialDensity identifies this count with the actual
  Set.partialDensity of the endpoint set.
- MAIN near_half_endpoints_positive_lowerDensity:
    0 < {M : |risingCount(M)/M-1/2| < epsilon}.lowerDensity.

The target of this result is a set of ENDPOINTS, not the original set of
rising integers. The positive lower bound can depend on epsilon. Nothing
here proves that the lower density tends to one, that all endpoints become
good, or that the original conjecture holds. This is a rigorous strengthening
of the prior subsequential and multiplicatively-syndetic consequences only.

Further reflection/ordered-multiplicative-group investigations did not
provide a same-prefix involution or a natural-density inverse theorem.
In particular, the prime-product reflection can change the losing prime and
moves the original endpoint; these defects were not suppressed.

Removed CheckGoodEndpoints.lean. Spec.lean is unchanged with the original
sorry and checksum 34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof/disproof has been obtained or submitted.

## Two distinct small-prime divisors: affine-offset transfer audit

Investigated dividing n and n+1 by different small prime divisors p,q,
instead of the common multiplier used in the existing prime-gap transfer.
The exact CRT quotients retain affine offsets. Swapping p,q does not simply
reverse the pair of label arguments, even at a common natural endpoint.
For p=2,q=3, n=6k+2 yields quotients (3k+1,2k+1); the swapped condition
n=6k+3 yields (2k+1,3k+2). Their sum of antisymmetric pair tests is not
identically zero: the remaining shift between 3k+1 and 3k+2 cannot be dropped.

Concentration of small-prime divisor counts can justify certain weighted
averages but does not establish the missing affine-correlation reflection.
Re-read FixedStableBias and StableLabelPrimeTransfer to ensure fixed-prime
stability was not incorrectly promoted to that reflection. No full-max-law
inverse theorem or new natural cancellation estimate was proved. No Lean
helper or modification to Spec.lean resulted from this audit. The target
still contains its original sorry; no proof/disproof is ready to submit.

## Continuation: rough grouping and weighted prime-kernel audit

Re-read VaughanRoughGrouping, VaughanPrimeKernel, ShortDivisorPrimeKernel,
OppositeProgressionWeights, VaughanProductHead, PowerSeparatedPrimeKernel,
SignedInverseRectangles, InverseRectangleSmoothing, and InteriorWindowCriterion.
No new signed arithmetic estimate was obtained.

The small-smooth-part annihilation and logarithm-affine rough-factor formula
cannot remove the smooth-part-one contribution. In that case the direct
Mangoldt term survives. For rough composite arguments the long coefficient
contains the corresponding negative logarithmic term; replacing this by an
unrestricted rough progression sum would reintroduce the original prime
kernel, rather than prove its cancellation. The roughness restriction was
not discarded.

Also reviewed the feasibility of a weighted bilinear/dispersion estimate for
the opposite progressions p | b*q +/- 1 in the power-separated upper-half
range. The existing unweighted inverse-rectangle estimates and monotone
progression-weight bounds do not bound the surviving weighted long term.
No applicable uniform prime-progression estimate, weighted spectral bound,
or same-endpoint contraction was established. No such estimate was added as
an assumption to a purported unconditional proof.

Spec.lean remains unchanged with its original sorry. No proof or disproof
of the original conjecture is available or submitted.

## NEW: near-linear absolute prime-current tails on fixed-ratio windows

Completed Submission/NearLinearPrimeCurrentWindows.lean and saved its .olean.
All six printed final axiom checks use exactly propext, Classical.choice,
Quot.sound. It has no admissions or unsafe evaluation. Temporary check files
were removed.

The checked finite theorem primeWinnerHarmonicWindow_high_bound states:
  for 2<=L<=U and any finite P all of whose labels exceed B,
  sum_{p in P} |rawWinner(p,U)-rawWinner(p,L)|
    <= card(bothAboveSet(B,U))/L + 2/(U-1) + 2/(L-1).
The denominators U-1 and L-1 here are real subtractions.

Proof components:
- primeHarmonicFluxError_finset_bound restricts the existing full l1
  divergence error bound to any finite label set.
- primeHarmonicWindow_flux_bound subtracts the errors at the two endpoints;
  the infinite divergence cancels exactly.
- primeLoserHarmonicWindow_high_bound bounds the absolute losing-current
  vector by the simultaneous-high count divided by the lower endpoint.
- The winner-window bound combines these without discarding signed flux.

NEW asymptotic statements:
- bothAbove_nearlinear_ratio_zero:
    U(N)->infinity and, for every u>0, eventually U(N)^(1-u)<=B(N)
    imply card(bothAboveSet(B(N),U(N)))/U(N)->0.
  This uses the previously checked uniform quadratic two-prime sieve bound.
- primeWinnerHarmonicWindow_nearlinear_zero:
    in addition L(N)->infinity, L<=U<=R*L for fixed R, and all labels in
    P(N) exceed B(N), the full sum of absolute winner-window currents ->0.
- nearlinear_power_bounds_of_log_ratio obtains the power hypotheses from
    log(B(N))/log(U(N))->1, with eventual B(N)>0.
- primeHarmonicWindowL1Above is the sum over Ioc B (U+1).
  rawPrimeWinnerHarmonic_zero_above_endpoint and
  primeHarmonicWindowL1Above_eq_tsum verify that this finite expression equals
  the full infinite high-label tail (under L<=U).
- MAIN primeHarmonicWindowL1Above_log_ratio_zero gives its convergence to zero
  on every bounded-ratio window under the logarithmic-ratio hypothesis.
- MAIN primeWinnerL1Above_nearlinear_zero and
  primeWinnerL1Above_log_ratio_zero give the analogous unweighted absolute
  current-tail convergence, divided by U.

There is NO rate or square-summability condition on how slowly the cutoff
exponent tends to one. This extends the earlier specific near-linear boundary
choices for window cancellation. It is NOT the missing raw-current l1
compactness theorem: every fixed cutoff U^c, c<1, fails this new near-linear
hypothesis, and the fixed-power interior still has no cancellation estimate.
It also does not assert convergence of the entire raw harmonic series for
these more slowly varying cutoffs.

Other investigation in this continuation: revisited whether the full limiting
prime-factor marginal plus all low-total-mass inclusion identities determines
comparison symmetry. The coalescence obstruction and possible continuous
parameterization were examined. No reconstruction theorem and no actual
Poisson-Dirichlet embedding were proved; the finite models were not presented
as arithmetic counterexamples. Reviewed polynomial-multiplier stability and
natural entropy transfer: a prescribed narrow multiplier band still does not
follow from the entropy-decrement scale selection. No inverse theorem or
same-target transfer was assumed.

Spec.lean remains unchanged with its original sorry, checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No proof or disproof of the original conjecture has been obtained or submitted.

## Continuation: inverse estimates and averaged divisor cutoffs

Re-read FullEndpointMixedRectangle, JointFullEndpointCutoffs,
MixedRectangleError, SizeSensitiveInverseRectangles, WeightedPrefixDiagonal,
WeightedComplementSelection, ComplementPrefixArithmetic,
HighComplementAlgebra, LargestPrimeToggle, and the superlinear rough-cutoff
modules. No new closing estimate was obtained.

Improving the unweighted modular-inverse discrepancy alone does not provide
an estimate for the surviving prime/Moebius-weighted fibers. The already
completed full high-factor endpoint remains N; the unrestricted low factor
was not silently included in that theorem.

Investigated averaging the divisor truncation parameter before bounding the
signed tail. The uniform small-modulus prefix bounds permit some such
averaging, but no estimate for the averaged large-divisor remainder was
proved. Smoothing the truncation indicator retains mixed subset products
beyond the sampling length together with their side-colour and Moebius
weights. In particular, averaging does not authorize applying a CRT main
term to those large products. Neither a finite-difference bound making the
full remainder negligible nor a sufficiently strong weighted inverse bound
was established.

Also considered convexifying the arbitrary-external-weight cutoff-selection
statement. No minimax theorem was applied here. The selected-cutoff
quantifiers still do not permit the external weight to depend on that same
selected cutoff, and the fixed short-degree range was not extended to all
complementary indices. The possible polynomial-multiplier inverse theorem
likewise remains unproved.

No new Lean helper was needed for this audit. The previously completed
NearLinearPrimeCurrentWindows module remains checked. Spec.lean remains
unchanged with its original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No proof or disproof of erdos_371 has been obtained or submitted.

## Continuation: prime-insertion and cofactor recurrence review

Re-read PrimeInsertionCheck, PrimeWinnerCongruenceRuns, PrefixBalanceObstruction,
CutoffSeparation, DivisorCycleBound, and the dyadic cancellation checks.
Investigated summing insertion errors rather than bounding each insertion
by the previously refuted two-unit estimate. No aggregate signed bound was
obtained.

Making each multiple of a newly inserted largest prime into a local maximum
balances its new pair of comparisons. The comparisons removed from the old
sequence still form a signed sum. Their dependence on the cofactor and both
neighbor labels was not discarded. In the large-prime range, stripping a
larger prime from a neighbor can leave a small cofactor; this is not the same
as that neighbor being smooth, so an unsigned smooth-number rarity estimate
cannot bound all such removed comparisons. The existing congruence-run
formulas allow one-sided local contributions and do not establish the
required cancellation after summing over primes.

Also reconsidered a universal skew estimate for polynomially
multiplier-invariant finite labels. The actual quantized max-prime labels
have this stronger invariance, but no inverse theorem or signed graph
estimate was proved. Neither the fixed-stable models nor the chirp exclusion
settles that question. No claim of such a theorem is used in Spec.lean.

No new Lean theorem or change to Spec.lean resulted from this round. The
conjecture remains unresolved with its original sorry and checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof has been submitted.

## Continuation: componentwise entropy and L1 harmonic-prefix prime-gap control

New checked modules (all main axiom checks show only propext, Classical.choice,
Quot.sound):

- ComponentwiseMixturePrimeTransfer.lean: average the separate component
  block entropies and mutual informations. One common finite horizon, chosen
  before the number of components, gives an average-SQUARE discrepancy bound.
  Component observables may be chosen AFTER the common scale. Also L1
  corollary. A prime subset family with #S(H)>=c H/log H is allowed.
- ComponentwiseHarmonicPrefixTransfer.lean: uniform harmonic-prefix mixture
  of ABSOLUTE naturalGapDiscrepancy averages, using rounded cycles. Absolute
  value is inside the mixture. This is stronger than the old scalar transfer;
  it still does not identify N/p with N.
- PrefixEnergyIdentity.lean: exact finite identity
    2 sum_{n<N} (f(n)B(n)-B(n)^2)/(n+1)
       =B(N)^2-sum_{n<N}(B(n+1)-B(n))^2,
  B(n)=prefixMean n f. For |f|<=1, the raw correlation/energy difference
  has absolute value <=5. Hence zero weighted harmonic correlation f B
  implies zero harmonic mean square of B. The premise for factorSign is
  NOT proved or assumed.
- PrimeFourierImaginaryEnergy.lean: imaginary prime Fourier average tends
  to zero in L2 of any fixed finite circle measure with no infinite-order
  atoms. This is stronger than just the signed integral.
- ComponentwiseCyclicSkewEnergy.lean: finite componentwise absolute cyclic
  skew is bounded by odd-shift INDICATOR energies. The bound is independent
  of cycle lengths and component count and allows separate skew tests.
- StationaryOddPrimeEnergy.lean: translate all negative gaps to positive
  coordinates, then identify the stationary word odd-shift energy exactly
  with 4 times the imaginary Fourier energy. Prime energy tends to zero.
- NarrowPrimeBands.lean: floor-linear endpoints, their PNT scaled counts,
  and fixed-relative-width prime bands. Their count lower bound and subset
  relation to halfBlockPrimes are checked. No short-interval PNT is used.
- NarrowPrimeBandEnergy.lean: difference of initial prime Fourier averages
  proves L2 imaginary energy cancellation on those bands. Stationary word
  energy counterpart included.
- CyclicWordBoundary.lean: general fixed-window cyclic/natural boundary
  estimate, and odd indicator energy error <=16 R/N.
- HarmonicPrefixOddEnergy.lean: component energies have the same limit as
  the common stationary harmonic word law, with explicit 16 R/H_N error.
- HarmonicPrefixPrimeSkewL1.lean: finite bound
    2 prefixGapL1 <= card(A)*eta + sum_b prefixOddEnergy(b)/eta +4R/H_N.
  MAIN harmonicPrefixPrimeSkewL1_narrow_eventually: given a common harmonic
  subsequential word limit with its proved stationarity and dilation bounds,
  every sufficiently large FIXED prime-band scale has eventually small L1
  harmonic-prefix prime-gap skew, uniformly over all bounded skew component
  tests. The large starting scale is chosen using the common word law, before
  the entropy horizon.

Conceptual audit: there is no need to assume that ergodic components inherit
all dilation inequalities. The finite skew bound uses the unconditioned
indicator energy, and the new L2 imaginary-prime theorem controls that energy.
Conditioning on infinitely fine real-valued prefix data was NOT used.
The new component entropy recurrence is proved by averaging exact finite
recurrences; it charges no entropy for the component index.

At this checkpoint, the endpoint reindexing and stable adjacent transfer have
NOT yet been combined to prove log-density-one of good endpoints. That is the
next planned application. Even that stronger almost-all-log-scales result
would NOT settle the original natural-density conjecture. Spec.lean remains
unchanged with its original sorry. No proof/disproof of erdos_371 submitted.

## Continuation completed: logarithmically almost all ordinary endpoints

The application planned in the previous checkpoint is now COMPLETE and
kernel-checked. There are 17 new modules, about 2,050 Lean lines, in this
continuation. This is a stronger partial theorem, NOT the Spec.lean conjecture.

Additional checked modules after that checkpoint:

- HarmonicPrefixFloorReindex.lean: for arbitrary |G|<=1 and fixed p>0,
    |mean_prefixLaw G(k/p)-mean_prefixLaw G(k)| <=(3p+12)/H_(N+1).
  No multiplier stability of G is needed. Quotient-block reciprocal weights
  give the raw bound 3p+8; the difference between the component law and the
  usual harmonic range law is <=2/H at each end.
- HarmonicPrefixStableAdjacent.lean: naturalAdjacentTransferError p N L C
  tends to zero for each fixed positive p and each fixed mean-stable label L.
  The ACTUAL endpoint floor(N/p) is retained. Its absolute harmonic-prefix
  mixture and the absolute average over any fixed finite positive-prime
  family also tend to zero. Generic bounded G(N)->0 implies its absolute
  component-law mean tends to zero.
- ComparablePrefixQuotients.lean: if 0<p<=q and (1-delta)q<=p, then
    |B(N/p)-B(N/q)| <=2 delta+2q/N
  for all N, including small/zero N, with |f|<=1 and B=prefixMean f.
- HarmonicPrefixBiasAnchor.lean: combine comparable-quotient and reindexing
  bounds, then the exact discrepancy decomposition. The finite bound is
    harmonicPrefixBias <= discrepancyL1+primeGapSkewL1+transferErrorL1
                         +2 delta+(5q+12)/H_(N+1).
- StableHarmonicPrefixAbsoluteZero.lean: MAIN generic theorem
    stable_finite_labels_harmonic_prefix_abs_zero.
  Fixed finite mean-stable labels and every bounded skew pair observable
  have vanishing absolute ordinary-prefix bias in the harmonic-prefix law.
  Proof chooses a common subsequential stationary word law FIRST, then a
  sufficiently large narrow-band starting scale, then the uniform finite
  componentwise entropy horizon. All the finitely many remaining errors
  vanish along the same subsequence. No same-endpoint natural transfer is
  assumed, and no ergodic-component dilation hypothesis is assumed.
- LargestPrimeLogAlmostAllEndpoints.lean: instantiate actual local labels,
  then use the already checked fixed-quantization approximation to obtain:

    factorSign_harmonic_prefix_abs_zero
    factorSign_prefix_absolute_harmonic_mean_zero
    factorSign_prefix_square_harmonic_mean_zero
    factorSign_prefix_weighted_harmonic_mean_zero
    largest_prime_rise_proportions_harmonic_absolute_half
    largest_prime_bad_endpoints_harmonic_zero
    largest_prime_near_half_endpoints_harmonic_one

  Precisely, if r(n)=risingCount(n)/n, then
    harmonicMean(N+1, |r(n)-1/2|) ->0,
  and for every epsilon>0,
    harmonicMean(N+1, 1_{|r(n)-1/2|<epsilon}) ->1.
  The harmonic mean is over endpoint n. This is a harmonic/logarithmic
  density-one theorem about good ENDPOINTS, NOT natural density one of
  those endpoints and NOT convergence of r(n) at every endpoint.

The originally contemplated prefix-weighted correlation f(n)B(n) is now
proved zero in harmonic mean as a corollary of the stronger absolute-prefix
result. Thus the earlier checkpoint's warning that its premise was not yet
proved has been superseded for the actual factorSign. The finite energy
identity remains a separate useful analytic lemma.

All main axiom checks in the final application show only propext,
Classical.choice, Quot.sound. All new modules have saved oleans. Temporary
CheckNarrowEnergy and CheckPrefixReindex files were removed. No new scaffold
or failed compilation remains. Only harmless linter warnings remain.

Remaining gap: harmonic density one of near-half endpoints allows sparse
infinite bad endpoints. The existing fixed-stable biased models are not
contradicted by this new theorem, and no Tauberian implication excluding
such exceptional endpoints is proved. Full raw-current l1 tightness,
fixed-ratio interior-window cancellation, and the other original sufficient
estimates remain missing. The new theorem alone does not settle them.

Submission/Spec.lean remains unchanged, with the original sorry and SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof of erdos_371 has been obtained or submitted.

## Final continuation audit: no complete settlement

Rechecked the unchanged conjecture, the fixed-ratio interior-window criterion,
the fixed max-multiplicative symmetry theorem, the natural prime-gap transfer,
and the weighted long Vaughan remainder. No new closing estimate was obtained.

The moving-window absolute-prefix extension described at the preceding
checkpoint remains a proposed argument, not a checked theorem. Even if proved,
it would allow isolated bad intervals of fixed multiplicative width and would
not imply the ordinary natural-density conclusion.

The following gaps remain explicit:
- Fixed finite-range max-multiplicative reversal is not uniform over the
  moving prime cutoffs used for the actual comparison.
- Natural adjacent transfer retains floor(N/p); comparable primes do not
  identify this endpoint with N.
- The long Vaughan kernel retains prime/Moebius weights and roughness
  restrictions. Unweighted inverse-rectangle estimates cannot simply be
  applied after discarding these weights.
- No uniform short-interval or weighted dispersion estimate closing these
  gaps has been proved or invoked.

No new theorem is asserted in this continuation. Spec.lean remains unchanged
with its original sorry. There is no complete proof or disproof to submit.

## NEW completed continuation: uniform logarithmic sparsity of bad endpoints

The moving-window absolute-prefix extension is now COMPLETE and kernel-checked.
It is a stronger partial result, not the natural-density conjecture.

New modules:
- ShiftedPrefixEndpointLaw.lean
- ComponentwiseShiftedPrefixTransfer.lean
- ShiftedPrefixOddEnergy.lean
- ShiftedPrefixStableAdjacent.lean
- ShiftedPrefixPrimeSkewL1.lean
- ShiftedPrefixBiasAnchor.lean
- StableShiftedPrefixAbsoluteZero.lean
- LargestPrimeUniformLogGoodEndpoints.lean

The endpoint law samples GLOBAL prefixes at k=A+i+1 with harmonic weights.
It is not the decreasing-prefix law applied to a translated sequence.
Checked bounds include:
  E(1/k) <= 2 / shiftedHarmonicMass(A,M),
  fixed quotient reindexing error <= (6p+24) / mass,
  cyclic odd energy to prefix energy error <= 32R / mass,
  prefix energy to shifted word energy error <= 24 / mass,
  2*skewL1 <= card(X)*eta + sum(odd energies)/eta + 8R/mass,
  prefix absolute bias <= discrepancyL1 + skewL1 + adjacentErrorL1
                          + 2delta + (10q+24)/mass.

The common componentwise entropy horizon is selected independently of A,M;
its rounded cyclic errors are integrated using the reciprocal-endpoint bound.
The common shifted stationary word law supplies the previously proved
narrow-prime-band odd energy cancellation. Every quotient endpoint is kept
until the finite reindexing estimate has accounted for it.

Generic main theorem:
  stable_finite_labels_shifted_prefix_abs_zero
For every fixed finite mean-stable label L and bounded skew pair C, the
absolute ordinary-prefix skew has mean zero along every sequence of harmonic
windows whose harmonic mass tends to infinity.

Actual maxPrimeFac application:
  factorSign_growing_harmonic_prefix_abs_zero
  factorSign_uniform_long_harmonic_prefix_abs
  largest_prime_rise_proportions_growing_harmonic_absolute_half
  largest_prime_bad_endpoints_growing_harmonic_zero
  largest_prime_bad_endpoints_uniform_long_harmonic_zero

The last theorem says: for every epsilon,eta>0 there exists R>0 such that
EVERY harmonic endpoint window of mass >=R has bad-endpoint harmonic
proportion <eta, where bad means |risingCount(N)/N - 1/2| >= epsilon.
Thus good ordinary endpoints have uniform logarithmic density one on long
windows. This is not natural density one of good endpoints and does not
imply convergence at all endpoints. Sparse bad intervals of fixed
multiplicative width remain compatible with this theorem.

All main axiom prints from the clean compilations use only propext,
Classical.choice, Quot.sound. All eight modules have saved oleans. The
CheckShifted scratch file was removed. No failed scaffold remains.

Additional closing-route audit: the proved slowly growing subpower current
head and near-linear current tail still cannot share a cutoff. A proposed
bilinear treatment of the long inverse-prime kernel must retain its thin
inverse-interval condition and outer modulus sum; a bound for a single
exponential sum with a full q-range loses too much relative to N. No such
weighted thin-region estimate or polynomial-multiplier graph expansion has
been proved. These are research possibilities, not invoked theorems.

Spec.lean is unchanged, still containing the original sorry, with checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof of the original conjecture is available.

## Further continuation: weighted thin-kernel and energy audit

No complete settlement and no new theorem in this pass.

Revisited the surviving Vaughan product tail, smooth-part annihilation,
prime-cofactor descent/preimages, and the exact winner-energy increments.
The following proposed shortcuts remain unjustified:

1. A full-range inverse-prime exponential estimate loses the density of the
   thin inverse-residue interval. A direct second-moment/character treatment
   on prime moduli of size P has scale P*sqrt(N) after summing moduli, rather
   than o(N), in the upper-half range P>sqrt(N). No weighted thin-region
   dispersion bound improving this has been established.

2. The cofactor descent reverses signs and contracts the index, but its
   inverse multiplicities still depend on a prime linear form and a
   simultaneous smoothness condition. There is no justified replacement of
   its pushforward by a smooth harmonic kernel acting on prefix biases.

3. The exact formula E(N)=N+2*crossSum(N) does not prove E(N)<=N. The
   earlier finite diagnostics do not supply the missing signed inequality.
   Local-minimum deletion is already known not to contract weighted energy
   pointwise.

4. Full small-prime smooth truncation in a Vaughan-type decomposition does
   not by itself make the long kernel absolutely negligible. Summing over
   the complementary cofactor introduces a logarithmic factor, so sparsity
   of rough integers alone is insufficient. No such absolute-tail assertion
   has been added.

The new uniform-logarithmic good-endpoint theorem from the preceding
continuation remains valid, but it does not rule out sparse fixed-ratio
exceptional windows. Spec.lean is untouched and still has its original
sorry. There is no complete proof/disproof to submit.

## Further continuation: antisymmetric prime-label graph moments

Examined a higher-moment route for the matrix of oriented consecutive
largest-prime-label edge counts. No spectral bound or new theorem obtained.

The checked divisor_cycle_product_bound applies to consistently directed
cycles with p_i dividing n_i and p_(i+1) dividing n_i+1. Higher even moments
of the antisymmetric matrix also contain mixed-orientation closed walks.
Their signed contributions are not bounded by the directed-cycle theorem.
An unsigned walk count or exclusion of short directed cycles cannot be
substituted for the needed signed spectral estimate.

The large-prime unordered-edge injectivity theorem remains useful but does
not control these higher signed moments. No assertion of graph expansion,
small antisymmetric operator norm, or reversal symmetry has been added.

Spec.lean remains unchanged with its original sorry. There is still no
complete proof or disproof to submit.

## Further continuation: determinant-one reflection and actual mixed cycles

The determinant-one reflection was rechecked. For an adjacent prime-divisor
pair, reversing orientation while preserving the same primes uses the CRT
reflection n -> p*q-n-1. It does not preserve a fixed prefix in the difficult
large-product range. Retaining a composite divisor mark preserves a bijection
on marked objects, not a count-controlled map on the original indices. No
new matching or multiplicity estimate was obtained.

New kernel-checked module (101 lines):
  Submission/MixedPrimeCycleObstruction.lean
Saved olean is present. All three main axiom checks show only propext,
Classical.choice, Quot.sound. There are no remaining compile errors.

This supplies explicit actual largest-prime-factor cycles showing why the
directed divisor-cycle product bound cannot be extended to mixed orientations:

1. Triangle: forward indices 172,173 and backward index 86, with labels
   43 -> 173 -> 29 -> 43. Endpoint products are equal, while
   43*173*29 > 3*174^2.

2. Four-cycle: forward indices 906,907,908 and backward index 302,
   with labels 151 -> 907 -> 227 -> 101 -> 151. Again the endpoint
   products agree, and the label product exceeds 4*909^3.

3. Balanced four-cycle (two forward, two backward):
   forward indices 10866,86936, backward indices 28978,14488,
   with labels 1811 -> 10867 -> 28979 -> 14489 -> 1811.
   The endpoint products agree, and the label product is
   8263231589192147 > 4*86937^3 = 2628293978635812.
   This comes from the prime values t,6*t+1,16*t+3,8*t+1 at t=1811.
   It has positive orientation product, so degenerate nonbacktracking
   mixed walks cannot all be discarded as negative moment terms.

Main names:
  mixed_prime_cycle_obstruction
  mixed_prime_four_cycle_obstruction
  balanced_mixed_prime_four_cycle_obstruction

These refute proposed extensions of an AUXILIARY finite estimate, not the
conjecture. No assertion that all spectral or matching approaches fail is
made. No new asymptotic cancellation estimate has been proved.

Spec.lean remains unchanged with its original sorry. There is still no
complete proof or disproof to submit.

## Further continuation: smooth-indicator correlation route

Revisited the neighboring smooth-cutoff criterion and the finite Fourier
formulation. No new cancellation estimate or theorem was obtained.

The exact smoothCutoffSkew_band_kernel retains the rank-two signed divisor
kernel. Reflection symmetry over a complete residue period cannot replace
control of a prefix whose length is far shorter than that period. Likewise,
the real Fourier coefficients arising from even divisibility indicators do
not by themselves estimate the incomplete cross-correlation. No uniform
incomplete-period estimate has been proved or assumed.

The fixed stable-label counterexample was also rechecked: fixed-multiplier
stability alone really does allow biased natural subsequences. The stronger
polynomial-multiplier property of the actual labels still needs a new
arithmetic or inverse argument; excluding a particular chirp does not supply
that argument.

An attempt to fetch https://www.erdosproblems.com/371 again failed with DNS
resolution error. No external result was imported or invoked.

No changes to Spec.lean. Its sorry remains; there is no complete proof or
disproof available to submit.

## New checked reduction: cumulative prime-winner energy suffices

Completed three development modules, with saved oleans:
  AveragedPrimeWinnerEnergy.lean
  AveragedPrimeWinnerSubpower.lean
  CumulativeWinnerCrossIdentity.lean
All main axiom prints contain only propext, Classical.choice, Quot.sound.
No failed scaffold remains; CheckAvg.lean was removed. Spec.lean is unchanged.

Let E(k)=primeWinnerEnergy k and cumulative E(X)=sum_{k=0}^X E(k).
New finite persistence inequality, valid for EVERY real f with |f|<=1:
  |sum_{n<N} f(n)|^3 <= 8 sum_{k<=2N} |sum_{n<k} f(n)|^2.
It uses the floor of half the endpoint absolute sum and retains that entire
short endpoint interval; it does not assume natural convergence.

Applications:
  |risingCount(N)-fallingCount(N)|^3
    <= 8 card(primeWinnerLabels(2N)) * cumulative E(2N).
  |primeWinnerLowSum(B,N)|^3
    <= 8 (B+1) * cumulative E(2N).
For the low-prime inequality, B is FIXED while the nearby endpoints vary.

Checked sufficient criteria for the ORIGINAL conjecture:
1. cumulative E(X) <= C X^2 eventually.
2. More generally, for EVERY eta>0,
     cumulative E(X) <= X^(2+eta) eventually.
The latter uses the existing high-prime tail estimate and the new low-prime
cubic inequality. It only requires a subpower-loss near-linear energy bound
ON AVERAGE over endpoints, not at every endpoint separately.

Main names:
  unit_prefix_cube_le_square_sum
  comparison_cube_le_cumulative_primeWinnerEnergy
  density_of_quadratic_cumulative_primeWinnerEnergy
  primeWinnerLowSum_cube_le_cumulative
  primeWinnerLowSum_power_zero_of_cumulative
  density_of_subpower_cumulative_primeWinnerEnergy

Exact new arithmetic identity:
  cumulative E(X) = X*(X+1)/2 + 2*triangularPrimeWinnerCrossSum(X),
where the cross sum is
  sum_{n<X} (X-n)*factorSign(n)*primeWinnerSum(primeWinner(n),n).
Checked as cumulativePrimeWinnerEnergy_eq_triangular_cross, together with
cumulativePrimeWinnerEnergy_le_iff isolating the one-sided remaining bound.

IMPORTANT: Neither cumulative energy hypothesis has been proved. The signed
triangular cross sum remains unestimated. Endpoint smoothing does not itself
supply cancellation of the prime-pattern terms. These are conditional
reductions, not a proof/disproof of the conjecture. No submission made.

## Cumulative-energy continuation: harmonic-current rate audit

Attempted to derive the new cumulative energy hypothesis from the checked
full harmonic-current l2 convergence and uniform head/tail budgets. No new
arithmetic estimate was obtained.

The per-prime absolute harmonic incidence budget is O(log(p)/p). The existing
l2 convergence uses a square-summable majorant and fixed-coordinate limits;
it does not establish a uniform decay rate of the size needed after undoing
the harmonic weights. The uniform smooth head estimate still controls a fixed
or slowly growing head, not all fixed positive-power prime bands. Averaging
over ordinary endpoints does not itself fill that quantitative gap.

No claim that the averaged energy condition follows from l2 convergence has
been added. The triangular signed cross sum remains unestimated. Spec.lean
is unchanged, and no complete proof or disproof is available to submit.

## Further continuation: summable critical harmonic diagonal and weighted flux tails

TWO NEW kernel-checked development modules, with saved oleans:
  Submission/PrimeLoserHarmonicDiagonal.lean
  Submission/PrimeHarmonicFluxTail.lean
All printed main axiom checks use only propext, Classical.choice, Quot.sound.
No unfinished scaffold, admission, or active compile error remains.

A. PrimeLoserHarmonicDiagonal.lean

Unconditional new summability:
  sum_n primeLoser(n)/n^2 < infinity,
with real casts and totalized division at zero. Main theorem:
  summable_primeLoserHarmonicDiagonal.

The proof uses the existing dyadic two-large-primes sieve. For n in
[2^k,2^(k+1)), split at T_k=(2^(k+1))^(1-u(k)), where
u(k)=(1/8)*(k+1)^(-3/4).
- Above T_k, the term is at most the existing summable exceptional
  reciprocal dyadicTopPrimeReciprocal(threeQuarterBandWidth,n).
- Below T_k, the block sum is at most T_k/2^k, exactly
    2*exp(-(log 2/8)*(k+1)^(1/4)),
  a summable stretched exponential.
A generic summable_exp_neg_rpow_nat lemma is checked using the library's
exponential-versus-power little-o theorem, for any positive a,c.

Also checked:
  primeLoserHarmonicTerm_weighted_square_row:
    sum'_p p*(primeLoserHarmonicTerm(p,n))^2=primeLoser(n)/n^2.
  summable_primeLoserHarmonic_weighted_square_rows.
  primeLoserHarmonicDiagonal_tail_zero.

IMPORTANT: Summability of squared increments is NOT convergence of their
sum. Repeated occurrences of the same loser label still have unestimated
signed cross terms. No Hilbert-space orthogonality was assumed or proved.

B. PrimeHarmonicFluxTail.lean

This complements the previously checked unweighted l1 divergence results
in PrimeHarmonicDivergenceMass/Convergence with CRITICAL PRIME-WEIGHTED
square tails, uniformly over the ordinary endpoint N.
Write D_p(N)=rawPrimeWinnerHarmonic(p,N)-rawPrimeLoserHarmonic(p,N).
For any finite S with p>B for all p in S, and B>0:
  sum_{p in S} D_p(N) <= 1/B,
  sum_{p in S} p*D_p(N)^2 <= 2/B.
The second uses D_p(N)>=0 for p>=2 and p*D_p(N)<=2.
It requires only maxPrimeFac(n)<=n, the one-hot label indicators, and the
reciprocal discrete-derivative bound, not any new prime-pattern estimate.

Passing to coordinate limits gives the same 2/B tail bound for D_p(infinity).
The error vector satisfies
  sum_{p in S} p*(D_p(N)-D_p(infinity))^2 <= 8/B.

Main names:
  harmonic_derivative_prefix_bound_of_cutoff
  finite_primeHarmonic_flux_tail_bound
  primeHarmonic_flux_mul_label_le_two
  finite_primeHarmonic_flux_weighted_square_tail
  finite_primeHarmonic_limit_flux_weighted_square_tail
  finite_primeHarmonic_flux_error_weighted_square_tail

These bounds control ONLY winner-minus-loser, not either current separately.
A common signed circulation can remain. No sufficient signed collision,
cumulative energy, or fixed-ratio harmonic-window estimate has been obtained.

Spec.lean is unchanged and retains its original sorry. There is still no
complete proof or disproof of the conjecture to submit.

## Signed-collision continuation: mixed-cycle circulation audit

Revisited the fixed-cofactor signed collision formula and the prime/smooth
linear-form conditions in CofactorDescentPreimage. Reflecting congruences
still does not preserve both the natural endpoint range and the retained
smoothness conditions. No uniform signed prime-pattern estimate resulted.

Added two kernel-checked theorems to MixedPrimeCycleObstruction.lean (saved
olean; permitted axioms only):
  balanced_four_cycle_all_comparisons_rise
  balanced_four_cycle_log_circulation_zero
The balanced mixed four-cycle at indices 10866,86936,28978,14488 has all
four ACTUAL largest-prime comparisons rising. Yet its logarithmic
circulation with two forward and two backward traversal edges is exactly
zero, by its previously verified endpoint-product equality.

This distinguishes traversal orientation from order-comparison sign.
Zero logarithmic circulation cannot simply be used as cancellation of
factorSign on the cycle. This is an obstruction to that auxiliary step,
not a disproof of the density conjecture or of every cycle-based approach.

No signed cross-term estimate sufficient for the target has been proved.
Spec.lean remains unchanged with its original sorry; no complete submission.

## Adjacent rational-rescaling barrier

New checked module Submission/AdjacentRescalingBarrier.lean, saved olean,
permitted axioms only, no admissions:
  reversed_adjacent_rescaling_bound
  reversed_adjacent_rescaling_both_bounds

Suppose positive integer coefficients satisfy
  a*n=b*(m+1), c*(n+1)=d*m.
Then
  (a*d-b*c)*n=b*c+b*d,
with strictly positive determinant. Consequently n<=b*c+b*d<=2*B^2
if b,c,d<=B. With all four coefficients positive and bounded by B,
the symmetric argument also gives m<=2*B^2.

Thus two rational rescalings with coefficients in a sub-square-root range
cannot directly swap endpoints of a large adjacent pair. This does not rule
out transformations with large numerically sized smooth coefficients, more
complicated correspondences, or other pairing methods. Those still require
unproved abundance, endpoint, and multiplicity estimates. It is not a
disproof of the conjecture.

No sufficient asymptotic cancellation estimate was obtained. Spec.lean is
unchanged with its original sorry; no complete proof/disproof to submit.

## New exact one-scale regularity criterion for the original conjecture

New completed module Submission/DyadicEndpointRegularity.lean, saved olean.
Main axiom checks list only propext, Classical.choice, Quot.sound. No
admission or unfinished scaffold remains.

Let g(N)=prefixMean N factorSign and
  Q(N)=smoothedEndpointBias N=(1/N)*sum_{k<N}|g(k)|.
Using the already proved uniform logarithmic absolute endpoint theorem,
checked the exact equivalence
  ORIGINAL density conjecture <-> Q(2N)-Q(N) -> 0.
Main name: density_iff_smoothedEndpointBias_dyadic_regularity.

Steps:
1. dyadic_increment_zero_iterate propagates asymptotic invariance to every
   fixed power of two.
2. nonneg_prefixMean_zero_of_dyadic_regularity: for ANY nonnegative f,
   if q(N)=prefixMean N f has vanishing dyadic increments and near-zero
   values in each sufficiently wide fixed multiplicative endpoint window,
   then q(N)->0. A near-zero M in [N,CN] lies between 2^j*N and 2^(j+1)*N
   for j<=C. Positivity makes the unnormalized numerator monotone, yielding
   q(2^j*N)<=2*q(M). Only finitely many dyadic iteration limits are used.
3. smoothedEndpointBias_syndetic_near_zero follows from the previously
   checked uniform logarithmic means of |g|, using the generic syndetic
   prefix-mean lemma.
4. A checked persistence inequality for any unit-bounded f:
   |prefixMean N f|^3 <= 96*prefixMean (2N+1) (k |-> |prefixMean k f|), N>0.
   This gives prefixMean_zero_of_absolute_prefixMean_zero.
5. The converse uses ordinary Cesaro preservation of convergence.

IMPORTANT: The dyadic regularity condition on Q has NOT been established.
The existing unweighted energy log savings and harmonic current bounds do
not justify it. This is an exact conditional reformulation, not a proof of
natural-density existence. Spec.lean remains unchanged with its original
sorry, and there is no complete proof/disproof to submit.

## Investigation of the new dyadic regularity condition

Revisited the actual factorSign_dyadic identity rather than adding another
conditional criterion. Algebraically, with g(N)=prefixMean N factorSign,
and h(n)=factorSign(n) on not-factorBetween(n), zero otherwise, the finite
pairing yields (for N>0)
  g(2N)-g(N)=1/N-prefixMean N h.
The 1/N is the exceptional pair at n=0; the dyadic identity holds for n>=1.
This calculation was used for the audit, not added as a new Lean theorem.

For the nonnegative smoothed endpoint bias, the remaining change involves
|g(2k)|-|g(k)|. The signed non-between prefix sum is not removable inside
that difference of absolute values. The already checked bounded harmonic
nonBetweenHarmonicSum is not a natural-prefix cancellation estimate.
The actual finite cancellation-reappearance example and local-minimum
energy-increase example remain relevant; no pruning or energy contraction
was inferred from the doubling identity.

No new sufficient arithmetic estimate or theorem was obtained in this
round. The dyadic regularity hypothesis remains unproved. Spec.lean is
unchanged with its original sorry; no complete proof/disproof to submit.

## Factor-mass reconstruction review

Re-examined whether conservation of each integer's total normalized
prime-factor mass can extend the low-product joint inclusion identities
into the missing large-product region. In a comparison p<q, replacing q
by its complementary factors makes the selected product involving p
smaller, but certifying that the selected collection is the FULL complement
requires excluding further factors. That exclusion is not supplied by the
available low-budget inclusion identities.

The checked finite fixed-marginal partition perturbation remains a valid
obstruction to an inference based only on mass conservation and those
identities. It is not a model of the actual continuous prime-factor
marginal law. No reconstruction theorem using that actual marginal, and
no absolutely continuous perturbation of that law, was established.
No claim about either was added to Lean.

No new sufficient arithmetic cancellation estimate resulted. Spec.lean is
unchanged with its original sorry; no complete proof/disproof to submit.

## Antisymmetric inverse-kernel scale audit

Revisited KloostermanFourthMoment, PowerSeparatedPrimeKernel,
ShortDivisorPrimeKernel, and the absolute-kernel obstruction, focusing on
whether the antisymmetric part could be controlled without a full joint
prime-factor distribution theorem.

The checked complete Kloosterman fourth moment gives nontrivial cancellation
for complete sums and suitable Fourier-controlled inverse tests. It does
not itself control the prime weights in the incomplete inverse kernel.
The losses incurred by a direct weighted/Fourier bound are not negligible
at the required natural scale in the large-product range. No stronger
weighted estimate was proved or assumed.

The existing polynomial Vaughan reduction still makes its short terms and
proper-prime-power error negligible in separated ranges while retaining the
actual signs. The long weighted kernel remains unestimated. Its signed
mean was not replaced by an unsigned sieve bound or by complete-modulus
cancellation.

No new Lean theorem or sufficient arithmetic estimate resulted. Spec.lean
remains unchanged with its original sorry; no valid complete submission.

## Continuation: long Vaughan grouping and largest-prime toggle

Re-read VaughanRoughGrouping, VaughanSmoothAnnihilation,
VaughanProductHead, OppositeProgressionWeights, LargestPrimeToggle, and
LargestPrimeBoundaryWeight, retaining the actual signed coefficients.

The logarithm-affine rough-factor formula does not give a free unweighted
progression in the smooth-part-one case: its direct Mangoldt term remains.
The rough-semiprime normalized coefficient is -1, in agreement with the
previously checked positive absolute reciprocal mass. The largest-prime
toggle instead retains a moving common-smoothness boundary weight. Dropping
that weight to invoke the unweighted progression bound would change the
sum; no estimate justifying that operation was found.

Also rechecked the damping expansion. Its exactly telescoping linear
coefficient does not supply an open interval of fixed-parameter cancellation.
The quadratic coefficient still contains the unestimated cross-prime skew;
no analytic-continuation conclusion was drawn.

No new sufficient cancellation estimate or Lean theorem was obtained.
Spec.lean remains unchanged with the original sorry. No complete proof or
disproof is ready for submission.

## Continuation: natural transfer endpoint comparison

Compared NaturalAuxiliarySkewCancellation, NaturalCyclicPrimeSkew,
ActualPrimeComparisonTransfer, ComponentwiseShiftedPrefixTransfer,
ComponentwiseHarmonicPrefixTransfer, and LocalGlobalPrimeRatio.

The actual natural transfer retains the adjacent endpoint N/p. Conditioning
on the prime multiplier in the auxiliary-gap kernel additionally retains
that auxiliary gap; exact multiplier invariance does not remove it.
Componentwise absolute transfer is stronger than scalar harmonic transfer,
but its endpoint sampling still does not yield the ordinary-prefix limit.
The local/global normalization L1 bound changes label normalization, not
this endpoint issue.

No new implication giving dyadic endpoint regularity or same-target natural
cancellation was obtained. No new theorem was asserted, and Spec.lean is
unchanged with its original sorry.

## NEW checked continuation: one dyadic harmonic window now suffices

Completed Submission/SingleDyadicWindowCriterion.lean and saved its .olean.
It compiles without errors or warnings. All three main axiom checks list
only propext, Classical.choice, Quot.sound. No admissions remain in it.

Using the already checked uniform logarithmic absolute endpoint theorem:

1. density_iff_single_dyadic_harmonic_window proves the ORIGINAL conjecture
   equivalent to the single limit
     rawHarmonicSum factorSign (2*N)-rawHarmonicSum factorSign N -> 0.
   The previous generic criterion required both ratios two and three.
   This reduction uses arithmetic information already available for factorSign;
   it is not a generic one-window Tauberian assertion for bounded sequences.

2. density_iff_single_dyadic_interior_harmonic_window gives the same
   equivalence with dyadicInteriorSign. The summable low and near-linear
   boundaries disappear by the previously proved window-error limit.

3. density_iff_nonBetweenHarmonicSum_converges proves the ORIGINAL conjecture
   equivalent to existence of a limit for nonBetweenHarmonicSum. The earlier
   bound |nonBetweenHarmonicSum N|<=3 is NOT convergence.

Generic checked steps:
- sum_range_double_pair and prefixMean_double_pair pair consecutive terms.
- dyadicHarmonicRounding f k = f(2k+1)*(1/(2k+1)-1/(2k)), with real division.
  Its absolute value is at most 1/(k+1)^2 when |f|<=1, including k=0.
- dyadic_coboundary_rawHarmonicSum is the exact identity
    H[f-(f(2k)+f(2k+1))/2](N)
      = Hf(N)-Hf(2N)+sum_{k<N}dyadicHarmonicRounding f k.
- A vanishing dyadic window makes this coboundary's raw harmonic sums
  converge. Kronecker then gives g(2N)-g(N)->0, g(N)=prefixMean N f.
- Consecutive prefix differences tend to zero. Thus dyadic regularity of g
  passes through absolute values and a second Cesaro average to the
  regularity condition in DyadicEndpointRegularity.
- For factorSign the coboundary's harmonic sum at N+1 is exactly
  nonBetweenHarmonicSum N. Both directions of its convergence criterion
  retain the summable reciprocal rounding term.

IMPORTANT: None of the three equivalent remaining limits has been proved.
This is a checked simplification of the missing estimate, not a settlement.
Spec.lean remains unchanged with its original sorry; no complete proof or
negation is ready for submission.

## Continuation: harmonic prime-insertion monotonicity check

Investigated whether finite initial prime cutoffs could give a monotone
approximation for the remaining harmonic convergence problem. A focused
finite calculation rules out monotonicity of their harmonic prefixes.

Added to Submission/PrimeInsertionCheck.lean, compiled with saved .olean:
  cutoffPrimeSkewRat
  insertion_thirteen_harmonic_increment
The latter is kernel-checked exact rational arithmetic and proves
  sum_{n<40} (skew_30030(n)-skew_2310(n))/n = -23/650.
Here 2310 and 30030 are the initial prime products through 11 and 13.
The change is 2/12-2/13+2/25-2/26-2/39. Thus even harmonic prefixes do not
increase monotonically under insertion of a new largest prime.
The printed axiom check uses only propext, Classical.choice, Quot.sound.

Exploratory evaluations of the infinite periodic harmonic limits also
suggested a negative increment at 13, but NO theorem about those infinite
values was proved or used. The checked claim is only the finite identity.
This is not a counterexample to the original conjecture.

A total-variation bound or cancellation estimate for accumulated insertion
changes remains unproved. The new single-window/convergence criteria have
not been discharged. Spec.lean is unchanged with its original sorry.

## Continuation: complementary-cutoff minimax audit

Read WeightedComplementSelection, MaximalShortPatternSelection,
MaximalComplementPrefixRow, ComplementPrefixIndicator,
LongComplementCriterion, and EscapingComplementCriterion.

Investigated convexifying the cutoff choice. A common fixed external test
weight is not the same as an arbitrary family of cutoff-dependent weights.
Moreover the selected estimate only controls X<=B^k with k fixed before
selection. No lower bound on the selected power exponent makes B^k cover
all complementary divisors. A mixed choice alone does not remove either
restriction. Decomposing an escaping complementary factor retains the
uncontrolled complementary component unless the escaping factor is already
near-linear, a range covered by earlier results.

No minimax implication giving the missing long-complement estimate was
proved or assumed. No new Lean theorem resulted. The single dyadic window
and nonBetweenHarmonicSum convergence criteria remain unproved. Spec.lean
is unchanged with its original sorry.

## Continuation: quantitative stability comparison

Compared ExactMultiplierChirpObstruction, FixedStableBias,
FixedStableSummableDefects, LocalPrimeLabelStability,
PowerPrefixQuantization, and AllPolynomialChirpExclusion.

The checked fixed-stable countermodels do not provide a counterexample to
an inverse theorem using the actual positive-power multiplier control and
maximum-under-multiplication law. Conversely, excluding the specific
polynomial-scale archimedean chirps is not such an inverse theorem. No
classification of all biased local models or estimate for the compressed
adjacent skew operator was proved. Fixed-multiplier harmonic summability
was not used to infer ordinary convergence.

No new arithmetic cancellation theorem resulted. The one-window criterion
remains unproved, and Spec.lean is unchanged with its original sorry.

## Continuation: endpoint propagation and full-marginal reconstruction review

Rechecked ActualPrimeComparisonTransfer, NaturalAuxiliarySkewCancellation,
ComponentwiseShiftedPrefixTransfer, ComponentwiseHarmonicPrefixTransfer,
LocalPrimeLabelStability, PowerPrefixQuantization, and the polynomial chirp
exclusions against the new SingleDyadicWindowCriterion.

A hypothetical propagation of a large bias at N to many smaller endpoints
could contradict the uniform logarithmic absolute endpoint theorem. The
available transfer does not provide that propagation: its adjacent endpoint
is N/p, and auxiliary-gap averaging still leaves the auxiliary gap. Common
entropy-scale selection and absolute componentwise estimates do not replace
these endpoints by N. No such propagation inequality was proved.

Also revisited the distinction between the checked finite-partition
low-total-mass countermodels and the actual limiting prime-factor marginal.
The finite models cannot alone rule out a reconstruction theorem using that
marginal. Conversely, no reconstruction theorem, continuous marginal
embedding, or new arithmetic mixed-moment estimate was established. Informal
possibilities concerning perturbations of three large parts were not used as
proved counterexamples or as claims about the conjecture.

No new Lean theorem or sufficient cancellation estimate resulted from these
reviews. In particular, the single dyadic harmonic-window limit and the
convergence of nonBetweenHarmonicSum remain unproved. Spec.lean is unchanged
with its original sorry; no complete proof or disproof is ready to submit.

## Continuation: repeated-label spacing and harmonic energy review

Compared PrimeLoserHarmonicDiagonal, PrimeCurrentAbsoluteBudget,
PrimeCurrentL2Convergence, PrimeWinnerNonadjacent,
PrimeWinnerCongruenceRuns, and the local-minimum collision estimates.

The spacing of occurrences of a prime label bounds unsigned incidence
counts, but does not supply orthogonality or sign cancellation for repeated
labels. The congruence-run identities retain same-direction contributions.
Automatic adjacent/local-extremum cancellation is already separated in
PrimeWinnerNonadjacent; its nonadjacent signed remainder is still unbounded
at the strength needed for the conjecture.

In particular, summability of the critical weighted harmonic diagonal was
not promoted to convergence of accumulated currents. Likewise, the checked
unweighted l2 convergence was not promoted to critical-weighted convergence
or to an l1 bound. No new sufficient cross-term estimate resulted.

Reconsidering the largest-prime toggle as a recursion also did not remove
its commonSmoothWeight. The weighted progression estimate cannot be applied
as though that input-dependent smoothness weight were absent or monotone.

No new Lean theorem was added in this review. Spec.lean remains unchanged
with its original sorry; the conjecture has not been proved or disproved.

## NEW checked continuation: weighted compactness of harmonic window currents

Completed Submission/PrimeWindowWeightedCompactness.lean (248 lines), with
saved olean. It compiles without errors or warnings; all five printed main
axiom checks use only propext, Classical.choice, Quot.sound. No admissions.

For fixed integer a>=1 define
  primeWindowCurrent a N p = rawPrimeWinnerHarmonic p (a*N)
                             - rawPrimeWinnerHarmonic p N,
  primeWindowMass a N p = sum_{N<=n<a*N, winner(n)=p} 1/n.

New checked bounds:
- primeWinner_window_card_bound:
    #{L<=n<U : winner(n)=p} <= 2*floor(U/p), for L>0.
  The proof covers the two adjacent multiples-of-p incidence sets.
- primeWindowMass_mul_label_bound:
    p*primeWindowMass a N p <= 2*a, for N>0.
- primeWindowMass_sum_bound: any finite sum of incidence masses is <=a.
- primeWindowCurrent_reciprocal_bound:
    |primeWindowCurrent a N p| <= 2*a/p, for p>0.
  Unlike the infinite-current absolute budget, there is no log(p) loss.
- primeWindow_critical_energy_bound:
    sum_{p in P} p*(primeWindowCurrent a N p)^2 <= 2*a^2
  for EVERY finite label set P and every N, including N=0.

New convergence:
- primeWindow_weighted_energy_zero:
  For EVERY FIXED w:N->R with w>=0 and w(p)->0,
    sum_{p<=a*N} w(p)*p*(primeWindowCurrent a N p)^2 ->0.
  This uses coordinate convergence of the fixed-prime harmonic currents,
  a finite-head/tail split, and the uniform critical-energy bound.
- primeWindowWeightedEnergy_eq_tsum and
  primeWindow_weighted_energy_tsum_zero give the full infinite-vector form.
  All nonzero window currents have p<=a*N.
- primeWindow_log_slack_energy_zero specializes to
    w(p)=(1+log(p+1))^(-delta)
  for every delta>0. It does NOT include delta=0.

LIMITATION: These results give boundedness, NOT decay, at the unslacked
critical weight p. There is no uniform estimate as delta tends to zero,
and no deduction of cancellation of the unweighted signed sum of currents.
The single dyadic harmonic-window criterion therefore remains unproved.

The initial scale-sensitive complementary-divisor review supplied no new
signed tail estimate: the selected short degree still does not exhaust the
full complementary endpoint, and arbitrary cutoff-dependent weights were
not substituted for a single external weight fixed before selection.

Spec.lean is unchanged with its original sorry. This is a checked partial
advance, not a settlement, and no proof/disproof is ready for submission.

## NEW checked continuation: growing-window prime-current l1 cancellation

Completed and compiled two development modules with saved oleans:
  Submission/VariableSupportSchur.lean
  Submission/GrowingWindowPrimeWinnerNorm.lean
All printed main axiom checks use only propext, Classical.choice, Quot.sound.
There are no admissions or remaining compile errors/warnings.

VariableSupportSchur:
- variable_cutoff_schur_of_sign_tests extends the previous triangular Schur
  theorem to arbitrary row-dependent finite support cutoffs B(N).
- It embeds row N at the strictly increasing index
    e(N)=sum_{j<=N}(B(j)+1),
  pads with zero outside the embedded rows, and applies the checked
  triangular theorem. No relation B(N)<=N is assumed.

GrowingWindowPrimeWinnerNorm:
- primeWinner_coloured_growing_harmonic_zero retains arbitrary FIXED Boolean
  colours of the winning prime on every moving window of diverging harmonic
  mass. The same local-quantization error bound as before is retained.
- shiftedPrimeWinnerCurrent A M p is the normalized harmonic signed current
  on the integer interval [A+1,A+M+1], inclusive.
- primeWinner_growing_harmonic_l1_zero proves
    sum_p |shiftedPrimeWinnerCurrent (A j) (M j) p| -> 0
  whenever shiftedHarmonicMass (A j) (M j) -> infinity.
  Absolute values are taken BEFORE the sum over labels.
- primeWinner_growing_harmonic_tsum_zero gives the full infinite-vector form;
  all nonzero coordinates have p<=A+M+2.
- primeWinner_uniform_long_harmonic_l1 gives a single mass threshold R for
  all intervals. No endpoint sequences need be chosen in that statement.
- primeWinner_moving_weights_growing_harmonic_zero and
  primeWinner_uniform_long_harmonic_weights allow arbitrary bounded prime
  weights chosen AFTER the interval. These follow from the l1 theorem,
  not from incorrectly treating a varying colour as a fixed stable label.
- shiftedPrimeWinnerCurrent_eq_raw_window is the exact identity
    [rawPrimeWinnerHarmonic p (A+M+2)-rawPrimeWinnerHarmonic p (A+1)]
      / shiftedHarmonicMass A M.

LIMITATION: The harmonic mass MUST diverge. On [N,2N) it stays bounded
(and tends to log 2), so none of these results supplies the unnormalized
single dyadic window limit. They also do not remove the extra vanishing
weight from PrimeWindowWeightedCompactness. The gap to ordinary density
has not been closed.

Spec.lean is unchanged with its original sorry. No completed proof or
negation of the conjecture is ready for submission.

## NEW checked continuation: ratio-uniform incidence and normalized critical energy

Completed and compiled with saved oleans:
  Submission/PrimeHarmonicWindowIncidence.lean
  Submission/GrowingWindowCriticalEnergy.lean
All printed main axiom checks use only propext, Classical.choice, Quot.sound.
No admissions, errors, warnings, or unfinished scaffolds remain in these files.

PrimeHarmonicWindowIncidence:
- Define reciprocalInterval L U = sum_{L<=n<U} 1/n.
- multiples_reciprocal_interval_bound proves, for L>0 and p>0,
    p * sum_{L<=n<U, p|n} 1/n <= reciprocalInterval L U + 1.
  This has an absolute boundary constant independent of p and of the window
  ratio. The proof writes the discrepancy from uniform density as the
  reciprocal-weighted discrete derivative of ((n-1) mod p)/p. First restrict
  to n>=max(L,p), since there are no earlier positive multiples of p.
- primeWinner_harmonic_window_label_bound proves, for 0<L<=U and p>0,
    p*|rawPrimeWinnerHarmonic p U-rawPrimeWinnerHarmonic p L|
      <= 3*(reciprocalInterval L U+1).
  Both incident endpoint labels are retained; the successor reciprocal costs
  a factor two. This improves the ratio dependence of the earlier 2a/p bound.
- reciprocalInterval_shift_le requires L>0. This condition is retained,
  since the analogous assertion starting at zero need not hold.

GrowingWindowCriticalEnergy:
- shiftedPrimeWinnerCurrent_mul_label_bound:
    p*|shiftedPrimeWinnerCurrent A M p| <= 3+3/H,
  H=shiftedHarmonicMass A M. These currents are NORMALIZED by H.
- shiftedPrimeWinnerCriticalEnergy A M is the full finite-support sum
    sum_p p*(shiftedPrimeWinnerCurrent A M p)^2.
  An exact tsum representation is also checked.
- shiftedPrimeWinnerCriticalEnergy_le_l1 bounds this by
    (3+3/H)*sum_p |shiftedPrimeWinnerCurrent A M p|.
- primeWinner_growing_harmonic_critical_energy_zero proves its convergence
  to zero whenever H tends to infinity, using GrowingWindowPrimeWinnerNorm.
- primeWinner_uniform_long_harmonic_critical_energy gives a single threshold
  working for all intervals of sufficiently large harmonic mass.

IMPORTANT: This is genuine critical-weighted convergence without an extra
logarithmic weight, but for NORMALIZED currents on GROWING-mass windows.
Equivalently the raw weighted energy is divided by H^2. It does not imply
critical-energy decay on [N,2N), whose harmonic mass tends to log 2, and it
is not a bound for ordinary prefix energy. No Tauberian upgrade removing
this distinction was proved or assumed.

Spec.lean is unchanged with its original sorry. There is still no completed
proof or disproof of the original conjecture to submit.

## NEW checked continuation: fixed-dyadic critical-energy criterion

Completed and compiled with saved olean:
  Submission/DyadicPrimeCriticalCriterion.lean
Main axiom checks use only propext, Classical.choice, Quot.sound.
There are no admissions, compile errors, or warnings in this new module.

Definitions:
- dyadicPrimeCriticalEnergy N = sum_{p<=2N} p*(primeWindowCurrent 2 N p)^2.
  The currents are UNNORMALIZED harmonic sums on [N,2N).
- dyadicPrimeCurrentL1 N = sum_{p in primeWinnerLabels(2N)} |current(N,p)|.
- dyadicPrimeCurrentL1Above B N restricts to labels above B.

Checked estimates and identities:
- primeWindowCurrent_eq_sum_filter, dyadicPrimeCurrent_total give the exact
  interval and full signed-sum identities.
- dyadicPrimeCurrent_low_bound bounds low-label absolute current by the
  number of B-smooth integers below 2N, divided by N.
- dyadicPrimeCurrent_high_sq_bound applies weighted Cauchy--Schwarz.
- dyadicPrimeCurrent_high_zero_of_criticalEnergy: for every fixed u>0,
  energy decay implies absolute cancellation above ceil((2N)^u).
- dyadicPrimeCurrentL1_zero_of_criticalEnergy completes the split, using
  smooth_count_ratio_log_bound and ceilPowerCutoff_succ_log_bound. The low
  contribution is at most 16u+o(1), and u is chosen after epsilon.
- dyadicPrimeCurrent_zero_off_labels and dyadicPrimeCurrentL1_eq_range
  reconcile the prime-label and integer-range supports, including N=0.
- dyadicPrimeCriticalEnergy_le_l1 gives E(N)<=4*L1(N).
- dyadicPrimeCriticalEnergy_zero_iff_l1 is an equivalence between the two
  UNPROVED cancellation limits, not an equivalence with the conjecture.
- dyadicPrimeCriticalEnergy_eq_tsum gives the full infinite-vector version.
- density_of_dyadicPrimeCriticalEnergy proves that E(N)->0 would imply the
  ORIGINAL density statement via density_iff_single_dyadic_harmonic_window.

LIMITATION: No unconditional decay of E(N), or of dyadicPrimeCurrentL1(N),
was obtained. The previously proved decay on growing-mass windows concerns
currents divided by that mass; it cannot be substituted for this hypothesis.
Likewise, the vanishing-extra-weight theorem does not allow weight 1.
The new file supplies a checked connection, not the missing arithmetic
cancellation. Spec.lean remains unchanged with its original sorry, and no
proof/disproof is ready for submission.

## Continuation: prescribed-endpoint quantitative stability review

Revisited the growing multiplier-range approach after the fixed-dyadic
critical-energy criterion, checking ActualPrimeComparisonTransfer,
PowerPrefixQuantization, PrimeLogQuantization, and the existing records of
rough-core and same-target entropy investigations.

The exact primeQuantLabel multiplier law is already available on a positive-
power range. It does not remove the prescribed-endpoint obstruction:
applying the natural transfer at X gives the adjacent endpoint floor(X/p).
Using X=p*N to target N makes the source sampling law depend on p; the
existing entropy recurrence is for a common source law. No common-law
replacement or scale-dependent recurrence was established.

Also considered aligning the different sources through a common product
of the primes and conditioning on residue classes. This does not supply a
valid entropy bound: conditioning all other residues to zero is a rare-event
conditional law, not the average conditional law in the entropy chain rule.
A chain-rule bound cannot simply be evaluated at that particular residue.
No independence or uniform conditional-entropy estimate was assumed.

The alternative rough-core graph formulation again leaves a signed
oriented count, already recorded earlier, rather than proving reversal.
This continuation supplies no new theorem and no improvement to the
unnormalized dyadic critical-energy estimate. Spec.lean is unchanged with
its original sorry; no completed proof or disproof is ready to submit.

## NEW checked continuation: reciprocal-rate energy replacement and harmonic collisions

Completed and compiled with saved oleans:
  Submission/PrimeWindowEnergyComparison.lean (178 lines)
  Submission/DyadicHarmonicSignedCollisions.lean (114 lines)
All printed main axiom checks use only propext, Classical.choice, Quot.sound.
No admissions, errors, or warnings remain in either completed module.

PrimeWindowEnergyComparison:
- primeLoserWindowCurrent a N p is the UNNORMALIZED loser harmonic current
  on [N,aN); primeLoserWindowMass is its unsigned incidence mass.
- primeLoser_window_card_bound and primeLoserWindowMass_mul_label_bound
  establish the same spacing bounds as for winner labels.
- primeWindowCurrent_pair_label_bound: for a>=1 and N>0, BOTH currents
  satisfy p*|current|<=2a, including the zero label.
- primeWindow_critical_energy_difference_bound: uniformly in EVERY finite
  label set P, the absolute difference of the two critical energies is at
  most 4a*(2/(aN-1)+2/(N-1)), for N>=2. Factorization of the difference of
  squares and the per-label bounds reduce it to the existing l1 flux bound.
- dyadicPrimeCriticalEnergy_difference_bound: |Ewinner(N)-Eloser(N)|<=64/N.
- dyadicPrimeCriticalEnergy_difference_zero.
- dyadicPrimeCriticalEnergy_zero_iff_loser: either unproved energy-decay
  hypothesis is equivalent to the other. This is NOT unconditional decay.

DyadicHarmonicSignedCollisions:
- dyadicLoserWindowDiagonal N=sum_{N<=n<2N} min(P(n),P(n+1))/n^2.
  Its convergence to zero follows from the already checked summability.
- dyadicLoserWindowSignedCollisions N retains all ORDERED unequal pairs
  n,m in [N,2N) with equal loser labels, with weight
    primeLoser(n)*factorSign(n)*factorSign(m)/(n*m).
- dyadicPrimeLoserCriticalEnergy_collision_formula is the exact identity
    Eloser(N)=diagonal(N)+signedCollisions(N).
- dyadicPrimeEnergy_sub_signedCollisions_zero proves
    Ewinner(N)-signedCollisions(N) ->0.
- dyadicPrimeEnergy_zero_iff_signedCollisions.
- Positivity gives signedCollisions(N)>-epsilon eventually. This is the
  LOWER one-sided bound, NOT the upper bound needed for decay.
- density_of_dyadicSignedCollisions_limsup: the unproved assertion that
  signedCollisions(N)<=epsilon eventually for every epsilon>0 would imply
  the ORIGINAL density statement.

LIMITATION: No upper cancellation estimate for the signed repeated-label
sum was obtained. Neither the unsigned incidence bounds nor the summable
squared-increment diagonal estimates that sum. The two modules improve
and quantify the replacement/error analysis, but do not settle Erdős 371.
Spec.lean remains unchanged with its original sorry. No proof/disproof is
ready for submission.

## Continuation: actual upper-half inverse-kernel parameter check

Rechecked the exact commonEndpointPrimeSkew and weightedOppositeKernel
formulas, rather than substituting a complete unweighted residue count.
The upper-half hypotheses give b<=N/(C+1)<p for B<p<=C, with the prime
variable q in (C,N/b]. At scales p comparable to C=N^u, the cofactor range
has size N^(1-u); u is not restricted to a small neighborhood of 1/2.

The existing size-sensitive unweighted inverse-rectangle estimate still
requires a much denser rectangle for relative savings. The relation between
these actual ranges does not make it apply across all fixed u<1. Moreover,
the q-variable retains its prime weight (or the corresponding long Vaughan
weight after replacement). An unweighted rectangle estimate cannot simply
be inserted into this weighted sum, and complete-modulus cancellation
cannot replace the incomplete weighted interval.

No new weighted inverse estimate, signed collision bound, or arithmetic
cancellation theorem was established in this review. The conjecture in
Spec.lean remains unchanged with its original sorry. No valid settlement
is ready for submission.

## NEW arithmetic continuation: unsigned sublinear-separation collision removal

Completed and compiled with saved oleans:
  Submission/ShortSeparationPrimeCollisions.lean
  Submission/ShortSeparationCollisionRemoval.lean
All main axiom checks use only propext, Classical.choice, Quot.sound.
No admissions, warnings, or failed scaffolds remain. CheckShortTmp was removed.

New arithmetic count:
- common_endpoint_divisor_offset: if p divides one endpoint of each of
  (n,n+1) and (n+d,n+d+1), then p divides d-1, d, or d+1.
- neighboring_divisor_offsets_card_bound: for d in [2,D], the count of such
  offsets is at most 3*floor((D+1)/p). All three integers are positive, so
  there is NO extra constant from the zero multiple. Each of the three
  maps d -> d-1,d,d+1 injects into positive multiples <=D+1.
- nearLoserOffsets_label_card_bound: for a fixed starting index n, the
  actual matching-loser offsets (with any upper endpoint U) satisfy
    primeLoser(n)*card(offsets) <= 3*(D+1).
  The critical weight cancels the residue-spacing denominator.
- nearLoserOffsets_harmonic_mass_bound: the forward row's unsigned harmonic
  mass is at most 3*(D+1)/n^2.
- dyadicForwardNearLoserMass_bound: summing n in [N,2N) gives
    forward nonadjacent unsigned mass <= 3*(D+1)/N, for N>0.
- dyadicForwardNearLoserMass_zero: EVERY D(N)/N->0 makes this mass vanish.
  No logarithmic loss and no cancellation of signs are needed.
- dyadicAdjacentLoserMass_bound/zero: adjacent matching-loser mass is at
  most dyadicLoserWindowDiagonal(N), already known to tend to zero.

Full ordered-pair connection:
- dyadicNearLoserPairs(D,N) includes all unequal n,m in [N,2N) with equal
  loser labels and Nat.dist(n,m)<=D.
- dyadicNearLoserMass_eq_twice_forward is an exact swap bijection.
- dyadicNearLoser_forward_offset_sum is an exact offset reindexing.
- dyadicNearLoserMass_bound:
    nearMass(D,N) <= 2*diagonal(N)+6*(D+1)/N, for N>0.
- dyadicNearLoserMass_zero for every sublinear D.
- dyadicSignedCollisions_near_far_split is an exact signed decomposition.
- dyadicSignedCollisions_sub_far_zero: removing ALL pairs within a
  sublinear separation changes the signed collision sum by o(1).
- dyadicSignedCollisions_zero_iff_far records the resulting equivalence.

LIMITATION: Collisions at larger separations remain. This argument does
not establish independence of two far-apart clusters, nor cancellation of
those signed terms. It does not allow D comparable to N in the zero-limit
statement (although the finite bound remains valid and is O(D/N)). Thus it
is a genuine unconditional estimate for a part of the arithmetic cross sum,
not a settlement of the conjecture.

Spec.lean remains unchanged with its original sorry. No completed proof or
disproof is ready to submit.

## Continuation: cofactor-descent review after short-separation removal

Checked CofactorDescent and CofactorDescentPreimage against the remaining
long-separation signed collisions. The proposed modulo reduction and
comparison reversal are ALREADY formalized. Their inverse formulas retain
q=r+p*k prime and, outside the upper-half range, the simultaneous smoothness
condition on (b*r +/- 1)/p+b*k. No weighted preimage-mass conservation or
contractive signed operator estimate was established.

The noninjective descent was not treated as a pairing, and reducing the
index was not used to infer cancellation of natural counts or harmonic
mass. No new theorem resulted in this review. The new sublinear-separation
removal from the previous continuation remains checked, but the surviving
long-separation sum is unestimated. Spec.lean remains unchanged with sorry.

## NEW arithmetic continuation: short-window energy with quadratic relative length

Completed Submission/ShortWindowCriticalEnergy.lean and saved its olean.
All printed main axiom checks use only propext, Classical.choice, Quot.sound.
No admissions, errors, warnings, or temporary checks remain.

New arithmetic input:
- same_sign_loser_dvd_sub: equal loser labels AND equal comparison signs
  force the common label to divide the index difference itself, not merely
  one of its three neighboring values.
- spaced_interval_label_card: a p-spaced finite set S in [L,U) satisfies
    p*card(S) <= U-L+p.
  The proof uses the minimum element and an injective quotient map. The
  zero-label case is explicitly included without dividing by zero.
- interval_loser_same_sign_card applies this separately to the two signs.
- interval_primeLoser_weighted_square_bound: after splitting a current into
  nonnegative positive and negative reciprocal sums, discard their negative
  cross term and apply Cauchy--Schwarz separately. This gives
    p*J_p(L,U)^2 <= (U-L+p) * sum_{L<=n<U, loser(n)=p} 1/n^2.
  No unproved cancellation is used.

Main finite bound:
- intervalPrimeLoserCriticalEnergy_bound, for 0<L<=U:
    sum_{p<=U} p*J_p(L,U)^2
      <= sum_{L<=n<U} primeLoser(n)/n^2 + (U-L)^2/L^2.
  Currents are raw, UNNORMALIZED harmonic sums.
- intervalLoserDiagonal_le_tail and the previously proved summability make
  the diagonal error small uniformly in EVERY upper endpoint U.
- intervalPrimeLoserCriticalEnergy_uniform_error records that uniformity
  while RETAINING the quadratic relative-window-length term.
- intervalPrimeLoserCriticalEnergy_sublinear_zero: for arbitrary sequences
  L_j->infinity, L_j<=U_j and (U_j-L_j)/L_j->0, the full raw critical loser
  energy tends to zero. No extra vanishing prime weight is needed.

LIMITATION: On [N,2N), (U-L)^2/L^2=1. Thus this supplies boundedness but not
vanishing for the fixed-dyadic criterion. It does not control the required
macroscopic signed correlations or upgrade the growing-harmonic-window
result. It is a genuine unconditional short-window estimate, not a proof
or disproof of the original density statement.

Spec.lean remains unchanged with its original sorry. No valid completed
settlement is ready for submission.

## Continuation: two-prime averaging after quadratic short-window control

Rechecked DoublePrimeAveraging, NaturalPrimeGapTransfer, and
NaturalAuxiliarySkewCancellation against the new ShortWindowCriticalEnergy
estimate. The two-sided prime-divisor replacement already has a uniform
vanishing error. Its exact cofactor formula still retains p*m+1=q*k and
the actual smooth-cutoff skew of m,k. No bound for that signed sum was
established.

Comparable p,q compare N/p with N/q, not with N. The new short-window
critical-energy bound is for accumulated ADJACENT prime-label currents;
it does not identify the comparison of two separated cofactor endpoints
with that accumulated current. A generic telescoping replacement would
lose the non-coboundary order-skew terms. No such replacement was made.

No new theorem resulted from this review. Spec.lean remains unchanged with
its original sorry, and no complete proof or disproof is available.

## NEW checked continuation: continuous polynomial moment-null kernels

Completed Submission/ContinuousKernelObstruction.lean (228 lines) and saved
its olean. All printed axiom checks use only propext, Classical.choice,
Quot.sound; no warnings, admissions, or errors remain. CheckKernelTmp removed.

For h(t)=t^3(1-t)^3, F=(partial_x-partial_y)^2[h(x)h(y)], define
k1=partial_x partial_y F and k2=partial_x partial_y[(x+y)F/2].
Proved in Lean:
- Both kernels symmetric.
- Each kernel has zero row integral on [0,1].
- Every sum-line integral inside the square is zero, using exact line
  primitives and vanishing endpoint jets h,h',h''.
- Square CDF integrals are F(t,t) and t F(t,t).
- F(t,t)=-6t^4(t-1)^4(2t^2-2t+1).
- The oriented CDF derivative pairing has strictly positive integral,
  because its integrand is the square F(t,t)^2.

This cubic bump is enough for the integral identities; the zero-extended
kernels are bounded piecewise polynomial, NOT globally smooth. Exact SymPy
algebra independently gives integral(F(t,t)^2)=74/1616615, but the Lean proof
needs and proves only positivity, not that rational value.

Wrote Submission/ContinuousPartitionPerturbation.md, auditing the proposed
PD(1) embedding with a=7/20, b=3/8, c=3/5. The ordered factorial expansion
has three overlap terms: integral over x+y<1-s; twice sum z_j times a row
integral up to 1-s; and sum_{j!=l} z_j z_l K(z_j,z_l). Every term is zero
for s<c. No missing half factor occurs with the ordered-pair convention.
The antisymmetric product perturbation therefore preserves exact PD
marginals and all mixed factorial densities of combined mass <=1, while
its largest-atom rising bias is epsilon*integral(A1^2)>0.

STATUS OF THAT NOTE: a mathematical argument using the standard PD(1)
factorial density, NOT a Lean formalization of PD or its probability-space
construction. It obstructs reconstruction from low-mass factorial data
alone; it does NOT disprove the original arithmetic conjecture, construct
an actual integer sequence, or assert all arithmetic constraints survive.
Only the kernel calculus is checked in Lean.

Also rechecked UpperHalfSmoothSkew and ShortPrimePairCancellation: the
short-product contribution is already negligible, while the required
long prime-weighted inverse discrepancy is still unestimated. No natural
same-endpoint cancellation was obtained. Spec.lean is unchanged with its
original sorry; no valid complete submission is ready.

## Continuation: positive endpoint-averaging audit

Checked whether actual_prime_comparison_transfer could yield a positive
averaging relation and a maximum principle without replacing N/p by N.
Its right side is still the prime-gap order-skew correlation at N, not
the adjacent observable at N. Auxiliary skew cancellation additionally
averages over a gap k; after prime conditioning that k remains. Thus no
positive self-averaging identity for the adjacent endpoint bias was proved.
Fixed-cyclic prime cancellation is not uniform in the cyclic process/period,
so it does not justify this missing replacement either.

No new arithmetic cancellation theorem resulted from this audit. The new
ContinuousKernelObstruction module is auxiliary; Spec.lean remains unchanged
with its original sorry. No completed proof/disproof is available.

## NEW continuation: split/merge obstruction reaches the upper-half region

Investigated whether the previous continuous kernel's support below 1/2 left
open reconstruction of symmetry when both largest prime factors are above
the square-root scale. Developed a different signed insertion identity:

  (x,y,z,R) - (x,y+z,R) - (y,x+z,R) - (z,x+y,R) + 2(x+y+z,R).

Any factorial observation of total selected mass below all three pair sums
annihilates this combination pointwise. Such a test can select no merged
atom and at most one original block atom; residual-only and single-atom
coefficients cancel separately. This identity includes arbitrary residual
partitions and is not limited to a finite list of moments.

Completed Submission/MergeKernelObstruction.lean with saved olean, no errors,
no warnings/admissions, and all printed axiom checks permitted. Its finite
certificate has two five-state families of total mass 100: triples
(24,30,36) plus residual 10, and (25,31,37) plus residual 7, with three
pair-merges and the full merge in each family. The signed vectors a,b have
coefficients (1,-1,-1,-1,2); K(i,j)=a(i)b(j)-b(i)a(j). Checked:
- row/column zero, |K|<=4;
- mixed inclusion moments of combined mass <110 vanish;
- rising signed mass 8, upper-half rising signed mass 7;
- W=1/100+K/1000 is strictly positive with fixed uniform marginals;
- all combined-mass-at-most-100 moments equal independence;
- full rising mass 229/500 and upper-half rising mass 287/1000.

Wrote Submission/SplitMergePDObstruction.md. Using the standard PD(1)
factorial Palm formula, a bounded density on a small box of triples gives
bounded Radon densities for all five insertion/merge pushforwards; the
convolution fibers have determinant-one changes of variables. Boxes near
(.24,.30,.36) and (.25,.31,.37) have interlaced largest-atom supports, giving
exact oriented pairings 8 and 7. The antisymmetric product perturbation
preserves exact PD marginals and low-mass factorial data while biasing
BOTH full and upper-half comparisons.

STATUS: the PD construction is a mathematical argument using the stated
standard Palm law, not a Lean formalization of that law or of PD. Only the
finite certificate is checked in this module. It obstructs that particular
reconstruction strategy; it is NOT a disproof of the arithmetic conjecture.
No actual integer factorization limit with this law was constructed.

Spec.lean remains unchanged with its original sorry. No completed proof or
negation of Erdős 371 is available, and no proof has been submitted.

## NEW arithmetic continuation: natural Katai Fourier tools and spectral atom exclusion

Completed SIX modules, 1067 lines total, with saved oleans:
  StableKataiCriterion.lean (223)
  StableIrrationalFourier.lean (161)
  StableSlowWeightFourier.lean (188)
  StableBlockFourier.lean (159)
  StableLocalCovarianceFourier.lean (173)
  NaturalSpectralAtoms.lean (163)
All compile without admissions, errors, or warnings; printed main axiom
checks use only propext, Classical.choice, Quot.sound. CheckKataiTmp removed.

This is NEW NATURAL arithmetic information, not another finite countermodel.
It does NOT settle the adjacent largest-prime comparison conjecture.

### Finite Katai criterion, including moving test/stable families

StableKataiCriterion introduces kataiRow, kataiPair, kataiStableSum and
kataiOffDiagonal. kataiPair(a,N,p,q) is the ACTUAL sum
  sum_{1<=m<=N/max(p,q)} a(p*m)*a(q*m).
No endpoint substitution is made.

Using the previously checked prime-divisor variance and Turán bound:
- prime weighted replacement error is bounded by the sum of fixed-prime
  dilation defects;
- Cauchy--Schwarz gives stableSum^2 <= N*(N*sum_{p in S}1/p+offDiagonal);
- the diagonal is bounded by N/p with exact positive-multiple ranges;
- stable_katai_orthogonality: if f_N,a_N are uniformly real unit-bounded,
  every fixed-prime f_N dilation defect has normalized mean zero, and every
  fixed distinct-prime a_N pair correlation above tends to zero after /N,
  then (1/N)sum_{n=1}^N f_N(n)*a_N(n) -> 0.
Both f_N and a_N may depend arbitrarily on N, subject to these hypotheses.

### Natural irrational Fourier cancellation for actual maxPrimeFac

StableIrrationalFourier proves exact geometric-sum bounds for fourier(k*m)x,
for every nonzero integer k and infinite-order x in UnitAddCircle. Real/imag
product-to-sum identities give the Katai pair hypotheses.

stable_irrational_fourier_zero handles any bounded stable real family.
maxPrimeFac_moving_weight_dilation_zero proves the required defects for
  f_N(n)=g_N(Nat.maxPrimeFac n)
UNIFORMLY over arbitrary bounded real prime weights g_N. Outside
P(n)<=p, multiplication by a fixed positive p leaves P(n) exactly unchanged;
the remaining fixed-smooth-number set has natural density zero.

maxPrimeFac_moving_weight_fourier_zero therefore proves
  (1/N)sum_{n=1}^N g_N(P(n))*fourier(n)x -> 0
for every fixed infinite-order x. The weights can depend on N. This is
one-coordinate Fourier cancellation, not a shifted product theorem.

### Slowly varying test coefficients and blockwise L1

StableSlowWeightFourier supplies a finite Abel bound
  |sum_{m=1}^M w(m)g(m)| <= B*(1+positiveVariation(w,M))
when |w|<=1 and every positive-prefix g sum is bounded by B.
SlowDilationVariation(w_N) means the variation of m -> w_N(p*m), divided
by N, vanishes for every fixed positive p. The product-dilation variations
in Katai's off-diagonal sums are bounded by the two individual variations.

stable_slow_weight_irrational_fourier_zero permits such arbitrary bounded
w_N multiplying the Fourier test, WITHOUT assuming w_N multiplicatively
stable. Both real and imaginary components are proved.

StableBlockFourier proves that w_N(n)=b_N(floor(n/H_N)), for ANY bounded
block coefficients b_N, has SlowDilationVariation whenever H_N -> infinity.
The finite variation bound is <=2*p*(N+1)/H_N, by telescoping the monotone
integer block indices. It is uniform in all block coefficients.

Taking signs separately on the real/imaginary Fourier sums in each block
then proves stable_block_fourier_mass_zero and its actual-maxPrimeFac
corollary. Explicitly, the sum of the absolute COMPLEX Fourier block sums,
divided by N, tends to zero. Blocks are the fibers of floor(n/H_N) within
1<=n<=N. H_N may tend to infinity at ANY rate, including arbitrarily slowly.
No summation of different blocks before absolute values is substituted.

### Local covariance and natural spectral irrational-atom exclusion

StableLocalCovarianceFourier defines
  B_H(n)=(1/H)sum_{0<=h<H} f(n+h)*fourier(n+h)x.
Its norm is <=1 and its one-step variation is <=2/H. The p-step norm
variation is <=2*p/H, so real/imaginary parts satisfy the slow-dilation
condition for every H_N -> infinity, regardless of the bounded family f_N.

The weighted Fourier theorem, applied to conjugate B_H, proves
  localCovarianceFourierMean(N,H_N,f_N,x) -> 0,
where the exact checked expansion is
  (1/H)sum_{0<=h<H}
    [(1/N)sum_{n=1}^N f_N(n)*f_N(n+h)] * fourier(-h)x.
This averages the gap over a growing window. It is NOT cancellation at h=1.

NaturalSpectralAtoms proves the generic joint-limit lemma needed to avoid
an illegitimate interchange of limits:
- a strictly increasing endpoint subsequence admits an extension of any
  growing H_j to a growing function of every natural endpoint, using a
  Nat.findGreatest inverse;
- convergence on EVERY growing graph H(N) implies joint convergence as
  both N,H tend to infinity;
- therefore any subsequential fixed-H row limits also tend to zero as H
  tends to infinity.

It then proves linear Fourier-average atom extraction by dominated
convergence. Combining the joint covariance estimate and atom extraction:
  natural_covariance_spectral_no_infinite_order_atoms
says that ANY finite positive circle measure whose Fourier coefficients
are the natural covariance limits of a bounded stable family along ANY
endpoint subsequence D_j -> infinity has no infinite-order atoms.
  maxPrimeFac_natural_spectral_no_infinite_order_atoms
specializes this to arbitrary bounded endpoint-dependent real prime weights.
Full natural covariance convergence or natural density existence is NOT
assumed. A compatible finite positive spectral measure is an explicit
hypothesis; this module does not construct a natural empirical word law.

This removes the harmonic-only restriction on the available ONE-COORDINATE
irrational spectral-atom theorem. It does not supply natural dilation
invariance of the whole word law, fixed-gap two-coordinate symmetry, or
uniform control at moving near-rational frequencies. In particular a
continuous spectral part can still contribute a nonzero skew at gap one.
The prime-gap transfer still retains the shorter adjacent endpoint N/p.

### Review limitations and next plausible integration

The initial attempted L1/critical-energy upgrade was not made: fixed-sign
absolute endpoint estimates do not automatically control an L1 norm over
prime labels with signs varying independently at each endpoint. Random
high-dimensional directions already obstruct that generic inference.

A possible next step is to construct natural empirical word limits for the
actual finite labels and connect their coordinate covariance measures to
the new no-irrational-atom theorem, then integrate that input into the
prime-gap/entropy argument. This is not expected by itself to remove the
N/p source/target mismatch; that obstruction must remain explicit.

Spec.lean remains unchanged with its original sorry. No completed proof or
negation of Erdős 371 is available. No proof has been submitted.

## Continuation: actual natural word laws and prime-gap skew cancellation

Completed five modules, 528 lines total, all with saved .olean files:
- NaturalWordLimit.lean (130)
- NaturalWordSpectrum.lean (120)
- NaturalOddPrimeEnergy.lean (76)
- NaturalComplexSpectrum.lean (105)
- NaturalPrimeSkew.lean (97)

All compile without admissions/errors/warnings. The printed main axiom
checks are exactly propext, Classical.choice, Quot.sound. Removed
CheckNaturalWordTmp.lean. The correct API is the ROOT name
`integral_complex_ofReal`, not MeasureTheory.* or Complex.*.

1. NaturalWordLimit constructs genuine empirical probability measures,
   their real integral formula, and a common weak subsequence for arrays
   that depend on the endpoint. Index convention is explicit:
   naturalWordEmpirical L N samples N+1 points, n=1,...,N+1, of L (N+1).
   A uniform telescoping bound proves stationarity for EVERY such array.
   exists_stationary_natural_word_limit chooses the law before any test.

2. NaturalWordSpectrum connects real continuous pair cylinders to the
   natural covariance limits in NaturalSpectralAtoms. A bounded observable
   defect is <=2 times the label defect. Every real unit-bounded observable
   of one common stable-array natural word law therefore has a finite
   positive spectrum with no infinite-order atoms. The arithmetic
   exists_primeQuantLabel_natural_spectral_limit uses exact eventually
   trivial fixed multipliers from PrimeLogQuantization. No harmonic word
   dilation domination is assumed for this natural law.

3. NaturalOddPrimeEnergy factors the older odd-energy theorem through a
   supplied spectral measure/no-atom hypothesis. It applies to actual
   natural word laws and primeQuantLabel. The empirical energy converges
   at every fixed prime cutoff; the limiting word-law energy tends to zero
   when the prime cutoff grows. The order of these limits is explicit.

4. NaturalComplexSpectrum extends atom exclusion to complex observables
   whose real and imaginary parts are individually unit bounded. A checked
   positive-energy domination gives
       sigma_f.real {x} <= 2*(sigma_Re_f.real {x}+sigma_Im_f.real {x}).
   This does NOT discard mixed covariances: it bounds the full complex
   polynomial energy pointwise and extracts atom masses using the bounded
   Fourier concentration polynomials and dominated convergence.

5. NaturalPrimeSkew combines complex spectra with the existing finite
   antisymmetric pair-phase expansion. In any natural empirical law of a
   stable array, every fixed antisymmetric finite-label observable has
   prime-gap mean tending to zero. primeQuantLabel_natural_prime_skew_zero
   specializes this to the actual arithmetic labels. The actual empirical
   prime-gap mean converges to its word-law value at each fixed cutoff.

LIMITATION / AUDIT: The entropy transfer still compares adjacent means at
N/p to gap-p means at N. These new natural-law theorems cancel the latter
prime-gap averages, but do NOT replace N/p by N, and do NOT settle gap one.
No natural full-word dilation domination, uniform moving near-rational
spectral estimate, or fixed-dyadic signed cancellation was inferred.

Reviewed Mellin weights p^(it) as a possible endpoint detector. No new
estimate was proved. Even modulated averages over primes tending to
infinity inspect endpoints far below the prescribed endpoint and can miss
bias localized to a fixed multiplicative neighborhood. The existing fixed
stable-label countermodels remain relevant; they are not counterexamples
to the arithmetic conjecture and do not have its maximum law. No inverse
classification using polynomial-range stability was found.

Spec.lean is unchanged, still with the original sorry, SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
There is still no complete proof or disproof of Erdős 371 to submit.

## Continuation: uniform natural endpoint continuity of exact prime marginals

NEW checked arithmetic result, not just a generic stable-sequence theorem.
Two modules, 303 lines, with saved .olean files:
- PrimeMarginalEndpoint.lean (218)
- PrimeMarginalTotalVariation.lean (85)
All compile without errors/warnings/admissions. Main axiom checks contain
only propext, Classical.choice, Quot.sound. Removed CheckMarginalTmp.lean.

For any bounded real weight g on exact prime values, define
  primeMarginalMean g N = (1/N) sum_{n=1}^N g(P(n)).
Using the PREVIOUSLY CHECKED Alladi identity alladi_divisors and
leastFactorTerm_eq_moebius, a weight vanishing for p<=B has Dirichlet
coefficients supported on d>1 with minFac(d)>B, each bounded by one.

The key finite bound is
  |mean_g(M)-mean_g(N)|
    <= (1/M+1/N) * roughNumberCount(B,N+1)
when 1<=B, 0<M<=N, |g|<=1, and g vanishes on [0,B].
The proof retains a common extended divisor range through N. After division
by the endpoints, the main 1/d terms cancel exactly; each remaining
normalized floor difference is <=1/M+1/N. No prime distribution theorem or
unproved smooth-number asymptotic is used.

Truncating an arbitrary g below B gives the uniform bound
  |mean_g(M)-mean_g(N)| <= (1/M+1/N) *
    ( #{n<N:P(n)<=B} + 2 + roughNumberCount(B,N+1) ).

Set B=subpowerCutoff(N). The parenthesized quantity / N tends to zero by
already checked smooth- and rough-number sparsity. Hence for any fixed K,
any M_j,N_j tending to infinity with M_j<=N_j<=K*M_j eventually, and ANY
endpoint-dependent bounded weights g_j,
  mean_{g_j}(M_j)-mean_{g_j}(N_j) -> 0.
The error bound is independent of the weights.

PrimeMarginalTotalVariation uses the sign of each probability difference
as an endpoint-dependent test and proves the explicit conclusion
  sum_p |Pr_{n<=M_j}(P(n)=p)-Pr_{n<=N_j}(P(n)=p)| -> 0.
The finite sum covers all primes through max(M_j,N_j), including the junk
value P(1)=1. This is full marginal L1 convergence, not merely convergence
for fixed cutoffs or finitely many fixed tests.

Names:
- primeMarginalMean_rough_endpoint_bound
- primeMarginalMean_endpoint_bound
- primeMarginalEndpointBudget_tendsto_zero
- primeMarginalMean_comparable_tendsto_zero
- primeMarginalL1Distance_comparable_zero

IMPORTANT LIMITATION: This is ONE-coordinate endpoint invariance. It is
not total-variation convergence of adjacent PAIR laws, and it does not
propagate the adjacent comparison bias from N to N/p. The previous natural
spectral and entropy results do not supply that missing implication.
Identical one-coordinate marginals alone allow nonsymmetric joint laws.

Also reviewed growing-multiplier max-law arguments, same-target entropy
sampling, and near-identity CRT reflections. No new two-coordinate
cancellation estimate was obtained. Varying the source with the prime still
changes the sampling law; the available common-source entropy theorem
cannot be reused without an additional argument.

Spec.lean remains unchanged with its original sorry, checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof of the original conjecture is ready to submit.

## Continuation: fixed-residue independence for exact prime marginals

NEW checked module: PrimeMarginalPeriodic.lean.
Saved .olean; all three main theorem axiom checks contain only propext,
Classical.choice, Quot.sound. No admissions/errors/warnings remain. Removed
CheckPrimeResidueTmp.lean.

Reviewed the dyadic endpoint regularity route first. The implication from
factorSign dyadic regularity to the original conjecture is ALREADY proved
in SingleDyadicWindowCriterion; no duplicate conditional theorem was added.
The regularity hypothesis itself remains unproved. The one-coordinate
Alladi argument cannot just be applied to the pair: two divisor moduli can
have product up to N^2, so the corresponding absolute rounding budget is
not the negligible one-dimensional rough count.

The new arithmetic theorem instead applies Alladi duality to periodic
one-coordinate tests:
- For d coprime to q, a real unit-bounded mean-zero function on ZMod q has
  positive progression prefix sums along d*m bounded by q, uniformly in d
  and the progression endpoint. This follows from permutation of a full
  residue period and exact periodic cancellation.
- A checked weighted divisor-sum reindexing turns sum g(P(n))*a(n mod q)
  into the sum of the least-prime divisor coefficients times these
  progression prefixes.
- If g vanishes at p<=B and B>=q, all active coefficients are q-coprime.
  The finite absolute sum is <=q*roughNumberCount(B,N+1).
- Truncation of an arbitrary bounded g adds only
  #{n<N:P(n)<=B}+2. Thus the normalized total error tends to zero for
  B=subpowerCutoff(N), for every fixed q.

Main primeMarginal_moving_periodic_zero permits BOTH g_N(p) and a_N(r) to
vary with N; only q is fixed, |g_N|,|a_N|<=1, and sum_r a_N(r)=0 are needed.

Specializing to a centered residue indicator gives
primeMarginal_moving_residue_independence:
  (1/N) sum_{1<=n<=N, n mod q=r_N} g_N(P(n))
     - (1/q)*(1/N) sum_{1<=n<=N} g_N(P(n)) -> 0.
The weights and the tested residue may both depend on the endpoint. This
is a uniform arithmetic marginal statement, not an assertion of pair
independence or of natural adjacent reversal symmetry.

Scope remains limited: pairwise conditional laws can have nonzero
circulation even when both marginals are independent of a fixed residue.
The natural entropy transfer still has its shorter adjacent endpoint N/p.
No proof of factorSign dyadic regularity, the single dyadic harmonic-window
limit, or the original conjecture was obtained.

Spec.lean is unchanged with its original sorry, checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof is ready to submit.

## Further continuation: audit of the adjacent remainder after marginal progress

Rechecked SmallPrimeReflection, SignedRoughUnitPowerCutoff,
UncoveredComplementCriterion, ComplementPrefixIndicator,
LongComplementCriterion, TwoTargetMaximalSelection, and
MaximalComplementPrefixRow against the new marginal estimates.

No new two-coordinate estimate resulted. The one-dimensional Alladi
rounding argument does not bound the adjacent divisor kernel: products of
the two moduli can exceed N and reach N^2. The exact small-prime reflection
is noninjective and does not preserve the original counting interval.
The long complementary term retains its input-dependent size condition
and side colour; neither marginal endpoint continuity nor fixed-residue
independence removes those weights. The already proved short-complement
selection remains limited to its selected range.

Also considered smoothing the complementary product cutoff and averaging
comparable double-prime multipliers. Smoothing leaves the component that
is invariant under the lower-prime colours, and a valid same-target
entropy argument was not obtained from comparable multipliers. No new
cancellation theorem was proved or assumed in this review.

The exact outstanding sufficient condition remains, for example,
  Tendsto (fun N => prefixMean (2*N) factorSign-prefixMean N factorSign)
    atTop (nhds 0).
Its implication to the conjecture is already checked in
SingleDyadicWindowCriterion. Its hypothesis has NOT been proved.
Spec.lean is unchanged with its original sorry. No proof or disproof is
available to submit.

## Further continuation: local divisor-block reflection check

Checked a proposed near-identity replacement for the earlier root reflection.
New module LocalReflectionCheck.lean, with saved olean and permitted axiom
check, defines
  reflectedInBlock Q n = Q*(n/Q)+(Q-1-n%Q).
It verifies the exact obstruction at n=8,Q=6:
  reflectedInBlock 6 8=9,
  P(8)=2<P(9)=3<P(10)=5.
Thus reflection within the existing divisor-product block swaps the chosen
2/3 divisibility marks but does not reverse the largest-prime comparison;
the reflected neighbor acquires the larger prime 5. This is only a
counterexample to an auxiliary pairing proposal, not to the conjecture.

An attempt to charge failed local reflections to larger winner labels was
not completed. With a fixed marked divisor pair the reflection is reversible,
but updating the mark to the new largest prime loses that simple pairing.
Allowing all prime factors makes divisor-product periods exceed the counting
interval; restricting to small factors loses the needed total logarithmic
mass. No injection, balanced multiplicity estimate, or contracting signed
transport bound was proved.

Spec.lean remains unchanged with its original sorry. The conjecture is
still unresolved in this development; no proof has been submitted.

## Continuation: exact adjacent-pair endpoint TV is arithmetically obstructed

NEW checked module Submission/PrimePairEndpointObstruction.lean (127 lines),
with saved .olean. All printed main axiom checks contain only propext,
Classical.choice, Quot.sound. No warnings, admissions, or unsafe evaluation.
Removed the temporary CheckPairTmp.lean.

This is an unconditional result about the ACTUAL adjacent maxPrimeFac law,
not an auxiliary sequence, but it is NOT a disproof of the conjecture.

Definitions use zero-based samples n=0,...,N-1, matching bothAboveSet:
  exactPrimePair n = (P(n),P(n+1));
  primePairProbability N t = #{n<N : exactPrimePair n=t}/N;
  primePairL1Distance M N is the full finite sum of absolute differences.
Both coordinates are bounded by max(M,N), so the finite sum covers the
entire support of both laws.

The arithmetic uniqueness lemma exactPrimePair_unique uses:
- P(n) and P(n+1) are coprime, as divisors of consecutive integers;
- equal ordered prime pairs at m,n imply m=n modulo P(n)*P(n+1);
- if that product is at least U, there can be no distinct m,n<U.

Consequently, if 2*N <= (B+1)^2, every pair represented in bothAboveSet B N
has mass exactly 1/N in the N-law and 1/(2*N) in the 2N-law. The pair image
is injective, giving the finite lower bound
  primePairL1Distance N (2*N) >= #bothAboveSet(B,N)/(2*N).

The PREVIOUSLY CHECKED two-band marginal estimate supplies
  #bothAboveSet(ceilPowerCutoff(21/40,N),N)/N >= 1/20
and the needed product inequality eventually. New main theorems:
  primePairL1Distance_dyadic_eventually_positive:
    eventually 1/40 <= primePairL1Distance N (2*N);
  primePairL1Distance_dyadic_not_zero:
    NOT Tendsto (N |-> primePairL1Distance N (2*N)) atTop (nhds 0).

Thus the recent exact ONE-coordinate total-variation continuity CANNOT be
extended to exact adjacent pair total variation. This is a sharper warning
than merely noting that the extension is unproved. It does not rule out
endpoint regularity for fixed coarse quantizations, bounded-rank pair tests,
or the actual comparison sign. Large exact-pair L1 discrepancy alone gives
no lower bound on the signed rise-minus-fall discrepancy.

Revisited the signed dyadic kernel/current and same-target entropy routes.
The existing large-product kernel already isolates atoms with reverse count
zero; sign cancellation among those atoms is still missing. Short intervals
of comparable prime multipliers do not resolve the entropy-scale selection
problem: the common source must be chosen before the good entropy scale,
and a source chosen as H*N varies with that scale. No valid diagonal entropy
recurrence, signed long-collision bound, or dyadic regularity was proved.

Spec.lean is unchanged, still with the original sorry, SHA256
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or disproof of the ORIGINAL conjecture is ready to submit.

## Further continuation: signed-current review after the pair-TV obstruction

Returned to the signed target, rather than extending the marginal results.
Reviewed the exact dyadic coboundary identity, the balanced reciprocal kernel,
and the loser-current collision expansion.

For loser primes above the square-root scale, the multiples of p in the
window have automatically p-smooth cofactors. This removes that particular
smoothness condition, but leaves the difference of prime/cofactor counts in
opposite residue classes modulo p. The modulus is above the range where the
existing fixed-modulus marginal estimate applies. Absolute collision bounds
still leave O(1) at macroscopic separations; positivity of the critical energy
provides the wrong one-sided inequality for the remaining signed cross term.
No cancellation estimate was obtained from these simplifications.

Also reconsidered deriving a same-target entropy recurrence with multipliers
in a narrow comparable prime interval. Making their endpoints close controls
rounding only after the multiplier scale is fixed. It does not justify
choosing the source as that scale times the prescribed target before the
entropy decrement selects its good scale. No new recurrence was established.

No new Lean theorem was claimed in this review. The latest checked result
remains PrimePairEndpointObstruction.lean. Spec.lean is unchanged and still
contains the original sorry; there is no complete proof or disproof to submit.

## New continuation: actual moving antisymmetric prime-pair witness

Completed Submission/PrimePairReversalObstruction.lean, with saved .olean.
It imports PrimePairEndpointObstruction. All printed main axiom checks use
only propext, Classical.choice, Quot.sound. No warnings or admissions.

The signed logarithmic-factorization review still leaves the prime-weighted
cutoff term: replacing the full Mangoldt divisor sum by log(n) does not
eliminate the ordered cutoff in the opposite-residue kernel. No new estimate
of that remainder was obtained. Also reviewed the dyadic edge-subdivision
identity: middle labels between endpoints preserve the coarse edge sign,
while outside labels create opposite-sign pairs. This pointwise identity
does not give an averaged contraction; the middle-label condition is still
correlated with the orientation.

The new checked result concerns a TOO-STRONG prospective uniform statement.
- exactPrimePair_reverse_impossible:
  if m,n<N and 2*N<=P(n)*P(n+1), then the ordered pair at m cannot be the
  reversal of the pair at n. Otherwise both coprime primes divide n+m+1,
  a positive integer strictly smaller than their product.
- primePairAsymmetryTest(B,N,a,b) is the indicator that (a,b) belongs to the
  image of bothAboveSet(B,N), minus the indicator for (b,a).
  It is antisymmetric and has absolute value at most one everywhere.
- Under 2*N<=(B+1)^2, the test on the actual sequence n<N equals precisely
  the indicator of bothAboveSet(B,N). Forward membership uses the ordered-
  pair uniqueness theorem; reverse membership is impossible by the lemma
  above. Its natural mean is exactly #bothAboveSet(B,N)/N.
- exists_moving_prime_pair_skew_with_positive_mean chooses
  B=ceilPowerCutoff(21/40,N). The PREVIOUS two-band lower bound gives a
  mean at least 1/20 eventually.

Thus uniform adjacent cancellation for ALL endpoint-dependent bounded
antisymmetric kernels on exact prime values is FALSE for the actual
arithmetic sequence. The witness depends on exact pair membership, not
only on the numerical order of the prime values. It need not factor through
any fixed finite quantization. It is therefore NOT a counterexample to the
original comparison-sign conjecture, nor to NaturalPrimeSkew's fixed finite-
alphabet statement with a prime-gap average and its explicit order of limits.

Spec.lean remains unchanged with its original sorry. No complete proof or
disproof of the original conjecture is ready to submit.

## Further continuation: periodic rough-factor cancellation does not remove the prime term

Rechecked VaughanRoughGrouping and VaughanSmoothAnnihilation against a
proposed fixed-cutoff smooth/rough summation. The mixed terms m>1 have the
already checked logarithm-affine dependence on the rough factor. However,
the m=1 term cannot be treated as an ordinary periodic rough-number weight.
The already checked vaughanLongFunction_rough states exactly
  Long(U,V,q)=Lambda(q)-log(q)
when minFac(q)>max(U,V), U,V>=1, q>0.
After division by log(q), this still contains Lambda(q)/log(q), the original
prime-power weight. Cancelling the periodic rough-number part therefore
leaves the prime-counting component, not a proof that the whole term is zero.
The exact semiprime coefficient -1 and its positive absolute reciprocal mass
remain consistent with this identity.

Considered iterating the divisor decomposition on rough composites. No
signed contraction or uniform bound was obtained: the short-divisor budget
and the free complementary variable's length still leave the critical
long-product region. No exchange of a fixed-cutoff limit with a moving
cutoff was assumed, and no unproved mixed-term tail estimate was used.

This review adds no new theorem. Recompiled PrimePairReversalObstruction;
its printed axioms remain propext, Classical.choice, Quot.sound. Spec.lean
is unchanged (same recorded checksum), still with sorry. The original
conjecture remains unresolved in this development.

## Further continuation: rough-part graph expansion review

Investigated a direct route from positive-power multiplier stability to
small antisymmetric adjacency averages. Grouping integers by roughPrimePart
turns a stable observable into a function on a weighted divisor graph.
A successful signed operator estimate here would avoid the N/p entropy
endpoint replacement, but no such estimate was established.

The cycle bookkeeping must distinguish nondegenerate affine compositions
from balanced ones. For a closed walk, multiplying the affine edge equations
can constrain the starting rough part when the product of the multipliers
is nontrivial. It does not eliminate balanced multiplier products, and it
does not estimate the signed mixed-orientation walks in an even matrix
moment. Those were already identified as a limitation in the earlier graph
review. Long natural-window paths from t to t+1 obtained through different
small dilations also produce balanced closed walks; no large-girth claim
was made. Bounding walk counts unsigned would lose the cancellation needed
for the antisymmetric operator.

Considered truncating smooth cofactors and increasing the moment length.
No parameter choice was proved to control both the nondegenerate walks and
the balanced signed walks. The specific chirp exclusion on positive-power
multiplier ranges does not supply the missing general inverse theorem.
No graph expansion or classification of all obstructions is being assumed.

No new Lean theorem or sufficient signed estimate resulted in this round.
Spec.lean remains unchanged with the original sorry. No proof/disproof of
the original conjecture is ready for submission.

## Further continuation: smoothing does not align the natural transfer endpoint

Reviewed ExponentialDensityCriterion, BoundedLaplaceTauberian, and
ActualPrimeComparisonTransfer. The exponential equivalence is already
proved and was not duplicated. Exponential smoothing of the natural
transfer still rescales the adjacent weight by the selected prime. Taking
a source proportional to the selected entropy scale again changes the
source law before the good scale has been chosen. No same-target smoothed
transfer was proved.

The Fourier--Laplace Tauberian theorem also keeps its continuous boundary
extension hypothesis explicit. No arithmetic boundary extension for the
comparison sign was obtained. Uniform cancellation on growing logarithmic
windows alone cannot be substituted for that hypothesis or for the
unnormalized exponential limit.

No new sufficient estimate or Lean theorem resulted in this review.
Spec.lean is unchanged with its original sorry; no valid settlement is
available to submit.

## Further continuation: critical-energy equality is not an upper bound

Rechecked whether winner/loser conservation gives a strict contraction of
the critical energy. The checked O(1/N) difference of the two energies only
identifies their possible limits. The collision formula leaves the same
signed off-diagonal term in both. Nonnegativity provides the known lower
bound on that term, not the upper bound needed by
`density_of_dyadicSignedCollisions_limsup`.

Ordering each edge from the smaller prime to the larger does not resolve
this: the coefficients are signed, and an ascending two-edge path can have
the same divergence as a single longer ascending edge while carrying a
different total signed comparison count. No strict energy contraction or
bound on the macroscopic collisions was proved. No new theorem was added.
Spec.lean remains unchanged with sorry; no valid settlement is ready.

## Further continuation: external/library check and natural-system review

Tried the Erdős problem page again; the request failed with DNS resolution.
A search of the available Mathlib and FormalConjecturesForMathlib sources
found no theorem for this maxPrimeFac natural-density statement. No claim
about the latest external research status is inferred from that failure.

Reconsidered whether the natural spectral results force reversal of the
whole adjacent law. Absence of infinite-order spectral atoms and cancellation
under prime-gap averaging do not imply that the gap-one covariance has zero
imaginary part. A symmetric extension to negative integers also cannot be
used to identify the positive-half word law with its reversal: it only makes
the mixture symmetric. No new componentwise invariance or same-target
transfer theorem was proved.

No new Lean theorem or sufficient arithmetic estimate was obtained.
Spec.lean remains unchanged with its original sorry. There is no complete
proof or disproof to submit.

## Further continuation: fixed-source localization audit

Tested localizing each prime's observable inside a single common source
interval so that division by p would reach a prescribed endpoint N.
A source interval of length X and a retained subinterval of length p*N
still require a normalization factor X/(p*N). The existing common-source
entropy error does not have a corresponding uniform gain. Choosing a
smaller input tolerance does not repair this without justification, since
the permitted range of entropy scales depends on that tolerance.

Reviewed the componentwise mixture/shifted-prefix transfer theorems. They
provide absolute control averaged under their stated endpoint laws, not
uniform control of a particular scale-dependent diagonal component. No
valid bound on the localization loss or new diagonal entropy recurrence
was obtained. No new Lean theorem was added.

Spec.lean is unchanged and still contains the original sorry. There is no
completed proof or disproof of the conjecture to submit.

## New continuation: a FIXED exact-prime antisymmetric kernel can have natural bias

Completed Submission/FixedPrimePairSkew.lean, with saved .olean. All printed
main axiom checks use only propext, Classical.choice, Quot.sound. No warnings,
admissions, or unsafe evaluation. Namespace Erdos371.FixedPrimePairSkew.

This strengthens the earlier endpoint-dependent witness to a SINGLE kernel
C : Nat -> Nat -> Real, fixed before taking any natural endpoint limit.
It is still NOT the numerical order-comparison kernel of Erdős 371.

Construction:
- For each previous cutoff B, choose an endpoint E(B)>=B+2 such that the
  proportion of n<E(B) with P(n)<=B, multiplied by 2, is <=1/40. This uses
  bounded_maxPrimeFac_hasDensity_zero via density_iff_count.
- At the same endpoint require the already proved two-band large-pair
  proportion >=1/20 and the product inequality needed by the local witness.
- Define band(0)=0 and band(j+1)=E(band(j))+1. The bands are strictly
  increasing. bandIndex(p) is the first j with p<=band(j+1).
- kernel(a,b) uses primePairAsymmetryTest at endpoint E(band(j)), with
  j=bandIndex(max(a,b)). The symmetric choice of j preserves antisymmetry;
  the test is unit bounded.
- At E(band(j)), the fixed kernel agrees with the local positive witness
  whenever max(P(n),P(n+1))>band(j). Any discrepancy is bounded by twice
  the indicator P(n)<=band(j), so its normalized error is <=1/40.
- Therefore kernel_mean_positive proves mean >=1/40 at every selected
  endpoint. endpoints_atTop proves these endpoints tend to infinity.
- kernel_mean_not_zero and exists_fixed_prime_pair_skew_not_zero conclude
  that the natural mean of this fixed antisymmetric exact-prime kernel does
  NOT tend to zero.

The result is about the ACTUAL maxPrimeFac sequence, not a substitute
stable sequence. It rules out reversal for arbitrary fixed bounded kernels
on the infinite set of exact prime values. Although the output has only
three values, the kernel need not factor through a fixed finite partition
of its two prime inputs. There is no contradiction with the fixed-finite-
alphabet prime-gap results, the fixed finite-range max-multiplicative
symmetry theorem, or the special order-kernel conjecture.

Spec.lean remains unchanged with its original sorry, checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No proof or disproof of the ORIGINAL conjecture is ready to submit.

## Continuation: ordered prime-band and high-moment review

Revisited PowerSeparatedPrimeKernel, ShortDivisorPrimeKernel, NaturalPrimeSkew,
and the single dyadic criterion. The surviving signed long Vaughan kernel
still requires a thin inverse-residue estimate with prime weights. A
full-range exponential-sum estimate alone does not retain the small density
N/(P*Q) of the inverse interval in the large-product range. No new bound was
proved.

The context summary understated the continuous moment obstruction. The
existing ContinuousPartitionPerturbation.md already contains a mathematical
PD(1)-marginal perturbation argument, with the polynomial kernel identities
checked in ContinuousKernelObstruction.lean. This argument must not be
repeated as an unexplored reconstruction route. Its PD probability-space
embedding remains unformalized, and it is not an arithmetic counterexample.

Also reviewed whether even graph moments could use unsigned upper bounds
instead of full orientation cancellation. The directed divisor-cycle bound
still does not count mixed product-degenerate walks. The existing balanced
four-cycle example has positive traversal-orientation product and all actual
comparisons rising. No sufficient high-moment bound, spectral estimate, or
contraction was established. No new theorem was added in this review.

Spec.lean is unchanged with its original sorry. The original conjecture is
not proved or disproved; no valid completed proof is available to submit.

## Continuation: rational-grid entropy audit

Considered putting the small-multiplier-invariant quantized labels on rational
grids to keep a prescribed base endpoint N. For p fixed, write the p phase
means using pairs L(p*n+a), L(p*n+a+p), 0<=a<p. Exact multiplier absorption
identifies phase a=0 with the adjacent mean at N. Averaging all phases is
exactly the unrestricted gap-p mean at p*N, by division with remainder.
Thus the endpoint change reappears as a phase-conditioning issue; no bound
on that conditional pair-law difference follows from the one-coordinate
marginal estimates. In particular, equal phase marginals do not rule out
different three-label cyclic pair circulations.

A putative fixed-finite-grid entropy argument would use only stability under
fixed rational multipliers, whereas the existing chirp obstruction already
shows why such stability alone is inadequate. The positive-power multiplier
range is extra information, but no recurrence exploiting that growing range
at the required same target endpoint was established. No new theorem was
added or unproved independence assumption introduced.

Spec.lean remains unchanged, with its original sorry. There is no completed
proof or disproof of the original conjecture to submit.

## New checked continuation: mixed cycles in narrow multiplicative intervals

Completed Submission/NarrowMixedPrimeCycle.lean. The final compilation checks
all printed main axioms against propext, Classical.choice, Quot.sound; there
are no admissions. Spec.lean is not modified.

Unconditional polynomial family, for t,h>=1:
  R=4(t+1)h+1, S=4th+1, V=2(2t+1)h+1,
  Q=8t(t+1)h+2t+1;
  a=2tR, b=Q, c=2tV, d=(2t+1)R.
The identities are
  a+1=Q, b+1=2(t+1)S, c+1=(2t+1)S, d+1=2(t+1)V,
  a*b*(c+1)*(d+1)=(a+1)*(b+1)*c*d.
Also 0<c<a<b<d and t*d<(t+1)*c. Thus product-degenerate
mixed four-cycles, as integer product identities, occur in arbitrarily
narrow fixed-relative-width intervals. No primality is needed for these
polynomial identities or bounds.

The theorem actual_labels identifies their ACTUAL maxPrimeFac labels when
R,S,V,Q are prime; this primality is a hypothesis, not an asserted infinite
prime-tuple theorem. The specialization t=101,h=660 verifies all four primes
using kernel-checked norm_num:
  R=269281, S=266641, V=267961, Q=54394763.
The indices are a=54394762,b=54394763,c=54128122,d=54664043.
All lie in [54128122,54664043], of width <1%. All four labels exceed
the square root of the upper endpoint. Their product exceeds
4*(54664043+1)^3, but the mixed endpoint-product difference is zero.
The actual edge comparisons consist of one rise (at a) and three falls
(at b,c,d), despite two forward and two backward traversal orientations.

Names: endpoint_product_equality, indices_ordered, narrow_interval,
actual_labels, concrete_labels, narrow_actual_cycle_obstruction,
narrow_cycle_comparisons.

SCOPE: this refutes blanket deterministic exclusion or comparison-sign
balance of mixed cycles even in a 1% interval. It does NOT estimate their
number, disprove a signed spectral bound, or provide an asymptotic
counterexample to the conjecture. In particular Q is almost the endpoint;
the example does not bypass the existing near-linear-tail removal.
Neither infinitely many prime specializations nor a positive-density
family of such cycles is claimed.

The original natural-density conjecture remains unresolved. Spec.lean
retains its original sorry; no complete proof/disproof is ready to submit.

## Continuation: smooth-progression/character estimate audit

Revisited PrimeWinnerCongruenceRuns, OddCharacterSkew, and the critical-energy
replacement. The signed row/current can be written using smoothness of
neighbors of multiples of p, hence opposite-residue progression counts.
No equidistribution theorem at the required growing modulus and cofactor
range has been established. The odd-character orthogonality identities do
not themselves estimate the retained prime-weighted hyperbolic sum.

Considered whether a short-character-sum bound on the cofactor interval could
suffice. In the upper-half range its length N/p can be an arbitrarily small
fixed power of p. Neither a fixed-modulus theorem nor an unweighted complete
sum supplies the needed uniform error after summing prime moduli. No Burgess
or stronger bound was proved or used as an unproved assumption; no sufficient
critical-energy estimate resulted. No new theorem was added in this review.

Spec.lean is unchanged with its original sorry; the conjecture remains
unsettled in this development.

## Continuation: short-interval multiplicative-function route

Considered whether short-interval results for bounded nonnegative
multiplicative functions could improve the prime-gap spectral step for
actual moving smooth-number indicators. Unlike arbitrary finite-label
arrays, each smoothIndicator B is a nonnegative multiplicative function.
No such deep short-interval theorem has been formalized or invoked here.

The proposed use still needs careful separation of two issues. Uniform
short-interval control of individual indicators would not itself give
residue-conditioned PAIR independence. Even granting a sufficiently uniform
unconditioned prime-gap skew estimate at varying source endpoints, the
entropy transfer still has to identify the phase-zero pair mean with that
unconditioned mean at a prescribed target N. Existing entropy decrement
selects a scale for one source; it does not select the diagonal source p*N
for each selected prime p. No new recurrence or bound for this conditioning
error was obtained. No claim that a short-interval theorem alone settles
the conjecture is being made.

No new Lean theorem or sufficient signed estimate resulted. Spec.lean
remains unchanged with its original sorry; no valid settlement is ready.

## New checked continuation: products of losing integers

Completed Submission/LosingProductComparison.lean with a clean compile and
saved olean. All printed main axioms are restricted to propext,
Classical.choice, Quot.sound. Spec.lean is unchanged.

For n,m>1 with the same winning prime p, put a=losingNumber n and
b=losingNumber m. Define r=losingProductIndex n m by
  r=a*b-1 if the two comparisons have the same orientation,
  r=a*b   otherwise.
The new exact theorem losingProductIndex_structure proves
  1<r,
  losingNumber r=a*b,
  p <= primeWinner r,
  factorSign r = -(factorSign n * factorSign m).
The proof uses the losing-number residue (+1 for falls, -1 for rises)
modulo p, and P(a*b)=max(P(a),P(b))<p. losingProductIndex_loser
identifies this exact new loser label. The new winner need not equal p:
losingProduct_winner_increases checks n=m=3 gives r=15, winner 5.

weighted_losingProduct_square retains every ordered pair, including the
diagonal, in the finite identity
  (sum_{n in S} w(n) factorSign(n))^2
    = -sum_{n,m in S} w(n)w(m) factorSign(losingProductIndex n m)
for any finite S all of whose members are >1 with winner p.

Also proved exact multiplicity control for p>2:
- losingNumber_injective_at_winner: the loser integer determines the input
  comparison within a fixed winner class. Otherwise p divides both neighbors
  of the loser, forcing p|2.
- losing_product_fibre_card_le: the number of ordered pairs from S with
  loser product L is at most L.divisors.card.
- losingProductIndex_fibre_card_le: the fibre over an output r has size at
  most (losingNumber r).divisors.card. Its loser is the exact product, so
  there is no need to sum the divisor counts at r and r+1.

LIMITATION: these identities do not give the missing signed estimate.
Inputs near N map near N^2 with nonuniform factorization multiplicities.
The divisor bound does not justify replacing that pushforward by uniform
natural or harmonic sampling, nor dropping its smoothness/winner conditions.
No upper bound sufficient for fixed-dyadic critical-energy decay or scalar
cancellation has been obtained. Higher-product smoothness decay has not been
shown to dominate the representation multiplicities.

A proposed complete fixed-prime cancellation route was checked against the
older Pell/S-unit investigations in this log; it supplies no new bound.
No completeness or uniform truncation theorem for smooth pairs is assumed.

The original conjecture remains unresolved in this development. Spec.lean
still has its original sorry; there is no valid proof/disproof to submit.

## Continuation: doubling and reciprocal-packing checks

Read the existing dyadic pointwise relation and its explicit obstructions
before attempting a contraction. DyadicIterationCheck shows cancellation
can reappear after further subdivision; DyadicSeparatedBias also rules out
using doubling invariance plus finite separated labels alone. No arithmetic
contraction or natural-prefix estimate was obtained from the actual doubling
relation. The fixed-dyadic cancellation condition remains unproved.

Considered a reciprocal packing bound for p-smooth integers in a nonzero
residue modulo p: an integer >=p with P(n)<p has a divisor between p and p^2.
After retaining the quotient, an unsigned progression majorant suggests an
O(log^2(p)/p) reciprocal tail bound. This was mathematical analysis only;
no new Lean theorem for that bound was added. It is not a signed progression
estimate and does not control the product pushforward in the required way.

For the actual winner currents, PrimeCurrentAbsoluteBudget already proves
the stronger O(log(p)/p) absolute incidence bound by dividing a p-labelled
integer by p. Squaring that bound with critical weight p leaves a prime sum
of order log^2(p)/p, not a summable majorant or a vanishing dyadic energy.
Likewise, subcritical weighted l2 convergence cannot be promoted to the
critical weight without a new uniform estimate. No such promotion was made.

No new sufficient estimate or Lean theorem resulted in this continuation.
The latest completed module remains LosingProductComparison.lean. Spec.lean
is unchanged with its original sorry; no proof or disproof is ready.

## Continuation: cofactor exchange and cycle-count check

Reviewed CofactorDescent and CofactorDescentPreimage before trying a new
exchange of the winning prime and its cofactor. The exact inverse already
retains a prime linear form and a simultaneous smooth linear form. No
estimate allowing their signed orientation difference to be discarded was
obtained. No primality-only replacement of the inverse was used.

Also considered a high-moment estimate for the directed prime-label matrix
on primes P near N^(1-delta), with cofactors H near N/P. This remains an
unproved spectral estimate, not a consequence of the existing cycle
identities. A cycle with 2k edges has TWO cofactor variables per edge, so a
naive enumeration has H^(4k), not H^(2k), possibilities before divisibility
and compatibility constraints. Solving the linear system for its prime
labels does not justify the missing H^(2k) saving. Integrality and the
small determinant restriction must still be counted. Product-degenerate
mixed cycles are also not automatically absent. No trace bound or signed
large-product estimate sufficient for the conjecture resulted.

No new Lean theorem was added in this continuation. Spec.lean retains its
original import, unchanged statement, and original sorry. There is no valid
settlement ready to submit.

## New checked continuation: constant multiplicity in the upper-half range

Completed Submission/LosingProductSidon.lean and
Submission/LosingProductSidonBoundary.lean. Both compile cleanly with saved
oleans; all printed main axiom dependencies are restricted to propext,
Classical.choice, Quot.sound. Spec.lean remains unchanged.

The new bound is stronger than the earlier divisor-count fibre bound:
- short_affine_product_unique: if |x|,|y|,|z|,|w|<=K and 4K<p, then equality
  of (px+1)(py+1) and (pz+1)(pw+1) identifies the unordered coefficient pairs.
  Expanding first forces p to divide a sum difference of absolute value <p;
  then the coefficient sums and products coincide.
- short_abs_affine_product_unique: the same holds for absolute affine
  products when p>2. A negative signed-product equality would force p|2.
- losingNumber_short_affine_certificate represents the actual losing
  integer as |px+1|, with |x| its winning cofactor.
- short_losing_product_unique identifies unordered pairs of actual inputs
  with common winner p, provided all winning cofactors are <=K and 4K<p.
- short_losing_product_fibre_le_two and
  short_losingProductIndex_fibre_le_two give cardinality <=2.
- upper_half_losingProductIndex_fibre_le_two: for inputs in S below N, all
  >1 with common winner p>2, the condition 4N<p^2 ensures this fibre bound.

The boundary file proves a genuine family of collisions, not merely an
identity with uncertified prime-factor labels. For positive a,b,c,d with
  cd=ab+1, p=a+b+c+d prime,
one has
  ap+1=(a+c)(a+d), bp+1=(b+c)(b+d),
  cp-1=(a+c)(b+c), dp-1=(a+d)(b+d).
Every displayed factor is positive and <p. Thus the comparisons at ap,bp
are actual falls with winner p, and those at cp-1,dp-1 are actual rises
with winner p; their losing products and their product-output indices agree.
Names: shifted_product_collision_factorizations and
shifted_product_collision_data. No infinite prime-values assertion is made.

losing_product_collision_eleven checks p=11 and inputs (11,55),(21,32),
both with product output 671. They lie below 56 and 2*56<11^2.

losing_product_collision_near_four certifies a collision even with
398*N<100*p^2 (i.e. 3.98*N<p^2). Its data are
  p=4063447, a=1010807, b=1020917, c=1010908, d=1020815,
  N=b*p+1=4148442120900.
The four original comparisons are ap,bp,cp-1,dp-1. Both pairs are
nondiagonal and not reorderings of one another. Primality of p is verified
by norm_num; maxPrimeFac facts come from the general factorizations, not
from unproved numerical factorization. The construction was obtained from
a determinant-one parametrization, not an unstructured search.

LIMITATION: constant fibre multiplicity alone does not settle the signed
count. Products of inputs near N lie near N^2 in a sparse, constrained set.
There is still no justified replacement by uniform natural or harmonic
sampling, nor a sufficiently strong signed estimate on that image. These
results do not establish fixed-dyadic cancellation or critical-energy decay.

The original conjecture remains unresolved; Spec.lean retains its original
sorry. There is no valid proof/disproof ready to submit.

## Continuation: exact winning cofactor after losing-number multiplication

Analyzed the next possible use of the constant-multiplicity result. For
original common winner p, let k,l be the winning cofactors and let s,t be
the real comparison signs, regarded as the integers +1 or -1. The original
losers are pk-s and pl-t. Their product is L, and the new comparison has
sign -st, hence winning integer
  W=L-st=p*(p*k*l-k*t-l*s).
The parenthesized integer is positive for the nontrivial original inputs.
Therefore the actual new winner is max(p,P(p*k*l-k*t-l*s)), and winner
preservation is equivalent to smoothness of that bilinear cofactor.
These calculations were mathematical analysis in this continuation; no new
Lean theorem for them was added.

No estimate for the resulting signed sum was obtained. The original two
smoothness certificates must still be retained, as must the condition on
the new bilinear cofactor if winner preservation is used. The upper-half
Sidon bound controls multiplicities but not sampling: for a fixed common
prime, the product image is much smaller than the full corresponding
winner class at the squared scale. Thus one cannot replace its weighted
current by the ordinary current of that larger class. No assertion of
uniform image coverage, independence, or a negligible escape contribution
was made.

The latest checked new modules remain LosingProductSidon.lean and
LosingProductSidonBoundary.lean. Spec.lean is unchanged with its original
sorry. No valid proof or disproof of the conjecture is ready.

## Continuation: direct signed quadratic-sieve audit

Reviewed QuadraticResidueSieve, ProductCutoffSelberg,
PrimeLoserCollisionPowerSieve, and OddCharacterSkew for a way to estimate
the signed second moment directly, without separate positive and negative
collision counts. No sufficient estimate resulted.

The available Selberg quadratic form majorizes a NONNEGATIVE avoidance
count. Its diagonal basis formula and polynomial cutoff error do not give
an o(N) approximation error for replacing the signed smoothness indicators
in the critical collision sum. Such a replacement would require control
of the majorant error with the retained weights. Taking the upper bound
termwise can discard the opposite-sign contributions and is not a proof
of signed-energy decay. No unproved small majorant error was used.

Odd-character orthogonality cancels the even-character part exactly, but
the remaining prime/cofactor character sum is still unestimated. The
initial-cofactor interval's exact character energy alone does not bound
the retained prime-weighted hyperbolic sum at the required scale.

No new Lean theorem or sufficient signed estimate was produced in this
continuation. Spec.lean remains unchanged with its original sorry; the
original conjecture is not settled in this development.

## Continuation: scalar order-kernel route

Revisited the weaker scalar target rather than the stronger absolute
prime-current criterion. SmoothedComparison already proves that the actual
sign is approximated in Cesaro L1 by
  (P(n+1)-P(n))/(P(n+1)+P(n)),
and proves equivalence of cancellation of this rational kernel to the
original density conjecture. No new bound for its signed mean was obtained.

Considered phases of the unscaled logarithmic prime ratio. Even a proposed
fixed nonzero-frequency cancellation would not by itself control the sign
integral near frequency zero; a uniform low-frequency estimate would still
be required. No such fixed-frequency or uniform low-frequency theorem was
proved here. The existing normalized clipped-log and additive-score
criteria were reviewed without changing their quantifiers or claiming
cancellation for their unproved signed averages.

No new Lean module or sufficient estimate resulted in this continuation.
Spec.lean remains unchanged with its original sorry. The conjecture has
not been settled in this development.

## New checked continuation: the FULL product image has summable reciprocals

Completed Submission/LosingProductSparsity.lean (imports existing auxiliary
modules). It compiles cleanly with a saved olean. All five printed main
axiom checks list only propext, Classical.choice, Quot.sound. Removed the
temporary CheckProductSparseTmp.lean. Spec.lean is unchanged.

The result is global: no balanced-input, short-cofactor, or upper-half
restriction is required.

Definitions and theorems:
- absoluteWinnerMass p = sum_n ||primeWinnerHarmonicTerm p n||.
- absoluteWinnerMass_rpow_bound uses the existing absolute incidence budget
  O(log p/p) to bound it by primeCurrentBudgetConstant*p^(-3/4).
- summable_absoluteWinnerMass_sq proves summability over all natural p.
- commonWinnerPairReciprocal(n,m) is 1/n*1/m if the two winners agree, and
  zero otherwise (zero denominators have the usual Lean value zero).
- summable_commonWinnerPairReciprocal proves that this function is summable
  on all ordered pairs. The proof uses nonnegative Tonelli and the exact
  sum of each prime-class product as absoluteWinnerMass(p)^2. No signed
  cancellation is used.
- losingProductOutputs is the set of ALL r=losingProductIndex n m with
  n,m>1 and equal winners.
- losingProductIndex_reciprocal_bound proves
    1/losingProductIndex n m <= 2/(n*m)
  on those inputs.
- summable_losingProductOutputs_reciprocal proves summability of
    losingProductOutputs.indicator (fun r => 1/r).
  One actual preimage is chosen per output; that selection is injective
  into the ordered-pair domain. The proof does not assume globally bounded
  fibre multiplicities.
- losingProductOutputs_hasDensity_zero follows by the checked elementary
  harmonic Tauberian lemma applied to the image indicator.

SCOPE: this is density ZERO of the auxiliary product image, not a density
statement about all rising comparisons and not a disproof of Erdős 371.
It makes precise why even the constant-fibre result cannot turn the product
identity into uniform sampling at the squared scale. Critical prime weights
are not covered by the summable unweighted pair budget; no critical signed
energy estimate or natural half-density proof follows here.

The original conjecture remains unresolved. Spec.lean has its original
sorry and unchanged statement/import. No valid settlement is ready to submit.

## New checked continuation: structured winner preservation

Completed Submission/LosingProductWinnerPreservation.lean. It compiles
cleanly with a saved olean; both printed main axiom checks list only
propext, Classical.choice, Quot.sound. Spec.lean is unchanged.

- cyclotomic_cube_identities and cyclotomic_sixth_identities give the
  algebraic factorizations underlying the examples.
- losingProduct_preserves_winner_cubic verifies the opposite-sign pair
  n=4912, m=5832 with common winner p=307, product output r=28652616,
  and winner(r)=307. It also verifies 4*5833<307^2.
- losingProduct_preserves_winner_same_sign verifies a same-sign example
  from k=71 and p=k^2+k+1=5113:
    n=71^6-1, m=72^6-1, r=5112^6-1.
  Both inputs are falls with winner p, n<m, 8m<9n, n+1<m,
  both loser labels have square <p, and the output winner is still p.
  Explicit certificates use
    71^6-1 = 5113*(70*72*4971),
    72^6-1 = 5113*(71*73*7*751),
    5112^6-1 = 5113*(5111*7*13*349*823*79*163*2029).
  All displayed cofactor factors are below p. The checked proof uses
  these factorizations rather than trial division of the large outputs.

Scope: these finite examples refute blanket strict-increase assertions,
including a same-sign version with comparability and strong label separation.
They do NOT refute an almost-all escape estimate or an asymptotic estimate
allowing any exceptional family. The same-sign example is not in the
upper-half range 4N<p^2. No infinite prime-family assertion was made.

Also inspected NaturalPrimeSkew, NaturalPrimeGapTransfer, and the single
dyadic-window criterion. Their established conclusions still do not give
the missing same-target adjacent cancellation. No quantifier exchange or
new unconditional endpoint theorem was obtained.

The original conjecture remains unresolved. Spec.lean still has its original
sorry; there is no proof or disproof ready to submit.

## New checked continuation: monotone quantization is not square-root cancellation

Completed Submission/MonotoneInsertionVariation.lean with a clean compile
and saved olean. All three printed main axiom checks use only propext,
Classical.choice, Quot.sound. The temporary CheckInsertionTmp.lean was removed.

- monotone_label_change_budget: for pointwise nondecreasing natural-valued
  arrays bounded by Q at the final stage, the total number of coordinate
  changes over T stages and N coordinates is at most Q*N.
- Model labels ramp(n)=n%3 and raised(n)=3 when 5 divides n, ramp(n) otherwise
  satisfy ramp<=raised<=3, and the update is supported on multiples of 5.
- insertion_increment: their comparison-skew increment on [0,15K) is -2K.
- no_square_root_bound_from_monotonicity: no fixed natural C bounds the
  square of every model prefix increment by C*N.

Scope: this is a model obstruction to obtaining a square-root saving from
finite quantization and monotonicity alone. The model is NOT an actual
largest-prime-factor cutoff, and the theorem does NOT refute a square-root
or averaged estimate using additional arithmetic hypotheses. In particular
it is not a density counterexample and not a disproof of Erdős 371.

The hoped-for entropy/insertion shortcut still requires a genuine arithmetic
cancellation estimate. No such estimate was obtained in this continuation.
Spec.lean remains unchanged with its original sorry, and no settlement is
ready for submission.

## Continuation: chirp endpoint model rederived, then recognized as redundant

Re-derived a circle-valued moving-frequency model exp(i*t*log n), proving a
positive adjacent skew at endpoint 64*t and simultaneous recurrence at each
fixed integer multiplier via compactness of the countable torus. Both new
files compiled with permitted axioms. On cross-checking the FULL earlier
log, MultiplicativeChirpObstruction and the subsequent exact/finite-label
countermodels already prove stronger results, and AllPolynomialChirpExclusion
already handles exclusion on every positive-power multiplier range.

This was a REDERIVATION, not a new mathematical advance. Removed the redundant
ArchimedeanPhaseSkew.lean and RecurrentArchimedeanModel.lean, their saved oleans,
and the temporary CheckPhaseTmp.lean and CheckPhaseRecurrenceTmp.lean. No
existing module depends on those removed files.

Important checkpoint reminders: the log around lines 990-1160 records the
original chirp model and multiplier exclusions; around lines 5120-5210 it
records exact finite-label, three-label, and power-stable countermodels;
around lines 9170-9220 it records the all-polynomial-range chirp exclusion.
Do not repeat these constructions or treat their exclusion as an inverse
theorem. There is no proof that they exhaust obstructions.

The max-multiplicative arithmetic cancellation gap remains open. No new
sufficient signed bound resulted. Spec.lean is unchanged with its original
sorry; the original conjecture is not settled.

## Continuation checkpoint: natural transfer and unweighted winner energy re-audit

Re-read NaturalPrimeSkew, NaturalPrimeGapTransfer, PrimeLogQuantization,
AllPolynomialChirpExclusion, PrimeWinnerEnergy, PrimeWinnerNonadjacent, and
LocalMinimumDeletionEnergy, and cross-checked the earlier research log.
No new arithmetic estimate or Lean theorem resulted.

- Prime-gap cancellation in a natural empirical word law still does not
  align the adjacent endpoint N/p with N.
- Exact positive-power multiplier stability of primeQuantLabel is present,
  but there is no proved inverse theorem making it a same-endpoint transfer.
- The unweighted energy criterion is conditional. The exact formula
  E(N)=N-2*A(N)+2*R(N) leaves the nonadjacent signed remainder R(N)
  uncontrolled; the sufficient inequality R(N)<=A(N) was not proved.
- The existing local-minimum deletion formula does not give a contraction.

This checkpoint records an audit only, not new progress toward settlement.
Spec.lean remains unchanged with its original sorry and checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No valid proof or disproof is ready to submit.

## Continuation checkpoint: analytic boundary and affine descent review

Reviewed BoundedIkehara, NeighborSmoothCancellationCriterion,
CofactorDescent, CofactorDescentPreimage, FixedMaxMultiplicativeSymmetry,
DivisorCycleBound, and the earlier damping and fixed-marginal obstruction
records. No new Lean theorem or sufficient signed estimate was obtained.

The bounded Wiener--Ikehara theorem remains conditional on a continuous
pole-subtracted boundary extension; no such extension was established for
the largest-prime comparison series. Cofactor descent continues to retain
simultaneous primality and smoothness conditions in its inverse rows.
Neither a Farey/affine reformulation nor grouping by the smaller cofactors
provided a signed contraction or a uniform summable error.

The fixed max-multiplicative reversal theorem was not promoted to a moving-
cutoff theorem. Likewise, low-product inclusion information and fixed
marginal laws were not treated as determining the full joint law. The
existing obstruction notes already explain why that inference is invalid.

This is an unsuccessful strategy review, not additional mathematical
progress. Spec.lean is unchanged; there is no complete proof or disproof.

## NEW checked continuation: negative winner congruence runs

Completed Submission/NegativeWinnerCongruenceRuns.lean, importing the
existing PrimeWinnerCongruenceRuns. It compiles cleanly with a saved olean.
All four printed main axiom checks list only propext, Classical.choice,
Quot.sound. Spec.lean is unchanged.

- If k+1 divides p-1 and k+1<p, then P(k*p+1)<p.
- Define negativeRunQuotient(p,k)=p+(p-1)/(k-1). When k>=2,
  k<p, and k-1 divides p-1, the exact factorization is
      (k-1)*negativeRunQuotient(p,k)=k*p-1.
  The quotient lies strictly above p and at most 2*p. Consequently
  P(k*p-1)>p iff this quotient is prime.
- negative_congruence_run_pair_contribution: for prime p under both
  divisibility hypotheses, the two p-winner contributions adjoining k*p
  total -1 when the quotient is prime, and zero otherwise.
- primeWinnerSum_negative_congruence_run: when every j<=K+1 divides p-1,
  the whole current at K*p+1 is minus the number of prime quotients for
  2<=k<=K. This retains the primality tests; no prime-tuples assertion is
  made or assumed.
- primeWinner_31_187_counts certifies three rises and five falls.
- primeWinnerSum_67801_339006 certifies current -4, using K=5, p=67801,
  and the prime quotients 135601, 101701, 90401, 84751.
- not_primeWinnerSum_ge_neg_one refutes the proposed universal bound -1.

Scope: these are finite arithmetic counterexamples to a one-sided current
bound, NOT a disproof of Erdos 371 and NOT an asymptotic obstruction to
cancellation. They complement the earlier positive-congruence-run identities.

Development note: kernel evaluation of the larger primality goals exceeded
recursion depth (and raising it too far caused a process stack overflow).
The final proof instead uses norm_num primality certificates and explicitly
expands the four-element cofactor set. No elevated recursion limit or unsafe
evaluation is present in the final auxiliary module.

The original conjecture remains unsettled. Spec.lean retains its original
sorry and checksum 34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No valid proof or disproof is ready to submit.

## NEW checked continuation: almost-all-prime zero currents at fixed cofactors

Completed Submission/AlmostAllPrimeCofactorCurrents.lean. It compiles with a
saved olean. All three printed main axiom checks use only propext,
Classical.choice, Quot.sound. Spec.lean is unchanged.

- primeWinnerSum_whole_endpoint_eq_loser: for prime p, the winner and loser
  currents agree exactly at every endpoint J*p+1 (the flux boundary vanishes).
- badCofactorPrimes K X consists of primes X<p<=2X for which some J<=K has
  nonzero current at J*p+1.
- badCofactorPrimes_subset_loser_image: for X>0 this set is contained in
  image primeLoser (bothAboveSet X ((2*K+1)*X)). A nonzero loser sum forces
  an incident edge; its two labels exceed X. No p>K assumption is needed.
- bothAbove_linear_count_scaled_log_tendsto: for each fixed positive integer
  c, #bothAboveSet(X,c*X)*log X/X tends to zero. This uses the existing
  two-large-prime sieve with u=log c/log(c*X), retaining its uniformity in u.
- badCofactorPrimes_scaled_count_tendsto and
  badCofactorPrimes_prime_proportion_tendsto: the bad set is o(X/log X), hence
  is an asymptotically zero proportion of primes in (X,2X], by the checked PNT.

This supplies genuine simultaneous exact-zero currents for almost every
prime in a fixed cofactor range. It does not allow K to grow like a positive
power of X and does not settle the original density conjecture. No sufficient
interior signed estimate or energy bound has been obtained. Spec.lean still
retains its original sorry and is not a valid completed submission.

Post-theorem bridge audit: the whole-endpoint flux equality does not iterate
into an unsigned contraction. The loser of one edge is a smaller prime label,
not a new independent whole-multiple endpoint for a larger-prime current.
Directed label cycles can support circulation with zero divergence, so zero
boundary correction alone does not cancel the interior sum. The new fixed-K
prime-proportion limit was not interchanged with a power-growing K. No new
sufficient signed estimate resulted from this audit.

## NEW checked continuation: growing logarithmic cofactor zero currents

Refactored AlmostAllPrimeCofactorCurrents to expose its already-used uniform
finite bound as bothAbove_linear_scaled_log_bound. Its fixed-cofactor results
are unchanged and recompiled successfully.

Completed Submission/LogGrowingPrimeCofactorCurrents.lean. It compiles cleanly
with a saved olean; all three printed axiom checks use only the permitted
propext, Classical.choice, Quot.sound.

For every 0<=a<1, let K(X)=floor((log X)^a). Then the primes X<p<=2X for which
some J<=K(X) has primeWinnerSum p (J*p+1) nonzero have cardinal o(X/log X),
and hence proportion tending to zero among primes in the band. This is an
explicit growing range, not an interchange of a fixed-K limit. The uniform
finite sieve estimate is applied with c=2*K(X)+1 and gives the bound

  #bad * log X/X <=
    16*C*(log 2+a*log log X+1)^2/(log X)^(1-a)
      + 4*2^65*(log X)^(a+1)/sqrt X.

Both displayed terms tend to zero for a<1. The result strengthens the
fixed-cofactor almost-all-prime result but still treats only exponent-one
boundary cutoffs. It does not bound the signed currents in the power-sized
cofactor interior, and it does not settle Erdos 371.

Spec.lean remains unchanged with its original sorry and checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No valid final proof or disproof has been produced.

## Continuation after logarithmic cofactor growth: interior signed-energy audit

Reviewed PrimeWinnerEnergy, PrimeWinnerEnergyIncrement,
PrimeWinnerNonadjacent, PrimeWinnerSubpowerEnergy,
PrimeLoserCollisionPowerSieve, and the earlier weighted-compactness and
energy-obstruction records. This review produced no new Lean theorem.

The exact decomposition E(N)=N-2*A(N)+2*R(N) still leaves the signed
nonadjacent remainder R(N) unbounded at the needed scale. Inserting a
power-growing cofactor cutoff into the available unsigned collision bound
retains a positive power of N; it does not yield the subpower-loss near-linear
energy hypothesis. The winner/loser identity is conservation, not an unsigned
contraction. No inference from the fixed or logarithmically growing exact-zero
prime-current theorem to the power-cofactor interior was made.

The descending prime-insertion and smooth-neighbor reflection viewpoints
were reconsidered, but neither supplied a sign-definite cross-term estimate.
This is an unsuccessful strategy review, not additional progress toward a
settlement. Spec.lean is unchanged and still contains its original sorry.

## NEW checked continuation: simultaneous smooth-neighbor runs around prime multiples

The proposed prefix-nonnegativity shortcut was immediately recognized as
already disproved in PrefixBalanceObstruction (N=3913, 1955 rises and 1958
falls). It was not treated as new work or used as an assumption.

Completed Submission/PrimeSmoothNeighborRuns.lean. It compiles cleanly with
a saved olean. All five printed main axiom checks use only propext,
Classical.choice, Quot.sound. No admissions or unsafe evaluation are used.

The earlier LogGrowingPrimeCofactorCurrents module was refactored to expose
its uniform two-large-factor cover estimate and its scaled-count limit as
logPower_bothAbove_linear_eventual_scaled_bound and
logPower_bothAbove_linear_scaled_count_tendsto. Its original three results
are preserved, recompiled, and still pass their axiom checks.

New arithmetic results:
- roughNeighborPrimes K X records primes X<p<=2X with some 1<=k<=K for which
  P(k*p-1)>p or P(k*p+1)>p.
- If K<=X and X>0, this set is contained in
  image primeLoser (bothAboveSet X ((2*K+1)*X)). At k*p the label is exactly
  p, so the adjacent exceptional edge really has loser p.
- Avoiding this exceptional set implies BOTH P(k*p-1)<p and P(k*p+1)<p
  at every k in the range. Equality is excluded by consecutive-factor
  inequality, not ignored.
- For every 0<=a<1 and K(X)=floor((log X)^a), the exceptional count is
  o(X/log X), and its proportion among dyadic-band primes tends to zero.
- Every sufficiently large dyadic interval contains a prime with the full
  smooth-neighbor run.
- logPowerCofactorCutoff_dyadic_domination compares exponents a<b at p and X
  uniformly for X<p<=2X.
- roughNeighborPrimesAtOwnScale_proportion_tendsto proves the zero exceptional
  proportion even for K(p)=floor((log p)^a), rather than K(X).
- infinitely_many_prime_smooth_neighbor_runs: for each 0<=a<1, infinitely
  many primes p satisfy P(k*p-1)<p and P(k*p+1)<p simultaneously for all
  1<=k<=floor((log p)^a).

This is stronger than zero winner current: larger neighboring factors are
absent, not merely canceled. It remains a logarithmic-cofactor boundary
result. It does not prove cancellation in the power-cofactor interior and
is not a proof or disproof of Erdos 371. Spec.lean remains unchanged with
its original sorry and checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.

## NEW checked continuation: nearly logarithmic smooth-neighbor runs

Completed Submission/CriticalPrimeSmoothNeighborRuns.lean. It compiles
cleanly with a saved olean. All five printed main axiom checks use only
propext, Classical.choice, Quot.sound. No admissions or unsafe evaluation.

Definitions:
  W_r(X) = log X / (1+log log X)^r,
  K_r(X) = floor(W_r(X)).

- For r>=0, the weight is eventually between 1 and log X, the cutoff is
  positive and <=X, and K_r(X) tends to infinity.
- criticalPrimeRunWeight_dominates_logPower: for every a<1 and every fixed
  M, eventually M*(log X)^a <= W_r(X). Thus this is genuinely larger than
  every fixed sublinear logarithmic power considered previously.
- The two-large-factor cover satisfies the explicit estimate
    #bothAboveSet(X,(2*K_r(X)+1)*X)*log X/X
      <= 4*C*(2*log 2+1)^2/(1+log log X)^(r-2)
         +4*2^65*(log X)^2/sqrt X.
  Both terms tend to zero when r>2.
- criticalPrimeRun_roughNeighborPrimes_scaled_count_tendsto and
  criticalPrimeRun_roughNeighborPrimes_proportion_tendsto: the primes
  X<p<=2X having any larger neighboring factor at k*p+-1 for 1<=k<=K_r(X)
  form an o(X/log X) set and have prime-relative proportion tending to zero.
- criticalPrimeRunCutoff_dyadic_domination: if 0<=s<r then, uniformly over
  X<p<=2X, eventually K_r(p)<=K_s(X).
- criticalRoughNeighborPrimesAtOwnScale_proportion_tendsto gives the same
  zero exceptional proportion with the nearly logarithmic range K_r(p)
  measured at the prime itself.
- infinitely_many_critical_prime_smooth_neighbor_runs: for every r>2 there
  are infinitely many primes p for which BOTH P(k*p-1)<p and P(k*p+1)<p
  hold for all 1<=k<=floor(log p/(1+log log p)^r).

This is a stronger unconditional smooth-neighbor boundary result, not a
settlement of Erdos 371. The cofactor range still grows more slowly than
any positive power of p. No signed interior estimate has been obtained.
Spec.lean is unchanged with its original sorry and checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.

## NEW checked continuation: one-logarithm saving from the smaller-prime band

Completed two new modules, both compiling cleanly with saved oleans:
  Submission/NarrowPrimeLoserSieve.lean
  Submission/NarrowBandPrimeSmoothRuns.lean
All eight printed main axiom checks use only propext, Classical.choice,
Quot.sound. No admissions or unsafe evaluation.

This is a genuine arithmetic refinement of the cofactor cover, not just a
change of the asymptotic cutoff. Retaining X<primeLoser(n)<=2X matters:
if n=a*q and n+1=b*s, then n<=2*X*max(a,b). The sieve can therefore use a
cofactor-dependent endpoint, rather than the common endpoint H*X.

NarrowPrimeLoserSieve:
- narrowLoserCofactorSet uses endpoint 2*X*max(a,b) for each cofactor pair.
- narrowLoserCofactorSet_bound uses the existing weightedSlopeSum_bound,
  giving main term 16*exp(19)*X*H*(1+log H)/log(z+1)^2 and error
  2*H^2*(z+1)^64, for H<=X.
- narrowLoserSet_subset_cofactors proves the actual finite cover.
- roughNeighborPrimes_card_le_narrowLoser retains the smaller-prime band.
- With z=floor(X^(1/128)), narrowLoserSet_scaled_log_bound proves
    #narrowLoserSet(X,H*X)*log X/X
      <= C_band*H*(1+log H)/log X
         +2^65*H^2*log X/sqrt X,
  where C_band=16*exp(19)*128^2.
  The main term has only one logarithm in H, not two.

NarrowBandPrimeSmoothRuns:
- For K_r(X)=floor(log X/(1+log log X)^r), the exceptional scaled count is
  bounded by
    4*C_band*(2*log 2+1)/(1+log log X)^(r-1)
      +16*2^65*(log X)^3/sqrt X.
- Thus every r>1 now gives an exceptional count o(X/log X), and a proportion
  tending to zero among primes X<p<=2X. This improves the prior r>2 range.
- narrowBand_criticalOwnScale_proportion_tendsto measures the cutoff at p
  itself, using the already-checked dyadic domination lemma.
- infinitely_many_narrowBand_prime_smooth_neighbor_runs proves infinitely
  many primes p satisfy BOTH P(k*p-1)<p and P(k*p+1)<p for every
  1<=k<=floor(log p/(1+log log p)^r), for every r>1.

Scope: this still concerns a nearly logarithmic cofactor boundary. It is not
cancellation in the power-cofactor interior and does not prove/disprove the
natural-density conjecture. Spec.lean is unchanged with its original sorry
and checksum 34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.

## NEW checked continuation: one-logarithm saving from the smaller-prime band

Completed two new modules, both compiling cleanly with saved oleans:
  Submission/NarrowPrimeLoserSieve.lean
  Submission/NarrowBandPrimeSmoothRuns.lean
All eight printed main axiom checks use only propext, Classical.choice,
Quot.sound. No admissions or unsafe evaluation.

This is a genuine arithmetic refinement of the cofactor cover, not just a
change of the asymptotic cutoff. Retaining X<primeLoser(n)<=2X matters:
if n=a*q and n+1=b*s, then n<=2*X*max(a,b). The sieve can therefore use a
cofactor-dependent endpoint, rather than the common endpoint H*X.

NarrowPrimeLoserSieve:
- narrowLoserCofactorSet uses endpoint 2*X*max(a,b) for each cofactor pair.
- narrowLoserCofactorSet_bound uses the existing weightedSlopeSum_bound,
  giving main term 16*exp(19)*X*H*(1+log H)/log(z+1)^2 and error
  2*H^2*(z+1)^64, for H<=X.
- narrowLoserSet_subset_cofactors proves the actual finite cover.
- roughNeighborPrimes_card_le_narrowLoser retains the smaller-prime band.
- With z=floor(X^(1/128)), narrowLoserSet_scaled_log_bound proves
    #narrowLoserSet(X,H*X)*log X/X
      <= C_band*H*(1+log H)/log X
         +2^65*H^2*log X/sqrt X,
  where C_band=16*exp(19)*128^2.
  The main term has only one logarithm in H, not two.

NarrowBandPrimeSmoothRuns:
- For K_r(X)=floor(log X/(1+log log X)^r), the exceptional scaled count is
  bounded by
    4*C_band*(2*log 2+1)/(1+log log X)^(r-1)
      +16*2^65*(log X)^3/sqrt X.
- Thus every r>1 now gives an exceptional count o(X/log X), and a proportion
  tending to zero among primes X<p<=2X. This improves the prior r>2 range.
- narrowBand_criticalOwnScale_proportion_tendsto measures the cutoff at p
  itself, using the already-checked dyadic domination lemma.
- infinitely_many_narrowBand_prime_smooth_neighbor_runs proves infinitely
  many primes p satisfy BOTH P(k*p-1)<p and P(k*p+1)<p for every
  1<=k<=floor(log p/(1+log log p)^r), for every r>1.

Scope: this still concerns a nearly logarithmic cofactor boundary. It is not
cancellation in the power-cofactor interior and does not prove/disprove the
natural-density conjecture. Spec.lean is unchanged with its original sorry
and checksum 34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.

## NEW checked continuation: positive prime fraction at the limiting sieve scale

Completed Submission/PositivePrimeFractionSmoothRuns.lean. It compiles
cleanly with a saved olean. All four printed main axiom checks use only
propext, Classical.choice, Quot.sound; no admissions or unsafe evaluation.

- scaledPrimeRunCutoff(c,X)=floor(c*log X/(1+log log X)).
- For 0<c<=1, the exceptional rough-neighbor count satisfies
    #bad*log X/X <= A*c + 16*2^65*(log X)^3/sqrt X,
  where A=4*C_band*(2*log 2+1). This retains the small constant c in the
  main term, rather than replacing it by one.
- scaledPrimeRunCutoff_dyadic_domination: uniformly for X<p<=2X,
  eventually K_{c/2}(p)<=K_c(X). No varying-exponent argument is used.
- scaledPrimeSmoothBand(c,X) contains primes in (X,2X] with BOTH
  P(k*p-1)<p and P(k*p+1)<p for all 1<=k<=K_c(p).
- exists_positive_prime_fraction_log_div_loglog_smooth_runs proves that
  there is an absolute c>0 such that, in EVERY sufficiently large dyadic
  prime band, at least half of its primes belong to scaledPrimeSmoothBand.
  The proof chooses the auxiliary constant 1/(16*(A+1)), halves it for
  endpoint transfer, and retains the explicit error and PNT count lower bound.
- exists_infinitely_many_log_div_loglog_prime_smooth_runs gives the resulting
  infinitude at a fixed positive constant times log p/(1+log log p).

Scope: the factor 1/2 in the new result is a lower bound for a fraction of
PRIMES with a special smooth-neighbor property. It is NOT the natural density
statement in Spec.lean. The uncontrolled power-cofactor interior remains;
no valid proof or disproof of Erdos 371 has been obtained. Spec.lean is
unchanged, still has its original sorry, and has checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.

## NEW checked scope result: subpower-cofactor centers and incident edges are sparse

Completed Submission/SubpowerCofactorBoundary.lean. It compiles cleanly
with a saved olean; all five printed main axiom checks use only propext,
Classical.choice, Quot.sound. No admissions or unsafe evaluation.

- prime_log_level_exception_hasDensity_zero turns the existing positive-level
  non-atomicity theorem into density zero for an event eventually trapped in
  every neighborhood of that level.
- normalizedPrimeLog_near_one_of_small_cofactor uses the exact factorization
  P(n)*primeCofactor(n)=n and logarithms to show that cofactor<=n^delta
  forces |log P(n)/log n-1|<=delta.
- subpower_cofactor_centers_hasDensity_zero: if K(n)<=n^delta eventually for
  every delta>0, then {n>1 : primeCofactor(n)<=K(n)} has natural density zero.
- polylog_cofactor_centers_hasDensity_zero gives the explicit c*(log n)^a
  bound, for arbitrary real c,a.
- shortPrimeMultiples_hasDensity_zero: the full set of k*p with p prime,
  k>0, k<=c*(log p)^a is density zero for c,a>=0; no good-prime restriction
  is necessary.
- density_zero_shift_one and density_zero_incident_edges handle the two
  incident comparison indices without silently identifying shifted counts.
- primeRunCenters_hasDensity_zero_of_polylog_bound retains an arbitrary
  integer-valued cutoff K(p) eventually bounded by c*(log p)^a. Small primes
  contribute only a bounded initial set, handled by a finite supremum.
- scaledPrimeRun_centers_hasDensity_zero and
  scaledPrimeRun_edges_hasDensity_zero apply directly to the exact cutoff
  used in PositivePrimeFractionSmoothRuns, including BOTH incident edges.

IMPORTANT SCOPE CONSEQUENCE: all centers and all incident edges in the recent
prime smooth-neighbor run theorems occupy a natural density-zero subset of
the integers. Their prime-relative abundance is genuine but does not provide
positive-density coverage of the original comparison problem. Further
logarithmic boundary refinements should not be presented as addressing the
unresolved power-cofactor interior.

This is a rigorously checked limitation, not a proof/disproof of Erdos 371.
Spec.lean is unchanged and retains its original sorry and checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.

## Continuation: polynomial-multiplier transfer review — no settlement

Reviewed SingleDyadicWindowCriterion, PrimeWinnerSubpowerEnergy,
NaturalPrimeGapTransfer, StableLabelPrimeTransfer,
ComponentwiseShiftedPrefixTransfer, and ThreeLabelPowerStableBias.
No new sufficient unconditional signed estimate was obtained.

Important terminology distinction: the power stability in
exists_three_label_power_stable_rise_deficit is L(n^r)=L(n), for r>0.
Its multiplier stability is only k<=j at selected endpoints N_j; it does
NOT establish stability for all k<=N_j^delta with fixed delta>0.
It therefore does not rule out an argument exploiting the actual
primeQuantLabel_mul polynomial multiplier range. Conversely, that actual
identity alone has not been turned into natural adjacent cancellation.

The checked transfer retains adjacent endpoint N/p and gap-p endpoint N.
Selecting a source p*N after an entropy scale is selected is still not
justified by its quantifiers. Narrow-band or componentwise transfer does
not supply the missing common-endpoint estimate. This review repeats a
known obstacle; it is not a new theorem or a proof of impossibility.

Spec.lean is unchanged with its original sorry. No complete proof or
negation proof has been obtained, and no proof has been submitted.

## NEW checked continuation: non-between harmonic sums have infinite variation

Completed Submission/NonBetweenHarmonicVariation.lean (215 lines), importing
only DyadicHarmonicCancellation. It compiles cleanly with a saved olean.
All five printed main axiom checks use only propext, Classical.choice,
Quot.sound. No admissions or unsafe evaluation are used.

- nonBetweenHarmonicTerm(n) is the increment of nonBetweenHarmonicSum at n.
- If 2*n+1 is prime, factorBetween(n) is false: its middle prime factor
  exceeds both endpoint prime factors.
- Therefore if 2*n+3 is prime, |nonBetweenHarmonicTerm(n)|=1/(n+1).
- not_summable_abs_nonBetweenHarmonicTerm follows from divergence of prime
  reciprocals. The proof embeds all primes except 2 through n |-> 2*n+3,
  compares reciprocal weights, and handles the removed prime by eventual
  equality. No asymptotic prime-counting estimate is needed.
- nonBetween_total_variation_tendsto_atTop: the total variation of the
  bounded harmonic partial sums tends to infinity.
- not_summable_nonBetween_positive / negative and their atTop versions:
  both positive and negative increments have divergent sums. These follow
  from the exact Jordan-part identities and the existing bound |H_N|<=3.
- nonBetweenHarmonicSum_increases_and_decreases: beyond EVERY endpoint
  there are both increases and decreases.
- Explicit corollaries rule out eventual monotonicity and antitonicity.

CRITICAL INTERPRETATION: Lean's Summable for real-valued families means
unconditional summability. Its failure, infinite variation, and arbitrarily
late changes of sign do NOT rule out conditional convergence of ordered
partial sums. That conditional convergence is exactly the property still
needed in density_iff_nonBetweenHarmonicSum_converges. This module therefore
rules out proposed absolute-convergence or monotone-convergence shortcuts;
it is neither a proof nor a disproof of the original conjecture.

Spec.lean is unchanged, retains its original sorry, and has checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof/disproof is ready for submission.

## Continuation: cofactor-order and harmonic-window audit — no new theorem

Rechecked maxPrimeFac_rise_iff_cofactor_fall in Explore and the exact inverse
formulas in CofactorDescentPreimage. The pointwise reversed order of the
cofactors does not imply equality of their oriented counting measures.
The inverse still requires primality of r+p*k and smoothness of the affine
cofactor (b*r +/- 1)/p+b*k. No signed estimate comparing these two orientations
was obtained. This is a known gap, not a new obstruction theorem.

Also checked the actual definitions behind the uniform shifted-prefix
results, rather than relying only on their descriptions. The sampling
weights are 1/(A+i+1), not 1/(i+1), and the hypothesis is divergence of their
sum. Thus a fixed-ratio window [N,2N] does not satisfy that hypothesis.
There is no direct specialization of these results to the missing dyadic
window cancellation.

No new Lean theorem was added during this continuation. The latest new
checked module remains NonBetweenHarmonicVariation. Spec.lean is unchanged
and retains its original sorry. No valid proof or disproof is ready.

## Continuation: factorization-moment constraint audit — no new estimate

Checked PartitionObstruction, FixedMarginalPartitionPerturbation,
RefinedPartitionObstruction, and the existing continuous perturbation notes.
Exact mass conservation is already present: every partition has the fixed
one-integer total mass. It is not an omitted extra condition that restores
uniqueness from the low-total-mass mixed inclusion data. The existing
MergeKernelObstruction also reaches the upper-half largest-part region.
These remain auxiliary models, not arithmetic counterexamples.

Rechecked the upper-half prime kernel and polynomial Vaughan reduction.
The surviving opposite-progression sum is prime-weighted. Complete-modulus
cancellation or a count of its unsigned incidences does not estimate its
signed long-divisor term at the required natural scale. No new weighted
large-modulus estimate was proved.

This continuation added no new Lean theorem. Spec.lean is unchanged with
its original sorry. The original conjecture and its negation remain
unproved in this development; no valid submission is ready.

## NEW checked continuation: relative harmonic half on the non-between event

Completed Submission/NonBetweenRelativeHarmonicHalf.lean (242 lines), importing
NonBetweenHarmonicVariation. It compiles cleanly with a saved olean, and all
four printed main axiom checks use only propext, Classical.choice, Quot.sound.
No admissions or unsafe evaluation are used.

Definitions:
- T_N = nonBetweenHarmonicMass N = sum_{1<=n<=N, not factorBetween n} 1/n.
- R_N and F_N are the same harmonic sums with actual rise/fall conditions.
- H_N is the existing signed nonBetweenHarmonicSum.

Results:
- Exact identities T_N=2*R_N-H_N=2*F_N+H_N and monotonicity of T_N.
- T_N tends to infinity, using the prior prime-reciprocal variation result.
- Finite errors |R_N/T_N-1/2| and |F_N/T_N-1/2| are <=3/(2*T_N) when T_N>0.
- nonBetween_relative_harmonic_rises_half / falls_half prove the resulting
  limits. The denominator is the subevent's OWN harmonic mass, not N.
- In an arbitrary window A..B with positive intrinsic mass T_B-T_A, the
  rising fraction error is <=3/(T_B-T_A). Consequently the relative fraction
  tends to half along any windows whose intrinsic mass tends to infinity.
- nonBetween_dyadic_window_mass_le_one proves T_(2N)-T_N<=1 for EVERY N.
- nonBetween_dyadic_mass_not_tendsto_atTop proves that no choice of endpoints,
  including a sparse subsequence, can satisfy the growing intrinsic-mass
  premise for fixed dyadic windows.

Scope: this is a genuine relative harmonic balance result, but it does not
establish the unnormalized fixed-dyadic cancellation or convergence of H_N.
Its explicit fixed-window obstruction prevents using this new half theorem
as the original natural-density half assertion. No proof/disproof of the
original conjecture has been obtained. Spec.lean is unchanged with its
original sorry and checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.

## NEW checked continuation: divisor-bounded mixed product completions

Completed Submission/ConsecutiveRatioFibres.lean (238 lines), importing
FormalConjecturesUtil. It compiles cleanly with a saved olean. All six printed
main axiom checks use only propext, Classical.choice, Quot.sound. No
admissions or unsafe evaluation are used.

The directed-cycle product bound was found to be already present in
DivisorCycleBound; no duplicate of that theorem was added. Instead this
continuation counts completions in the product-degenerate mixed cases that
MixedPrimeCycleObstruction showed cannot be excluded.

General finite results:
- If 0<R<L and L*c*d=R*(c+1)*(d+1), the two positive factors
    ((L-R)*c-R), ((L-R)*d-R)
  have product L*R. Mapping a pair to the first factor is injective on the
  solution set, giving cardinality <=(L*R).divisors.card for ANY finite set
  of positive solutions. No endpoint occurs in the divisor majorant.
- If 0<R<L and L*(c+1)*d=R*c*(d+1), then (L-R)*d<R and
    ((L-R)*c+L)*(R-(L-R)*d)=L*R.
  This gives the analogous quotient-fibre bound. Swapping c,d extends the
  result to any positive unequal L,R.

Specializations, with c,d in Icc 1 N:
- balanced_four_product_completions handles
    (a+1)(b+1)cd=ab(c+1)(d+1).
- alternating_four_product_completions handles
    (a+1)b(c+1)d=a(b+1)c(d+1), retaining the essential a!=b hypothesis.
- three_forward_product_completions handles
    (a+1)(b+1)(c+1)d=abc(d+1).
All three have the explicit bound tau(a*b*(a+1)*(b+1)).
- alternating_equal_ratio_iff and alternating_equal_ratio_completions
  handle the omitted a=b case: it is exactly c=d, giving N completions.

Scope: these are finite arithmetic bounds on the product-equality part of
mixed four-edge configurations, valid without primality assumptions. They
are NOT a bound for the full signed prime-label matrix moment or winner
energy. A count over the first two edges, and control of nonzero product
imbalances with their signs, remain necessary. No tau(n)=n^o(1) estimate was
formalized in this module, and no near-linear energy bound is asserted.

Spec.lean is unchanged with its original sorry and checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
There is still no complete proof or disproof ready for submission.

## Checked continuation: subpower completion bounds above a large shared label

Completed and saved oleans for three modules:

- DivisorSubpower.lean proves
    tau(n)^k <= ((k! * 2^k)^(2^k)) * n  (n != 0),
  and consequently, for each d and epsilon>0, eventually uniformly for
  n<=N^d, tau(n)<=N^epsilon. The proof uses prime-factorization products,
  binomial bounds, and real-power growth, not an unproved divisor estimate.
- ConsecutiveRatioSubpower.lean combines this with the previously checked
  ratio-fibre injections. Balanced and three-forward four-edge product
  completions are uniformly <=N^epsilon. Alternating completions have
  this bound ONLY off the a=b diagonal; that diagonal has N solutions.
- LargeEndpointDegenerateWalks.lean counts initial pairs a,b in [1,N]
  sharing a largest prime factor >B at prescribed endpoint offsets, with
  the second offset at most one. An injection using b's cofactor gives
    #pairs <= N*((N+1)/(B+1)+1).
  Summing the completion bounds gives the same quantity times N^epsilon.
  If beta<=1 and N^beta<=B+1, all three (off-diagonal where needed)
  completion majorants are <=3*N^(2-beta+epsilon), eventually uniformly.

The last file's new power-bound section was compiled successfully after
replacing a simplifier-sensitive addition step with push_cast/linarith.
All its printed main axiom checks contain only propext, Classical.choice,
Quot.sound. No admission or unsafe evaluation was added in these modules.

SCOPE: these are product-EQUALITY completion majorants. The product-
INEQUALITY walks and their signs remain uncontrolled. No full matrix
moment or near-linear winner-energy bound follows. In particular, the
naive fourth-moment argument would need P>N^(3/4) to exclude the nonzero
product differences but P<N^(2/3) for the resulting bilinear saving;
those requirements do not overlap. Additional closure conditions have
not yet been used to improve this parameter mismatch.

Spec.lean still has the unchanged original theorem and sorry. No genuine
proof or disproof of the original natural-density assertion is available.

## Final review in this continuation: remaining cycle closure gap

Reviewed the actual-label closures in MixedPrimeCycleObstruction and
NarrowMixedPrimeCycle against the new completion majorants. No additional
uniform counting factor was obtained. In particular, the known balanced
mixed cycles prevent replacing the product-equality contribution by an
empty-set claim. The nonzero product-difference signed contribution also
remains unbounded at the strength required for a density proof.

This continuation completed the pending auxiliary bound, not the original
conjecture. It supplies no valid replacement for Spec.lean's sorry and no
negation of that theorem. The original statement and import were preserved.

## Checked continuation: the crude cycle-moment exponent gap persists

Added Submission/CycleMomentExponentBarrier.lean, importing
FormalConjecturesUtil. It compiles with a saved olean; the printed main
axiom checks use only propext, Classical.choice, Quot.sound.

For every integer k>1 it proves
  k/(k+1) < 1-1/(2*k).
If beta >= 1-1/(2*k), the normalized exponent from the particular crude
trace budget N^k/P^(k-1), P=N^beta, satisfies
  beta*(k+1)/(2*k)-1/2 >= (k-1)/(4*k^2) > 0.
Consequently the associated normalized power budget tends to infinity.
This is an algebraic check of ONE proposed argument, not a claim that the
actual matrix moment is this large, nor an obstruction to stronger signed
estimates. No general high-moment arithmetic bound was supplied or assumed.

Also reviewed whether the determinant relations ap-bq=+/-1 permit a
prime-free operator estimate. The existing complete reciprocal estimates
still do not control the necessary prime-weighted long sum. No such
operator estimate was proved. Reconsidering rational near-unit dilations
and smooth-multiplier grids likewise did not remove the phase-conditioning
or endpoint-normalization issues documented earlier.

The original density conjecture remains unresolved here. Spec.lean is
unchanged with its original sorry. None of these auxiliary results is a
valid replacement for the requested final proof or disproof.

## Further continuation: max-multiplication and same-endpoint review

Reviewed the exact max-under-multiplication identity, the fixed versus
moving max-multiplicative models, and the cofactor descent formulas. No
new same-endpoint signed estimate was obtained. Absorbing small or smooth
multipliers is a pointwise identity on the sampled multiples; it does not
identify their conditional adjacent law with the unrestricted law at the
same natural endpoint. The inverse cofactor-descent weights still include
prime progression counts and smoothness conditions, so they cannot be
replaced by uniform harmonic weights without a new theorem.

Also reconsidered the high-prime determinant matrix ap-bq=+/-1. The
available incidence and complete reciprocal bounds do not supply the
required signed estimate over all polynomial prime ranges. No unproved
operator estimate was used, and no new Lean theorem is claimed from this
review. The original Spec.lean statement and sorry remain unchanged.

## Further continuation: audit of target-shaped declarations

Searched the existing Lean modules for HasDensity(1/2) declarations and
reviewed their premises. No unconditional theorem with the original target
was found: the relevant results still assume dyadic regularity, signed
smooth-neighbor cancellation, prime-current tightness, or an energy bound.
The unconditional half-density statements for auxiliary additive scores
are not statements about maxPrimeFac.

Reviewed FixedMaxMultiplicativeSymmetry as well. Its finite label function
is fixed before the natural endpoint limit. Applying it to moving
primeQuantLabel cutoffs would require uniformity that its type does not
provide. Finite fixed clipping also collapses both prime labels into the
top class, so it cannot approximate the original order test in natural
mean. No limit interchange or uniform approximation was proved here.

No new theorem or sufficient signed estimate resulted from this audit.
Spec.lean remains unchanged, and the original conjecture is still not
settled in this work.

## Further continuation: additive-score phase cancellation review

Reviewed AdditiveLogScores, including its exact completely multiplicative
phase and sine-autocorrelation identity. No uniform natural cancellation
of these phases was proved. The normalized phase depends on N, and
fixed-function statements cannot be substituted without uniformity.
Small-frequency estimates alone also do not recover the sign: the
frequency range needed to resolve small score differences must be retained.
The identity is a reduction, not the missing arithmetic cancellation.

A renewed external check of the official problem page failed at DNS
resolution; no research-status claim is inferred from that failure.
No new Lean theorem resulted, and Spec.lean is unchanged with its sorry.

## New checked continuation: mixed-cycle dichotomy and narrow odd-cycle bound

Added two modules with saved oleans, compiling without warnings. Their
printed main axiom checks contain only propext, Classical.choice,
Quot.sound. No admissions or unsafe evaluation were used.

1. Submission/MixedDivisorCycleDichotomy.lean imports DivisorCycleBound.
   endpoint_divisor_cycle_dichotomy permits arbitrary endpoints a_i,b_i
   between n_i and n_i+1, with p_i|a_i and p_{sigma(i)}|b_i. It proves:
     product(a_i)=product(b_i), OR
     product(p_i)<=(N+1)^k-N^k,
   when all n_i<=N. Both product-difference orientations are handled.
   mixed_divisor_cycle_dichotomy specializes this to Bool traversal
   directions and the bound k*(N+1)^(k-1). Repeated edges/labels are allowed;
   their multiplicities are retained. The actual-largest-prime versions
   show that a larger label product forces product equality, not that the
   mixed walk is absent. A uniform cutoff version uses
     k*(N+1)^(k-1)<(B+1)^k.

2. Submission/NarrowMixedCycleBalance.lean imports the first module.
   consecutiveLogRatio_bounds proves
     1/(n+1)<=log((n+1)/n)<=1/n  for n>0.
   mixed_equal_product_log_balance proves equality of the forward and
   backward logarithmic increment sums from endpoint-product equality.
   narrow_equal_product_traversals_balanced proves equal traversal COUNTS
   when all n_i lie in [L,N], L>0, and k*(N+1-L)<L. The proof bounds each
   logarithmic increment between 1/(N+1) and 1/L; an excess traversal
   cannot be offset by all the allowed increment variation.
   narrow_equal_product_card_even is a consequence. Hence the actual
   narrow odd-cycle product bound holds for arbitrary mixed orientations:
     product(source largest-prime labels)<=k*(N+1)^(k-1).

SCOPE: traversal balance is not balance of the numerical prime comparisons.
The existing narrow balanced even examples are fully compatible with these
new theorems. They do not supply a signed even-moment estimate or repair the
previous trace-budget exponent gap. No original density proof follows.

Spec.lean remains unchanged, with checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff,
and still contains the original sorry. No proof or disproof is ready.

## New checked continuation: genuine closed four-walk counts and their diagonal

Added Submission/ClosedFourDegenerateCounts.lean (327 lines), importing
LargeEndpointDegenerateWalks and MixedDivisorCycleDichotomy. It compiles
without warnings and has a saved olean. All five printed main axiom checks
contain only propext, Classical.choice, Quot.sound.

Definitions use finite sigma types to encode actual prime-label closure:
- balancedClosedDegenerateFourWalks: traversal pattern ++--, with all four
  prime labels>B and the exact endpoint-product identity.
- alternatingClosedDegenerateFourWalks: pattern +-+-, likewise, including
  the immediate-backtracking a=b case.
- balancedClosedFourWalks and alternatingClosedFourWalks omit the product
  identity but retain actual largest-prime-label closure and all bounds.

Finite results:
- Balanced degenerate count <= balancedEndpointDegeneracies B N 1 0.
- Alternating off-diagonal count <= alternatingEndpointDegeneracies B N 1 1.
- For a=b, product equality gives c=d. Actual closure additionally gives
  P(a)=P(c)>B. The map (a,a,c,c) -> (a,c) injects this entire diagonal into
  commonLargeEndpointPairs B N 0 0. Thus its count is
    <=N*((N+1)/(B+1)+1),
  not the unrestricted N completions for every base pair.
- The full alternating degenerate count is at most the off-diagonal
  majorant plus that shared-label pair bound.
- Uniformly for epsilon>0 the two counts are bounded respectively by
    N^epsilon*N*((N+1)/(B+1)+1),
    (N^epsilon+1)*N*((N+1)/(B+1)+1).

The two explicit Fin 4 cycle specializations of the prior dichotomy prove
that 4*(N+1)^3<(B+1)^4 forces product equality. Consequently the raw and
degenerate walk sets coincide above this threshold. Finally, for
3/4<beta<=1 and epsilon>0, eventually uniformly in B with N^beta<=B+1,
  balancedClosedFourWalks.card <=3*N^(2-beta+epsilon),
  alternatingClosedFourWalks.card <=6*N^(2-beta+epsilon).
These last statements really count all actual closed walks of those two
traversal types in the stated high-label regime.

SCOPE: no matrix trace expansion, operator estimate, or original density
proof is asserted. The previously checked exponent mismatch persists:
this regime is not the range where the crude trace-to-bilinear estimate
would give the required saving. The nonzero product-difference contribution
at lower labels remains uncontrolled. Spec.lean is unchanged with its sorry.

## New checked continuation: explicit full harmonic-current L2 rate

Added Submission/PrimeCurrentQuantitativeL2.lean, importing
PrimeCurrentL2Convergence and UniformPrimeCurrentHead. It compiles cleanly
with a saved olean. All four printed main axiom checks contain only
propext, Classical.choice, Quot.sound.

- primeCurrentSquaredError(N) is the full sum over all natural prime labels
  of (rawPrimeWinnerHarmonic(p,N)-primeWinnerHarmonicLimit(p))^2.
- primeCurrentSquaredError_head_tail proves, for every B,N,
    squaredError(N) <= primeCurrentHeadError(B,N)^2
                      + tailConstant*(B+1)^(-1/4).
  The finite part uses sum of squares <= square of the L1 sum. The tail
  splits the existing p^(-3/2) majorant as p^(-1/4)*p^(-5/4), retaining
  an explicit summable constant rather than merely dominated convergence.
- primeCurrentSquaredError_exp_scale specializes B=ceil(exp(t)) when
  t>0, log(3)<=t, and t^2=log N. It bounds the full squared error by
    rateConstant*(1+t)^2*exp(-(log(2)/32)*t).
- primeCurrentSquaredError_stretched_exp_bound absorbs the polynomial:
  eventually squaredError(N) <=
    rateConstant*exp(-(log(2)/64)*sqrt(log N)).
- primeCurrentSquaredError_log_power_zero gives, for every fixed natural k,
    (log N)^k*squaredError(N) -> 0.
- stretched_exp_sqrt_log_times_rpow_atTop checks the limitation of this
  bound: for every delta>0 and every real c,
    N^delta*exp(-c*sqrt(log N)) -> infinity.
  This is about the majorant, NOT a lower bound on the actual error.

This is a genuine quantitative strengthening of the previous L2 convergence
statement. It is not the fixed positive-power rate or critical-weighted
cancellation needed to undo harmonic averaging and settle natural density.
No proof or disproof of the original conjecture follows. Spec.lean is
unchanged and still contains its original sorry. Do not resubmit as solved.

## Further continuation: automated audit of accumulated density declarations

Imported the 99 compiled leaf modules together in a temporary audit file.
The combined imports load successfully. An unrestricted exact? search for
the original target timed out after 4,000,000 heartbeats; this is not a
mathematical impossibility claim.

A separate successful metaprogram audit enumerated Erdos371 declarations
whose conclusion is definitionally the exact original HasDensity target.
It found 23 declarations, all with substantive premises (signed smooth
reciprocity, damped cancellation, dyadic regularity, current tightness,
energy/collision estimates, allocation cancellation, or exponential means).
None is a zero-premise theorem of the original target. No overlooked
unconditional proof was obtained. The temporary AuditProofSearch.lean was
removed after this audit; it is not part of the proposed submission.

Spec.lean is unchanged with its original sorry. No complete proof or
disproof is ready, and another unchanged submission would not be valid.

Follow-up audit across ALL imported namespaces: 61 declarations had a direct
Set.HasDensity conclusion. Of these, 23 matched the original target under
definitional equality; all were the previously identified conditional
Erdos371 theorems. There were zero zero-binder matches. Thus this audit found
no direct imported proof outside the Erdos371 namespace either. This does
not rule out a new argument or a nontrivial combination of theorems. The
temporary audit file was again removed. Spec.lean remains unchanged.

## New checked continuation: enhanced stretched-exponential current rate

Added Submission/PrimeCurrentEnhancedRate.lean, importing
PrimeCurrentQuantitativeL2. It has a saved olean and no admissions or unsafe
evaluation. The three printed principal axiom checks use only propext,
Classical.choice, Quot.sound.

- enhancedCurrentScale(N) = sqrt(log N * log(log N)).
- enhancedCurrentRateConstant =
    (exp(4)*(1+2/log(2)))^2 + primeCurrentL2TailConstant, and is positive.
- primeCurrentSquaredError_large_u_scale is a finite estimate under explicit
  scale hypotheses. It uses B=ceil(exp(t)), u=log N/log(B+1), and the existing
  optimized large-u smooth reciprocal estimate. The scale conditions imply
  u*log u >= t/8, giving head error <=C*(1+t)*exp(-t/128).
  Squaring and adding the previously checked tail gives
    squaredError(N) <= enhancedConstant*(1+t)^2*exp(-t/64).
- enhancedCurrentScale_data proves all of these hypotheses eventually for
  t=sqrt(log N*loglog N), using log L/sqrt(L)->0 with L=log N.
- primeCurrentSquaredError_enhanced_bound absorbs the polynomial factor:
    eventually squaredError(N) <= enhancedConstant *
      exp(-sqrt(log N*loglog N)/128).
  This genuinely improves the old exp(-c*sqrt(log N)) rate.
- enhancedCurrentScale_div_log_tendsto_zero and
  enhancedCurrentScale_still_subpower verify its scope: for every real c
  and every delta>0,
    N^delta*exp(-c*sqrt(log N*loglog N)) -> infinity.
  This is a statement about the majorant, NOT a lower bound on the actual
  current error.

The new rate remains insufficient to sum over a positive-power-sized prime
head or to establish the critical prime-weighted energy limit. No new
signed fixed-dyadic cancellation has been proved. Spec.lean remains
unchanged with its original sorry and checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof/disproof is ready; do not submit the unchanged file as solved.

## New checked continuation: quantitative Abel transfer to ordinary energy

Added Submission/PrimeWinnerEnergyEnhancedRate.lean (saved olean). Imports
PrimeCurrentEnhancedRate, PrimeWinnerEnergyIncrement, PrimeWinnerBulkUpper,
and RawHarmonicTauberian. It compiles cleanly. All four printed main axiom
checks contain only propext, Classical.choice, Quot.sound. No admissions or
unsafe evaluation occur in this module.

- primeWinnerSum_abel_prefix and primeWinnerSum_abel_interval give exact
  scalar Abel formulas. Subtracting the formulas at M and N cancels the
  fixed limiting current, including the zero-index contribution.
- primeWinnerEnergy_of_uniform_harmonic_error is the finite vector-valued
  transfer: for 0<M<=N, R>=0, and squaredError(k)<=R for every M<=k<=N,
    primeWinnerEnergy(N) <= 4*M^2 + 12*N^2*R.
  The proof uses four-term Cauchy, finite sums of squared errors bounded by
  their summable full series, and E(M)<=M^2. No signed first-moment estimate
  or critical-weighted estimate is assumed.
- enhancedCurrentScale_half_log_comparison: if log N>=4 and
  log K>=log N/2, then enhancedScale(N)<=2*enhancedScale(K).
- primeWinnerEnergy_enhanced_bound chooses M=ceil(sqrt(N)), uniformly applies
  the harmonic rate for k in [M,N], and proves eventually
    E(N) <= (16+12*enhancedCurrentRateConstant)*N^2 *
      exp(-sqrt(log N*loglog N)/256).
  This is a genuine ordinary-prefix energy estimate, stronger than the
  previous arbitrary fixed logarithmic savings at the quadratic scale.
- enhancedWinnerEnergy_majorant_not_near_linear proves that this displayed
  majorant divided by N^(1+eta) tends to infinity for each eta<1.
  This is a limitation of the MAJORANT, not a lower bound for actual E(N).

The resulting saving remains subpower and does not establish the near-linear
energy hypothesis or signed fixed-dyadic cancellation. The original target
is not proved or disproved. Spec.lean is unchanged with its original sorry;
checksum 34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof/disproof is ready for submission.

## Targeted continuation audit: natural limits, existence, and negation

A temporary audit imported the 99 current compiled leaf modules and examined
798 Erdos371 theorem conclusions headed by Tendsto, Exists, or Not, after
opening their leading binders. Definitional comparison against nine fixed
targets found zero matches: ordinary signed-count mean, ordinary factorSign
mean, the single dyadic harmonic window, ordinary dyadic regularity, critical
winner/loser energies, ordinary rationalFactorSign mean, existence of a
natural density for the actual rise set, and the conjecture's negation.
The successful report is /tmp/natural_limits_audit.txt.

A separate attempt to instantiate generic theorem parameters before comparing
conclusions timed out. A second, per-comparison-budget attempt also timed out;
these unsuccessful runs are not exhaustive searches and prove no impossibility.
Their output is /tmp/natural_limits_meta_audit.txt. The temporary
Submission/AuditNaturalLimits.lean has been removed. No compilation is pending.

No overlooked unconditional natural-limit theorem or density-existence proof
was obtained. This audit added no mathematical estimate. Spec.lean is still
unchanged with its original sorry; no complete proof or disproof is ready.

## Checked continuation: ordinary non-between prefixes have both signs

Added Submission/NonBetweenPrefixSign.lean with a saved olean. It compiles
cleanly; the three printed axiom checks use only propext, Classical.choice,
Quot.sound. The integer discrepancy sums the actual non-between comparison
signs on [1,N], not harmonic weights and not an auxiliary label sequence.

- nonBetweenPrefixDiscrepancy_two certifies the value 2.
- nonBetweenPrefixDiscrepancy_fifteen certifies the value -1.
- nonBetweenPrefixDiscrepancy_both_signs and the two universal-sign negations
  rule out an everywhere-nonnegative or everywhere-nonpositive prefix claim.

The proposed one-sided Tauberian route therefore cannot use a fixed sign of
all these ordinary prefixes. These finite checks DO NOT rule out an eventual
one-sided bound, a constant lower bound, or a sublinear one-sided bound. No
such sufficient bound was proved. They are not a density counterexample.

The original conjecture remains unresolved. Submission/Spec.lean is unchanged
with its original sorry; no completed proof/disproof is ready for submission.

## Checked continuation: one-sided smoothed dyadic endpoint criterion

Added Submission/OneSidedDyadicEndpoint.lean, importing
DyadicEndpointRegularity. It compiles cleanly with a saved olean. All three
printed axiom checks contain only propext, Classical.choice, Quot.sound.

- dyadic_no_drop_iterate propagates the one-sided eventual inequalities
    q(N) <= q(2N)+epsilon
  to every fixed dyadic iterate, with arbitrarily small total error.
- nonneg_prefixMean_zero_of_dyadic_no_drop proves a general analytic result:
  for a nonnegative sequence, the one-sided no-drop condition on its Cesaro
  means, together with multiplicatively syndetic near-zero Cesaro means,
  forces those means to tend to zero. The proof uses no upper bound on the
  upward dyadic jumps.
- density_of_smoothedEndpointBias_no_dyadic_drop applies that result to
    q(N) = (1/N) * sum_{k<N} |prefixMean(k, factorSign)|.
  The existing syndetic-near-zero theorem supplies the anchor hypothesis.
  Thus only eventual q(N)<=q(2N)+epsilon, for every epsilon>0, is required.

LIMITATION: the actual arithmetic no-drop hypothesis has NOT been proved.
The earlier nonnegative comparison-variation/energy identities do not
supply it. This is a weaker sufficient condition than the previously used
two-sided dyadic regularity, not an unconditional density theorem.
Spec.lean remains unchanged with sorry. No proof/disproof is ready to submit.

## Checked continuation: prime-supported critical-energy obstruction

Added Submission/PrimeSupportedCriticalObstruction.lean with a saved olean.
It compiles cleanly; all five printed axiom checks use only propext,
Classical.choice, Quot.sound.

The artificial array is c(N,p)=1/p for primes N<p<=N^2 and zero otherwise.
At the ambient scale X=N^3 this is an interior power band, not a boundary.
Elementary weighted-prime harmonic bounds prove that its reciprocal band
mass is eventually between 1/4 and 3. Consequently:
- Every fixed coordinate eventually vanishes.
- |c(N,p)|<=1/p, with support only on primes.
- The unweighted square sum is at most 3/N eventually, hence tends to zero.
- The critical square sum sum_p p*c(N,p)^2 equals the band mass and does
  NOT tend to zero; neither does its l1 norm.
- For EVERY fixed nonnegative w(p)->0, sum_p w(p)*p*c(N,p)^2 tends to zero.
- not_prime_supported_critical_upgrade packages these properties as the
  negation of the corresponding general analytic implication, using full
  tsums (the arrays have finite support).

SCOPE: This is not the actual comparison-current array. In particular, no
arithmetic counterexample or consistency with all current identities is
claimed. It proves that prime support, an interior band, the reciprocal
coordinate bound, square convergence, and the entire collection of
subcritical weighted conclusions alone cannot supply critical convergence.
It is NOT a disproof of Erdős 371. No new signed arithmetic cancellation was
obtained. The cycle and entropy/source-scale discussions in this continuation
likewise produced no unconditional density theorem.

Spec.lean is unchanged and still contains its original sorry; checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof/disproof is ready, and no submission call was made.

## Checked continuation: limits of diagonal domination

Two new auxiliary files compile cleanly with saved oleans; all printed axiom
checks use only propext, Classical.choice, Quot.sound.

1. Submission/WeightedLoserRankingCheck.lean
   A reordered-prime model, including every prime factor and retaining the
   max-under-multiplication identity. rank_injective and decode_rank are
   proved globally. Numerical weights are the original primes, NOT ranks.
   On the forty positive edges from (1,2) through (40,41), the weighted loser
   energy is 321 and its diagonal is 319. The finite values are kernel-checked.
   This refutes the universal E_loser<=D_loser proposal for this rank model;
   it says nothing against the same bound in the actual numerical prime order.

2. Submission/PrimeLoserGroupDiagonalObstruction.lean
   This one uses the ACTUAL numerical ordering of prime factors.
   The p=5039 loser incidences below N=45352 are exactly
     {10078,15117,20156,25195,30234,35273,45351}.
   The finite computation is reduced to the eighteen edges next to the nine
   multiples of 5039, rather than enumerating the entire prefix in Lean.
   The incidence count is 7, and primeLoserSum 5039 45352=7, the latter using
   the prior congruence-run winner sum and the exact endpoint flux identity.
   Thus this group's square is 49>7: a per-group diagonal domination bound
   fails, including after multiplying both sides by the positive prime.

Targeted diagnostics (NOT proofs): testing global numerical-order weighted
loser energy versus its diagonal through N=200000 found no violation; at
that terminal endpoint E=345828636, D=486803164. Two prior rank models and
random rank tests also gave no violation of the new bound, but a targeted
rank optimization found the certified 321 versus 319 example above.
Do not rerun these finite tests as evidence of an asymptotic theorem.

The global actual inequality E_loser(N)<=D_loser(N) remains neither proved
nor refuted here. It cannot be obtained merely by summing per-group diagonal
bounds (which are false), nor by appealing just to the max multiplication
law (the rank model refutes that generalization). These finite auxiliary
counterexamples do NOT negate Erdős 371.

The other reviews in this continuation (endpoint-rate, summability,
prime-count charging, polynomial doubling) gave no new unconditional signed
cancellation. Spec.lean remains unchanged with the original sorry. No
complete proof/disproof is ready, and no submission call was made.

### Further targeted finite-cutoff diagnostic (not a Lean theorem)

Tested the weighted loser-energy diagonal inequality for maxima over finite
sets of primes in their NUMERICAL order. The first forty initial prime sets
showed no violation for the tested positive prefixes below 10000. A finite
set with gaps did violate it:
  S={2,23,47,53,59,61,71,101,107,127,137,191,193,197}.
On positive edges (1,2) through (1643,1644), the Python diagnostic gave
energy 3913 and diagonal 3579. This value has NOT been certified in Lean.
It concerns a truncated/gapped prime model, not Nat.maxPrimeFac.

Thus an induction statement uniform in arbitrary finite prime sets is not
supported by this test. This does NOT refute diagonal domination for complete
initial prime sets or for the actual largest-prime sequence. No proof of
those stronger arithmetic cases was found. No changes to Spec.lean and no
valid submission resulted.

## Targeted continuation: logarithmic-loss weighted energy diagnostic

No settlement and no new Lean theorem resulted. Spec.lean was not changed.

A finite simulated-annealing diagnostic tested reordered-prime max labels,
with the original numerical primes as weights, for the auxiliary proposal
E_loser(N) <= C*log(N)*D_loser(N). It did NOT test or disprove the density
conjecture. The diagnostic script and full tested ranks are saved as
/tmp/rank_energy_log_test.py and /tmp/rank_energy_log_test.json.

Largest ratios found (not certified in Lean and not claimed optimal):
- N=40: E=321, D=319, E/D approximately 1.00627.
- N=100: E=1460, D=1026, E/D approximately 1.42300.
- N=200: E=6217, D=4017, E/D approximately 1.54767.
- N=500: E=30968, D=18134, E/D approximately 1.70773.
- N=1000: E=96649, D=60199, E/D approximately 1.60549.

There was no violation of E<=log(N)*D in these tested ranks. This is NOT a
proof of that bound, of any universal constant bound, or of the bound for
actual numerical prime order. No general orthogonality estimate for finite
prefixes was obtained. CRT martingale orthogonality over a full primorial
period does not itself control the initial interval of length N.

Other reviews since the last checked module did not supply new estimates:
- Reindexing collisions by their separation retains the neighbouring
  largest-prime restrictions, not just divisibility of the separation.
- Local-minimum cancellations provide the already proved positive opposite
  fraction, not the missing limiting fraction one half.
- Fixed-prime harmonic convergence and the sublogarithmic limiting-current
  mass bound do not justify convergence of the outer signed prime sum.
- The long Vaughan remainder retains non-monotone arithmetic restrictions;
  the opposite-progression monotone-weight bound does not apply to it.
- External reference retrieval failed by DNS; direct-IP DNS-over-HTTPS also
  timed out. No updated external research-status claim follows.

Spec.lean still has its original sorry, checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No complete proof or exact-negation disproof is ready for submission.

## New checked continuation: logarithmic-rate decay of the actual diagonal

Added Submission/PrimeLoserDiagonalLogRate.lean with a saved olean.
It imports PrimeLoserPrimeWeightedCollisions and PrimeWinnerLogPowerCofactor.
Compilation is clean. Both main printed axiom checks contain only propext,
Classical.choice, Quot.sound. No admissions or unsafe evaluation occur.
The temporary CheckDiagonalRate.lean was removed.

- primeLoserPrimeWeightedDiagonal_threshold_bound proves, for T>=0,
    D(N) <= N*T + N*#{n<N : T<primeLoser(n)}.
- primeLoserPrimeWeightedDiagonal_power_bound specializes this to
    D(N)/N^2 <= N^(-u) + #bothLargePrimeSet(N,u)/N.
- primeLoserPrimeWeightedDiagonal_log_rpow_zero proves, for EVERY fixed
  real 0<=a<2,
    (log N)^a * D(N)/N^2 -> 0.
  The proof takes b=a+1 and uses the already defined moving exponent
    u(N)=log(2*(log N)^b)/log N.
  The small-label contribution is exactly 1/(2*log N), after multiplying
  by (log N)^a. The uniform two-prime sieve supplies the other terms:
    C*(log 2+b*loglog N+1)^2/(log N)^(2-a)
  and 2^65*(log N)^a/N^(1/2), both tending to zero.
- primeLoserPrimeWeightedDiagonal_log_zero records a=1 explicitly.

This gives a quantitative ACTUAL arithmetic diagonal estimate, stronger
than its previously proved o(N^2) bound. In particular, a global bound
E_loser(N)<=C*(log N)^a*D(N), with fixed a<2, would suffice (together with
the already proved endpoint estimate). NO SUCH GLOBAL SIGNED ENERGY BOUND
HAS BEEN PROVED. The new module does not control the off-diagonal term,
and does not prove or disprove Erdős 371.

Spec.lean remains unchanged with its original sorry and checksum
34c169f1da983cc3ebc71054a31b6268194e7fa99bc4297ec6a4e76ba50369ff.
No completed proof/disproof is ready to submit.

## New checked continuation: numerical-prime-set energy obstructions

The original conjecture remains unresolved. Spec.lean was not modified.
Two new auxiliary modules compile cleanly, have saved oleans, and their
printed main axiom checks use only propext, Classical.choice, Quot.sound.
Neither contains admissions or unsafe evaluation.

1. Submission/NumericalPrimeSetEnergyObstruction.lean
   Uses the finite set S={263,307,421,1579}, ordered by the NUMERICAL primes.
   The label is max(1, max{p in S : p divides n}); comparison ties have
   sign zero. Energy weights are the original primes. The diagonal is
   sum loser(n)*sign(n)^2, so ties do not contribute.
   - label_mul proves the max-under-multiplication law (including zero).
   - label_eq_of_selected_prime proves each selected prime labels itself.
   - prefix_values proves E(2104)=2368 and D(2104)=822.
   - not_energy_le_twice_diagonal refutes uniform E<=2D for THIS model.

2. Submission/NumericalPrimeSetLogEnergyObstruction.lean
   Uses the numerically ordered finite set
   {7817,8389,8719,9257,9337,10141,10243,17123,25583,29531,63839,
    68399,72959,128981,234511,390851}.
   Again labels are selected numerical primes, signs are zero on ties,
   and diagonal weights include sign^2.
   - Same max multiplication and selected-prime properties are proved.
   - Sparse-support lemmas reduce a prime's group/fiber sum to edges
     adjacent to its multiples; these retain all endpoint restrictions.
   - selected_group_value proves groupSum(7817,390850)=15.
   - The squared-sign incidence fiber is 15 at 7817 and zero at all the
     other selected primes (private checked certificates).
   - diagonal_upper_bound proves D(390850)<=118027.
   - energy_lower_bound proves E(390850)>=1758825.
   - log_endpoint_lt_fourteen proves log(390850)<14.
   - logarithmic_energy_bound_fails proves E(390850)>log(390850)*D(390850).
   The actual numerical E=1758826, D=117964 were independently calculated
   in Python; those EXACT values are NOT claimed as Lean theorems here.

Scope: these are GAPPED prime-set models, not Nat.maxPrimeFac. They do not
refute any energy bound for the complete natural prime order and do not
negate Erdos 371. The second example refutes only the logarithmic inequality
with constant ONE in the generic finite-prime-set setting; it does not
refute a larger unspecified constant times log N. Any successful generic
argument must respect these limitations and use additional arithmetic
structure where needed.

Development notes:
- Sparse fiber sums avoid evaluating all 390850 edges.
- Proving selected-prime identities algebraically avoids a large finite
  decision computation. Individual prime certificates use norm_num.
- The diagonal is recombined by a fiber identity, not by a numerical scan.
- Explicit fiber cases replace a prohibitively expensive broad norm_num.
- The temporary CheckSparseStar.lean was removed.

### Additional diagnostics, not new Lean results

An incremental C++ rank optimizer and an independent Python recalculation
found larger reordered-prime ratios. Files are under /tmp/rank_energy_*.
Examples: N=1000, E=118430, D=56006; N=5000, E=1976768, D=901026;
N=10000, E=7329804, D=3345898. These refute constant two numerically in
those reordered models, not the original sequence. The attempted large
rank certificate was not completed; its source was moved to
/tmp/WeightedLoserRankingTwoCheck.unfinished.lean and removed from
Submission. Do NOT count it as a verified module. The smaller numerical-
order prime-set obstruction above IS kernel-checked.

The algebraically selected star examples and their independent sparse
calculations are stored in /tmp/prime_star_263_8.json,
/tmp/prime_star_7817_50.json, /tmp/prime_star_31859_100.json and associated
_edges.json files. The 31859 example is diagnostic only.

### Unformalized follow-up observation (not a settlement)

For N divisible by 6, consider S={3} together with primes q in (N/2,N]
from one nonzero residue class modulo 3. Such q occur only once in the
positive prefix. If A is their number, the isolated patterns suggest the
exact formulas E=3*A^2, D=2*N/3+3*A (sign reversed for residue 2).
Using the more numerous class and a quantitative half-block prime lower
bound would then yield large generic energy/diagonal ratios. This has NOT
been formalized here. It concerns endpoint-dependent gapped prime sets,
not the complete prime set, and supplies no original-density disproof.

Spec.lean still contains its original sorry. No complete proof or exact-
negation disproof is ready, and no submission was made in this continuation.
