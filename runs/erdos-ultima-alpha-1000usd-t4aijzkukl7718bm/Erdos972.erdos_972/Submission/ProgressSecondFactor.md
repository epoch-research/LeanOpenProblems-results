# Checkpoint: second-factor foundations (conjecture still unresolved)

`Spec.lean` remains unchanged with the original `sorry`. No irrational
counterexample and no prime-pair lower bound has been proved. Do not submit the
current artifact as complete.

## New compiled and axiom-audited files

### DoubleVaughan.lean
Namespace `Erdos972DoubleVaughan`.

- `typeIPart U V = μ_≤U * log - μ_≤U * ζ * Λ_≤V + Λ_≤V`.
- `typeIIPart U V = μ_>U * ζ * Λ_>V`.
- Exact two-sided identity:
  `C = pair(A,Λ) + pair(Λ,A') - pair(A,A') + pair(R,R')`.
- `typeIIPart_prime`: the genuine remainder vanishes at prime arguments when
  U,V ≥ 1.
- `pairSum_convolution_convolution`: exact four-factor hyperbola expansion
  with indicator `k*l = floorMul α (m*n)`.
- `fourFactor_support`: nonzero terms have m>U, n>V, k>S, l>T.
- `pairSum_majorant_lower`: Bonferroni lower bound for genuine pointwise
  majorants, with majorant hypotheses explicit.

### VaughanRemainderSigns.lean
Namespace `Erdos972VaughanRemainderSigns`.

- `typeIIPart 3 3 30 = log 5 > 0`.
- `typeIIPart 3 3 35 = -(log 5 + log 7) < 0`.
- `typeI_not_mangoldt_majorant`: Vaughan's Type-I part is not a pointwise
  Mangoldt majorant. Do not infer positivity of the double remainder product.

### SlowOscillationTauberian.lean
Namespace `Erdos972SlowOscillationTauberian`.

A new SIGNED bounded Tauberian theorem, extending the earlier nonnegative
monotone version:

`bounded_slow_laplace_tauberian` assumes f is measurable, bounded, zero for
`t ≤ 0`, has a Laplace transform with continuous boundary on `0 ≤ Re z ≤ 1`,
and satisfies eventual slow oscillation:

`∀ ε>0, ∃ δ>0, ∀ᶠ x, ∀ |u|<δ, |f(x+u)-f(x)| ≤ ε`.

It proves `f(t) → 0`. Uses the previously constructed concentrated positive
band-limited kernels. No new analytic theorem is assumed.

### MobiusPartialSums.lean and MobiusLaplace.lean
Namespaces `Erdos972MobiusPartialSums`, `Erdos972MobiusLaplace`.

Definitions:
- `reciprocalMoebius N = sum_{n≤N} μ(n)/n`.
- `reciprocalMoebiusReal x = reciprocalMoebius (floor x)`.
- `logMoebius t = if 0<t then reciprocalMoebiusReal(exp t) else 0`.

Proved slow oscillation from the explicit estimate
`|logMoebius(x+u)-logMoebius(x)| ≤ exp(2δ)-1+exp(δ-x)`
for x>δ and |u|<δ, using only |μ(n)|≤1.

Define the continuous regularized zeta function by updating
`(s-1)*riemannZeta s` to value 1 at s=1. It is nonzero for Re s≥1.
The exact Laplace transform of `logMoebius` is
`Lμ(1+z)/z = 1/(z*ζ(1+z))`, with continuous boundary at z=0 as well.

Main theorem:
`Erdos972MobiusLaplace.reciprocalMoebius_tendsto_zero`.

This strengthens the earlier bound `|sum μ(n)/n| ≤ 2` to convergence to zero,
without a quantitative rate.

### ReciprocalDivisorCounts.lean
Namespace `Erdos972ReciprocalDivisorCounts`.

`inverse_approximant_bounds` converts the approximation r≈1/α used by the
one-prime rows into an approximation r⁻¹≈α, retaining quantitative denominator
bounds. For α≥1 and q=r.den≥2α:
- `q/(2α) ≤ (r⁻¹).den ≤ 2q`;
- `|α-r⁻¹| ≤ 2α²/q²`.

`reciprocal_scale_divisor_prefix_bound`:
For `u^4 ≤ q ≤ 16u^4`, `4α ≤ u`, `αX ≤ u^6`, e≤v, d,e>0:

`|# {0<n≤X : d|n and e|floor(αn)} - X/(d e)| ≤ 118*v*u^4`.

It is uniform in all prefixes X and even all input divisors d. This is an
unweighted joint divisibility count, not a prime-pair estimate.

### DivisorCovariance.lean
Namespace `Erdos972DivisorCovariance`.

Definitions `divisorPolynomial D a n`, `divisorMean D a`, `coefficientMass D a`.

`polynomial_pair_error`:
A uniform local error B gives joint-polynomial error at most
`B * coefficientMass D a * coefficientMass E b` from main term
`N * divisorMean D a * divisorMean E b`.

`logPower_prefix_approx` and `logPower_polynomial_pair_error`:
Any fixed logarithmic power k costs at most `2*(log N)^k` times the uniform
prefix error.

`exists_joint_prime_divisor_scale`:
At arbitrarily large common u, both
1. ALL prime-output arc estimates for m≤root64 u and X≤u^6;
2. ALL joint divisibility prefix estimates for e≤root64 u and
   X≤scaleCutoff α u
hold simultaneously.

`squared_family_divisor_error_tendsto k`:
`(root64 u)^3*(1+log u)^k/u^2 → 0`.
Thus summing the local error over two moving divisor indices, with logarithmic
losses, remains sublinear at N≈u^6/α.

## Change to existing helper

`PolynomialRowScales.lean` now contains
`exists_polynomial_beatty_arc_scale_data`, returning the actual rational r,
its approximation to 1/α, and `u^4 ≤ r.den ≤ 16u^4`, along with all old
conclusions. Both old existence theorems retain their original types as
wrappers. Existing downstream results still audit correctly.

## Next concrete development target

Complete the TWO-TYPE-I centered covariance estimate using these foundations:

For n>0, express each Vaughan Type-I part as
`log n * divisorPolynomial U μ n
 - divisorPolynomial U (fun d => μ(d)*log d) n
 - divisorPolynomial (U*V) (μ_≤U * Λ_≤V) n
 + Λ_≤V(n)`.

The common logarithmic slope is exactly `reciprocalMoebius U`, now known to
tend to zero. After centering, the intercepts cancel. Joint moments above
control all divisor-polynomial products, including log and log² weights.
Replacing `log(floor αn)` by `log α + log n` costs O(logarithms) times coefficient
masses (use the existing `WeightedBeattyRows.log_floorMul_gap`). Small cutoff
terms have sublinear total cost.

This should give vanishing centered Type-I/Type-I covariance when both Möbius
cutoffs grow, without assuming quantitative PNT. Combined with a dual
(output-factor) Type-I estimate, it would leave the genuine centered
four-factor remainder.

**The four-factor remainder still has no proved strict lower bound.** Neither
its algebraic expansion nor the fact it is supported on composites gives a
sign. The ultimate conjecture is still unresolved.

## Other notes

- One literature access retry failed again (DNS resolution). Local Mathlib
  search found no applicable irrational prime-pair theorem. No external status
  has been independently established.
- All principal results above audit with only `propext`, `Classical.choice`,
  `Quot.sound`. Audit file: `Submission/AuditDouble.lean`.
- Scratch `Check*.lean` files may contain intentionally failed `#check`s.
