# Checkpoint: actual two-Type-I covariance and dual prime rows

The original conjecture is STILL UNSOLVED. `Submission/Spec.lean` is unchanged
and retains its original `sorry`. No irrational counterexample has been found.
No genuine two-prime Type-II/four-factor lower bound has been proved. Do not
submit the current artifact as a complete solution.

## Newly completed, compiled, axiom-audited files

### ProfileLogShift.lean
Namespace `Erdos972ProfileLogShift`.

- `divisorPolynomial_linear`, `coefficientMass_linear`, `profileMass_shift`.
- Shifting the output constant coefficient by `log α * c` aligns the output
  profile with the input logarithm, leaving its signed slope unchanged.
- `profile_log_shift_l1`: total absolute replacement error is at most
  `coefficientMass E c * (1+log N)` for α≥1.
- `profile_covariance`: covariance of the actual two profiles is bounded by
  `32N*|mean a*mean c|`, the joint-divisor discrepancy term, and the harmonic
  logarithm-replacement term.

### TypeICovariance.lean
Namespace `Erdos972TypeICovariance`.

- `typeIPart_profile`, `typeI_profileMass_le`, `profile_abs_of_log_le`.
- `typeI_covariance_bound`: for positive U,V,S,T, products U*V,S*T≤v≤N,
  α≥1, and uniform joint divisor-prefix discrepancy ≤B:

  ```
  |Cov_N(A_UV(n), A_ST(floor αn))|
  ≤ 32N*|reciprocalMoebius U * reciprocalMoebius S|
    +100*(B+1)*v²*(1+log(αN))⁵.
  ```

  This is for the actual Type-I functions, including both isolated small
  terms. The small-term perturbation costs at most `70v² L²`.

### TypeICovarianceScales.lean
Namespace `Erdos972TypeICovarianceScales`.

- `eventually_covariance_budget`: the local-error term with
  `B=118*root64(u)*u⁴`, `N=scaleCutoff α u` is o(N).
- `growing_slope_product_tendsto`: the signed main coefficient tends to zero
  when both cutoffs are `growingCutoff u = sqrt(root64 u)`.
- `exists_growing_typeI_covariance_scale`: arbitrarily large common scales
  have actual Type-I/Type-I covariance ≤εN and retain all original prime-
  output arc estimates at exactly that scale. Both cutoffs grow.

### InverseGoodApproximation.lean
Namespace `Erdos972InverseGoodApproximation`.

- `normalize_approximant`: if `|θ-r|≤C/r.den²`, C positive natural, there is
  a good approximant s with `r.den≤2C*s.den`, `s.den≤4C*r.den`, and
  `|θ-s|≤1/s.den²`.
- `inverse_good_approximant`: from a good r≈1/α with r.den≥2α, and J≥α≥1,
  obtains a good s≈α with both denominator losses at most `64J³`.

### ScaledPrimeRows.lean
Namespace `Erdos972ScaledPrimeRows`.

- Generalizes the reciprocal-row estimates to a fixed denominator-comparison
  loss K. Hypotheses are `u⁴≤K*r.den`, `r.den≤16K*u⁴`.
- `scaled_rows_prefix_bound`: Fourier error constant `rotationConstant
  (256*K*H*M)`; eligibility `2048*K*H*M≤u`.
- `scaledRowError K u v = (28+rotationConstant (256*K))*(1+log u)^5*u^6/v^3`.
- `scaled_arc_prefix_bound`: arbitrary suitably interior arcs, with error
  `scaledRowError`, when v≥2048K and v^64≤u.

### DualPrimeRows.lean
Namespace `Erdos972DualPrimeRows`.

- `inputDivisorRow α e N = sum_{0<n≤N,e|floor αn} Λ(n)`.
- `inputDivisorRow_complement_arc`: for e>1, the complement is the centered
  arc at frequency α/e with endpoints a=1/(2e), 1-a and translation -a.
  This follows from `floor_dvd_iff_fract_div_lt` and `fract_sub_center`.
- `input_divisor_row_discrepancy`: on the scaled rational family,
  `|inputDivisorRow α e X-psi(X)/e|≤scaledRowError K u v`, uniformly e≤v,
  X≤u^6. The e=1 case is exact.
- `summed_scaledRowError_tendsto K k`: v*(1+log u)^k*scaledRowError/u^6→0.
- `dualScaleLoss α = 64*ceil(α)^3`; `dualScaleLoss_pos` for α≥1.
- `exists_two_sided_prime_divisor_scale`: arbitrarily large u simultaneously
  supplies (1) original prime-output rows, (2) dual prime-input/output-divisor
  rows, and (3) ordinary joint-divisor prefix counts. It also gives
  4α≤u and 2048*dualScaleLoss α≤root64 u.

### DualProfileCovariance.lean
Namespace `Erdos972DualProfileCovariance`.

- `prime_polynomial_expansion`, `prime_polynomial_moment`,
  `prime_log_polynomial_moment`, `prime_aligned_moment`.
- `mangoldt_covariance_perturb`: first/mixed moment errors E1,E2 imply
  covariance error ≤E2+7E1 (using psi(N)/N≤7, not a log N pointwise bound).
- `covariance_model_right`: model covariance = signed slope times Cov(Λ,log).
- `mangoldt_log_covariance`: exactly `selfCenteredLog psi N`.
- `mangoldt_log_covariance_tendsto`: Cov(Λ,log)/N→0 by qualitative PNT.
- `prime_aligned_covariance`: main term
  `|divisorMean E c|*|Cov(Λ,log)|`, error
  `2*(1+log N)*(Bp+7Bd)*profileMass E c d`.

### DualTypeICovariance.lean
Namespace `Erdos972DualTypeICovariance`.

- `dual_typeI_covariance_bound`: α≥1, S,T>0, S*T≤v≤N, dual prime row error
  Bp≥0, and unweighted joint-divisor error Bd≥0 (input divisor only 1):

  ```
  |Cov_N(Λ(n), A_ST(floor αn))|
  ≤ 2*|Cov_N(Λ(n), log n)|
    +50*v*(1+log(αN))³*(Bp+Bd+1).
  ```

  The actual output logarithm and isolated small Mangoldt term are both
  restored. Their joint L1 error is ≤8vL, so covariance perturbation ≤16vL².
  The signed Möbius slope is bounded by 2, avoiding any quantitative PNT.

## Next concrete reduction steps

1. Turn `dual_typeI_covariance_bound` into a sublinear common-scale estimate.
   The Bp term is covered by `summed_scaledRowError_tendsto` (k=3), using
   `1+log(α*scaleCutoff α u)≤6*(1+log u)` and u^6≤2αN.
   The Bd+1 term can be absorbed by the existing two-Type-I local budget:
   `50vL³(Bd+1)≤100v²L⁵(Bd+1)` for v,L≥1.
   The main term tends to zero by `mangoldt_log_covariance_tendsto`; prove
   `scaleCutoff α` tends to atTop from N≥u eventually if useful.

2. Convert the existing original-side Type-I estimate, which is centered at
   `commonMean α N`, into true covariance. The exact correction is

   ```
   Cov(A,Λ_output)
   = weightedSum A (Λ_output-commonMean) N
     -(total N A/N)*(total N Λ_output-commonMean*N).
   ```

   Existing `typeI_uniform_budget` handles the first term. The second needs
   only the m=1 centered row error and a bound `|total A|/N≤3vL²`.
   A generous budget `200vL³(E+1)+2|commonLogCenter(αN)|/α` should suffice.

3. Combine all three vanishing Type-I covariance terms at scales from
   `exists_two_sided_prime_divisor_scale`. The double Vaughan identity is
   bilinear, so it also holds for covariance. Finite primeSet implies
   Cov(Λ,Λ_output)/N≈-1 on these scales (use prime-power removal, PNT, and
   the m=1 prime-output row estimate). Consequently it forces the genuinely
   centered four-factor remainder close to -N.

4. A strict lower gap for that four-factor remainder is STILL MISSING.
   Completing steps 1–3 is only a reduction, NOT a solution of the conjecture.

## Mathematical cautions

- No general sign is available for the Vaughan remainder. Verified earlier
  examples give both signs.
- Do not posit arbitrary-coefficient four-factor decorrelation. Multiplicative
  archimedean phases m^(it), n^(it), k^(-it), l^(-it) can align on
  kl≈αmn. Any such theorem would need hypotheses controlling these modes.
- No external source has independently verified the full conjecture's status.
- All principal new results audit with only propext, Classical.choice,
  Quot.sound. Audit files: AuditTypeICovariance.lean and AuditDualRows.lean.
