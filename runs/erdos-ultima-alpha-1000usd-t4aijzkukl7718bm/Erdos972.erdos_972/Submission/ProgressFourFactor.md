# Checkpoint: fully centered four-factor reduction (still unsolved)

The original conjecture is STILL UNSOLVED. `Spec.lean` is unchanged and still
contains its original `sorry`. No irrational counterexample or sufficient
four-factor lower bound has been proved. Do not submit as complete.

## Completed in this phase

### OriginalTypeICovariance.lean
Namespace `Erdos972OriginalTypeICovariance`.

- `covariance_center_identity`: exact correction from an arbitrary scalar
  center to true covariance.
- `typeIPart_centered_sum`: weighted centered Type-I sum = first-second+small.
- `typeIPart_abs_bound`: |A_UV(n)|≤3vL² when U,V>0, UV≤v, L≥1,
  log(UV), log n≤L-1.
- `original_typeI_covariance_bound`: with the original prime-output row
  discrepancy E, U,V>0, UV≤v≤N:

  ```
  |Cov_N(A_UV(n), Λ(floor αn))|
  ≤200v*(1+log(αN))³*(E+1)+2|commonLogCenter(αN)|/α.
  ```

  The approximate commonMean is now replaced by the true average. This
  bound is unconditional under the stated one-prime row estimates.

### CovarianceScaleBudgets.lean
Namespace `Erdos972CovarianceScaleBudgets`.

- `scaleCutoff_tendsto`: floor(u^6/α)→∞ for α≥1.
- `scale_log_bound`: 1≤1+log(αN)≤6(1+log u), for u>0 and α≤u.
- `scale_log_weight_tendsto`: generic transfer of
  v*(1+log u)^k*f(u)/u^6→0 to C*v*(1+log(αN))^k*f(u)/N→0,
  for nonnegative f and C≥0.
- `eventually_bound_of_scaled_limit`: normalized convergence implies an
  eventual unnormalized εN bound.
- `eventually_original_covariance_budget`.
- `eventually_dual_covariance_budget`.
- `eventually_double_typeI_budget`.

All three full covariance budgets are now o(N) at the same numeric scales,
not just separate existential choices. The latter uses the signed Möbius
product tending to zero at `growingCutoff u`.

### CommonCovarianceScales.lean
Namespace `Erdos972CommonCovarianceScales`.

`OutputPrimeScale α u` is the original family of prime-output arc estimates:
all m≤root64 u and X≤u^6, with error polynomialRowError u (root64 u).

`exists_common_typeI_covariance_scale`:
For α>1 irrational, ε>0, B natural, there are u,N with
B<u, N=scaleCutoff α u, B<growingCutoff u, root64 u≤N,
OutputPrimeScale α u, and SIMULTANEOUSLY:

```
|Cov_N(A(n), Λ(floor αn))|≤εN
|Cov_N(Λ(n), A(floor αn))|≤εN
|Cov_N(A(n), A(floor αn))|≤εN
```

where A uses both cutoffs equal to growingCutoff u. This invokes the actual
common-scale theorem from DualPrimeRows; the three scales are not independent.

### CenteredDoubleVaughan.lean
Namespace `Erdos972CenteredDoubleVaughan`.

- `covariance_add_left`, `covariance_add_right`, `covariance_double_split`.
- `centeredFourFactor α N U V S T` is exactly
  Cov_N(typeIIPart U V n, typeIIPart S T (floor αn)).
- `centeredFourFactor_eq`: equals raw fourFactorRemainder minus the product
  of the two actual remainder means divided by N.
- `centered_double_vaughan_identity`:

```
Cov(Λ,Λ_output) = Cov(A,Λ_output)+Cov(Λ,A_output)-Cov(A,A_output)
                   +centeredFourFactor.
```

No sign assumptions on the remainders are made.

### PrimeCovarianceObstruction.lean
Namespace `Erdos972PrimeCovarianceObstruction`.

- `output_row_error_budget_tendsto`:
  (polynomialRowError+2log(αN)+7)/N→0.
- `output_total_error`: the m=1 good row controls
  |total Λ_output-commonMean*N| by that numerator.
- `eventually_output_mean_error`: on good scales the output mean approaches
  commonMean, uniformly at every sufficiently large good scale.
- `finite_primeSet_forces_negative_prime_covariance`: if primeSet α is
  finite, then for every ε>0, eventually in u:

```
OutputPrimeScale α u → |Cov_N(Λ,Λ_output)/N+1|≤ε.
```

Uses prime-power removal and qualitative PNT, not a prime-pair estimate.

### FourFactorReduction.lean
Namespace `Erdos972FourFactorReduction`.

**Main new necessary condition:**
`finite_primeSet_forces_negative_fourFactor`:
if α>1 irrational and primeSet α finite, then for every ε>0 and B there
exist u,N with B<u, N=scaleCutoff α u, B<growingCutoff u, N>0,
OutputPrimeScale α u, and

```
|centeredFourFactor α N W W W W / N + 1|≤ε,
W=growingCutoff u.
```

**Conditional sufficient criterion:**
`infinite_primeSet_of_fourFactor_gap`:
if δ>0 and eventually for all good u,

```
-(1-δ)*N ≤ centeredFourFactor α N W W W W,
```

then primeSet α is infinite.

The gap is an EXPLICIT UNPROVED HYPOTHESIS. This theorem is not a settlement
of the conjecture. All preceding Type-I estimates are now in place.

## Genuine remaining mathematical blocker

One must either produce a strict lower gap for the centered four-factor
remainder on suitable common scales, find a different prime-pair lower-bound
argument, or construct an actual irrational counterexample. None has been
found. It is no longer useful merely to add more versions of the Type-I
reduction without attacking this gap.

Notes from mathematical reconsideration (not formal claims):

- Direct Cauchy-Schwarz via remainder variance is too weak: the remainder's
  variance can retain a logarithmic factor; the desired gap is on scale N.
- Arbitrary-coefficient four-factor decorrelation cannot simply be assumed:
  multiplicative phases m^(it), n^(it), k^(-it), l^(-it) align when kl≈αmn.
- Replacing Vaughan A by a true Selberg majorant would permit nonnegative
  residual products, but the usual mean-2 majorant is at the parity boundary.
  Establishing sufficient simultaneous rough-composite mass is itself a
  substantive missing estimate, not a consequence of the upper sieve.
- No external literature theorem has independently settled the full statement.
- No final submission has been made. The final proof, if found, must be
  flattened into Spec.lean without adding or removing its sole import.

All new principal results compile and audit with only propext,
Classical.choice, Quot.sound. Audit file: Submission/AuditFourFactor.lean.
