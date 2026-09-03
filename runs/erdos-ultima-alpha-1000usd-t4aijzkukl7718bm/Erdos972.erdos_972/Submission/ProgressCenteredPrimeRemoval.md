# Fully centered prime-factor removal — still no settlement

The conjecture remains UNSOLVED. Spec.lean is unchanged with its original
sorry. No signed lower gap or irrational counterexample has been proved.
No incomplete proof was submitted.

## Main advance in this phase

The earlier removal estimates compared RAW four-factor sums. They could
not be used to replace the actual remainder means without an additional
argument. This phase proves that argument: both mean differences and their
product correction are controlled by the same sparse-support method.

The resulting common-scale reduction now uses an explicitly centered prime
off-diagonal with the ACTUAL PRIME-RESTRICTED remainder means. No mean
correction has been silently omitted or assumed small.

## New verified files

All principal declarations compile and audit with only propext,
Classical.choice, and Quot.sound.

### SparseSingleDivisorMoment.lean
Namespace Erdos972SparseSingleDivisorMoment.

For s subset (0,M] and 1+log M<=L:

- `sparse_single_sum_square`: if |f(n)|<=C*tau(n),

  (sum_s f)^2 <= C^2*#s*M*L^3.

- `divisor_log_sum_square`: if |f(n)|<=tau(n)*log n,

  (sum_s f)^2 <= M^2*L^5.

- `remainder_difference_sum_square`: for Z>0, Z^3<=V, arbitrary U,

  (sum_s [R_UV(n)-R'_UV(n)])^2 <= 4*M^2*L^5/Z.

  Here R' is the prime-restricted remainder. The difference is supported
  on the intersection with largeSquareSet Z M. The sparse cardinal bound
  is retained, as is the divisor second-moment logarithmic loss.

- `floor_image_subset` and `sum_floor_eq_image` transfer these estimates
  to the output arguments by injectivity of floorMul for alpha>=1.

### MeanProductErrorAlgebra.lean
Namespace Erdos972MeanProductErrorAlgebra.

- `product_difference_square_le`: bounds (ab-cd)^2 from bounds on
  (a-c)^2, (b-d)^2, c^2, and b^2, retaining both perturbation terms.
- `fourth_sub_le`: |a-b|^4<=8*(|a|^4+|b|^4).

### RemainderMeanProductError.lean
Namespace Erdos972RemainderMeanProductError.

- `input_total_square`, `output_total_square`: logarithmic bounds for the
  actual sums of a divisor-log-bounded function.
- `input_difference_total_square`, `output_difference_total_square`:
  the preceding sparse difference bounds at both actual argument sets.
- `meanProductError alpha N U V` is exactly

  [total(R)*total(R_output)-total(R')*total(R'_output)]/N^2.

For alpha>=1, N,Z>0, Z^3<=V, and
1+log N, 1+log(floor(alpha*N))<=L:

- `meanProductError_square_bound`:

  meanProductError^2 <=16*alpha^2*L^10/Z.

- `meanProductError_fourth_bound`:

  |meanProductError|^4 <=256*alpha^4*L^20/Z^2.

No assertion that either remainder mean itself vanishes is needed.

### CenteredPrimeFactorError.lean
Namespace Erdos972CenteredPrimeFactorError.

- `centeredPrimeRemainder` is the covariance of R' and R'_output, with
  their own actual means.
- `centeredPrimeFactorError` is centeredFourFactor - centeredPrimeRemainder.
- `centered_error_identity`:

  centeredPrimeFactorError/N = primeFactorError/N - meanProductError.

- `centered_error_normalized_fourth`:

  |centeredPrimeFactorError/N|^4 <=4096*alpha^4*L^38/Z^2.

The constant is deliberately loose. The theorem is uniform in U; it does
not assert signed cancellation in either covariance.

### CenteredPrimeFactorScales.lean
Namespace Erdos972CenteredPrimeFactorScales.

At N=scaleCutoff(alpha,u), Z=mobiusCutoff(u):

- `centeredPrimeFactorBudget` =

  4096*alpha^4*[6^19*(1+log u)^19/Z]^2.

- `centeredPrimeFactorBudget_tendsto`: this tends to zero.
- `uniform_centeredPrimeFactorError_scale_fourth` bounds the normalized
  fourth power by the budget for every U and V>=Z^3.
- `eventually_small_uniform_centered_prime_factor_error`: eventually
  |centeredPrimeFactorError|<=epsilon*N uniformly in those cutoffs.
- `eventually_small_balanced_centered_prime_factor_error` specializes to
  U=V=growingCutoff(u), using the existing Z^3<=growingCutoff(u).

### CommonCenteredPrimeOffDiagonal.lean
Namespace Erdos972CommonCenteredPrimeOffDiagonal.

Defines

  centeredPrimeOffDiagonal(alpha,N,U,V)
    = primeFactorOffDiagonal(alpha,N,U,V)
      -total(R')*total(R'_output)/N.

This is a definition with the full actual prime-remainder mean product.

- `centered_prime_remainder_split`:

  centeredPrimeRemainder = primeVaughanDiagonal+centeredPrimeOffDiagonal.

- `centered_prime_offDiagonal_removal_identity`:

  centeredFourFactor-centeredPrimeOffDiagonal
    =primeVaughanDiagonal+centeredPrimeFactorError.

- `exists_balanced_typeI_and_centered_prime_offDiagonal_scale`: for every
  alpha>1 irrational, epsilon>0, and B, finds u,N with B<u, B<W,
  N=scaleCutoff(alpha,u), W=growingCutoff(u), W^2<=root64(u)<=N,
  OutputPrimeScale(alpha,u), and simultaneously

  |Cov(A_WW,Lambda_output)|<=epsilon*N,
  |Cov(Lambda,A_WW_output)|<=epsilon*N,
  |Cov(A_WW,A_WW_output)|<=epsilon*N,
  |centeredFourFactor(alpha,N,W,W,W,W)
    -centeredPrimeOffDiagonal(alpha,N,W,W)|<=epsilon*N.

All four errors use the SAME common scale and actual prime-row estimates.
There is no assumed distribution or signed-gap hypothesis in this
existence theorem.

## Remaining mathematical gap

The new centeredPrimeOffDiagonal is still signed. No strict lower bound
above -(1-delta)N has been established. Distinct prime factors, sparse
prime-power removal, small diagonal, and correct centering do not by
themselves provide that lower bound.

No new equivalent sufficient criterion was added. The original conjecture
has neither been proved nor disproved, and cannot be replaced by these
error estimates.

Audit: AuditCenteredPrimeRemoval.lean.
