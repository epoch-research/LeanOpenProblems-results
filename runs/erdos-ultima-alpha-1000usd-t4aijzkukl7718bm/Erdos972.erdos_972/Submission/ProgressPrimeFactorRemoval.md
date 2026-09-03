# Checkpoint: proper-prime-power removal and explicit prime off-diagonal

The original conjecture is STILL UNSOLVED. `Submission/Spec.lean` is unchanged
and retains its original `sorry`. No irrational counterexample or sufficient
signed lower bound has been established. Do not submit this as a settlement.

## New verified files

All the following files compile. Principal axiom audits list only `propext`,
`Classical.choice`, and `Quot.sound`.

### LargeSquareDivisors.lean
Namespace `Erdos972LargeSquareDivisors`.

- `proper_prime_power_has_large_square`: a nonprime prime power d>U^3 contains
  a square divisor b^2 with b>U. Write d=p^k, k>=2, and take b=p^(k/2).
  The elementary inequality k<=3*(k/2) supplies the threshold.
- `largeSquareSet U N`: positive n<=N divisible by b^2 for some b>U.
- `largeSquareSet_card_le`: card<=N/U, for U>0.
- `prime_power_divisor_mem`: proper-prime-power divisors above U^3 imply
  membership in this sparse set.
- `pairLargeSquareSet alpha U N`: n<=N for which n or floor(alpha*n) has such
  a square divisor.
- `pairLargeSquareSet_card_le`: card <= (N+floor(alpha*N))/U, for alpha>=1.
  Uses injectivity of floorMul, not an unproved distribution assertion.

This replaces the proposed L-series summability argument with a simpler,
stronger elementary support estimate. No new Dirichlet-series lemma is needed.

### SparseDivisorMoment.lean
Namespace `Erdos972SparseDivisorMoment`.

- `sum_product_fourth_le`: for arbitrary finite s and real f,g,

  (sum_s f*g)^4 <= card(s)^2 * (sum_s f^4)*(sum_s g^4).

- `output_divisor_fourth_moment`: the output fourth moment is at most the
  ordinary divisor fourth moment up to floor(alpha*N).
- `divisor_product_fourth_bound`: for s subset (0,N], Y=floor(alpha*N),
  1+log N, 1+log Y <= L,

  (sum_s tau(n)*tau(floor(alpha*n)))^4 <= card(s)^2*N*Y*L^30.

- `sparse_sum_fourth_bound`: multiplies the preceding RHS by C^4 for weights
  with absolute value at most C*tau(n)*tau(floor(alpha*n)).

Uses the previously verified `DivisorFourthMoment.lean`.

### PrimeFactorRemainder.lean
Namespace `Erdos972PrimeFactorRemainder`.

- `primeMangoldt`: Lambda restricted to primes, an arithmetic function.
- `primeTypeIIPart U V`: (mu_{>U}*zeta)*(primeMangoldt_{>V}).
- `typeII_dominated_abs_bound`: if 0<=g<=Lambda, then

  |(mu_{>U}*zeta*g_{>V})(n)| <= tau(n)*log n.

- `prime_remainder_abs_bound` specializes this to primeTypeIIPart.
- `prime_remainder_eq_of_no_large_square`: if U^3<=V, the original and
  prime-restricted remainders agree outside largeSquareSet U N.
- `pair_difference_eq_zero_outside` and `pair_difference_abs_bound` retain
  the actual two-factor difference; it is supported on pairLargeSquareSet
  and bounded by 2*L^2*tau(n)*tau(floor(alpha*n)).

### PrimeFactorError.lean
Namespace `Erdos972PrimeFactorError`.

`primeFactorError alpha N U V` is exactly the original raw remainder pair
sum minus the prime-restricted raw remainder pair sum.

For alpha>=1, N,U>0, U^3<=V, and the logarithmic bounds above,
`primeFactorError_normalized_fourth` proves

  |primeFactorError/N|^4 <= 16*alpha*(1+alpha)^2*L^38/U^2.

### PrimeFactorErrorScales.lean
Namespace `Erdos972PrimeFactorErrorScales`.

At U=mobiusCutoff u, V=U^3, N=scaleCutoff alpha u:

- `primeFactorBudget` =

  16*alpha*(1+alpha)^2 * [6^19*(1+log u)^19/U]^2.

- `primeFactorBudget_tendsto`: budget -> 0.
- `primeFactorError_scale_fourth`: |error/N|^4 <= budget, for u>0, alpha<=u.
- `eventually_small_prime_factor_error`: for alpha>=1 and epsilon>0,
  eventually |primeFactorError|<=epsilon*N.

This holds on EVERY sufficiently large scale, not on independently chosen
subsequences. No prime-pair distribution hypothesis is used.

### FourFactorDiagonalSplit.lean
Namespace `Erdos972FourFactorDiagonalSplit`.

- `factorOffDiagonal alpha N a b`: the actual four nested finite sums for
  pairSum(a*b,a*b), with exact floor relation and the condition p != q.
- `factorDiagonal alpha N a b`: sum over p and diagonalRows of
  a(m)*a(floor(alpha*m))*b(p)^2.
- `diagonal_inner_sum`, `diagonal_expansion`, and
  `pair_convolution_diagonal_split`: exact generic decomposition.
- `factorDiagonal_tail`: truncates p from (0,N] to (V,N].
- `fourFactor_diagonal_split`: fills the previously missing bookkeeping
  linking the original fourFactorRemainder with vaughanDiagonal.
- `primeVaughanDiagonal`: same row sum with primeMangoldt(p)^2.
- `primeFactorOffDiagonal`: factorOffDiagonal for a=mu_{>U}*zeta and
  b=primeMangoldt_{>V}.
- `prime_remainder_diagonal_split`: exact prime-restricted decomposition.
- `prime_offDiagonal_support`: every nonzero term has U<m,k, V<p,q,
  both p,q prime, p!=q, and k*q=floor(alpha*m*p).
- `prime_vaughan_diagonal_bound`: the same absolute envelope as the earlier
  vaughan_diagonal_bound, with no sign assumption.

### PrimeFactorDiagonalScales.lean
Namespace `Erdos972PrimeFactorDiagonalScales`.

`scale_prime_diagonal_bound` and `eventually_small_prime_diagonal` transfer
that envelope to the same diagonalBudget and the same approximation data
as the original diagonal estimates.

### CommonPrimeOffDiagonal.lean
Namespace `Erdos972CommonPrimeOffDiagonal`.

- `fourFactor_prime_offDiagonal_identity`:

  original fourFactorRemainder - primeFactorOffDiagonal
    = primeVaughanDiagonal + primeFactorError.

- `exists_two_sided_scale_small_prime_diagonal`: the prime diagonal is small
  on the SAME scale as both prime-row families and small-divisor estimates.
  Retains the same reciprocal approximant construction as the existing
  CommonAsymmetricDiagonal result.
- `exists_typeI_and_prime_offDiagonal_scale`: for alpha>1 irrational,
  epsilon>0 and B, there exist u,N with B<u, B<U, N=scaleCutoff alpha u,
  U*V<=root64 u<=N, OutputPrimeScale alpha u, and simultaneously

  |Cov(A,Lambda_output)| <= epsilon*N,
  |Cov(Lambda,A_output)| <= epsilon*N,
  |Cov(A,A_output)| <= epsilon*N,
  |fourFactorRemainder - primeFactorOffDiagonal| <= epsilon*N.

All cutoffs are the existing asymmetric ones U=mobiusCutoff u, V=U^3.
This is an unconditional common-scale existence theorem, not an assumed
prime-pair lower bound.

## Still missing

The signed primeFactorOffDiagonal sum has NOT been bounded from below or
shown to decorrelate. Its coefficients are genuine Mobius-derived divisor
coefficients and have both signs. Distinct prime factors and determinant
uniqueness give no signed cancellation by themselves.

The existing decisive four-factor criterion is CENTERED: finite primeSet
forces centeredFourFactor/N near -1. The new replacement estimate is RAW.
It may be substituted there only while retaining the original remainder
mean-product subtraction. Do not silently equate raw off-diagonal with
centered covariance, or silently replace the means by prime-restricted ones.

No new conditional criterion has been added in this phase, and the original
conjecture has not been proved or disproved.

External literature lookup was attempted again and failed at DNS resolution.
No prime-ratio approximation theorem covering the fixed irrational-slope
unit-width problem was independently verified.
