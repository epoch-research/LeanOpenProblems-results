# Sparse diagonal estimate and restored balanced cutoffs

The conjecture is STILL UNSOLVED. Spec.lean is unchanged and retains the
original sorry. This phase supplies no signed off-diagonal lower bound and
no irrational counterexample. Do not submit as a settlement.

## Main improvement

The earlier diagonal estimate used |a_U(n)|<=U+1, resulting in a factor
(U+1)^2 and motivating unequal cutoffs V=U^3. The divisor fourth moment now
removes that loss entirely: the new diagonal bound is UNIFORM IN U.
Proper-prime-power removal has also been generalized to use an independent
square-divisor threshold Z, rather than tying that threshold to U.

Consequently both removals work with the original balanced cutoffs
U=V=growingCutoff(u)=sqrt(root64(u)). All three existing Type-I covariance
estimates and the prime-off-diagonal replacement hold at the SAME scales.
No centering or sign correction is omitted.

## New verified files

Every principal theorem compiles and audits with only propext,
Classical.choice, Quot.sound.

### SparseCommonDivisorSupport.lean
Namespace Erdos972SparseCommonDivisorSupport.

- `floor_common_divisor_iff`: for p>0 and alpha>=0,

  p | floor(alpha*m*p) iff fract(alpha*m)<1/p.

- `floor_div_common_eq`: on that support, floor(alpha*m*p)/p=floor(alpha*m).
- `commonDivisorSet alpha N V`: positive n<=N for which some p>V divides
  both n and floor(alpha*n). No prime restriction is imposed.
- `commonDivisorSet_eq_union`: exact union of the images m -> m*p of the
  earlier diagonalRows.
- `commonDivisorSet_card_bound`: with the existing reduced a/q approximation
  hypotheses |alpha-a/q|*N<=1 and N<=q^2, V>0,

  #commonDivisorSet <= 10N/V+(2N/q+5q)(1+log(2q))+2q.

### SparseVaughanDiagonal.lean
Namespace Erdos972SparseVaughanDiagonal.

- `diagonalAt alpha U V g n`: the diagonal grouped by its actual input n;
  sums over common divisors p>V of n and floor(alpha*n).
- `diagonalAt_sum_eq`: exact reindexing to factorDiagonal for
  a=mu_{>U}*zeta and b=g_{>V}.
- `diagonalAt_zero_outside`: support is commonDivisorSet.
- `absolute_divisor_mangoldt_sum`:

  sum_{p|n} |a_U(n/p)| Lambda(p) <= tau(n)*log n.

- `diagonalAt_abs_bound`: for 0<=g<=Lambda, alpha>=1,

  |diagonalAt(n)| <= tau(n)*tau(floor(alpha*n))*log n*log(floor(alpha*n)).

  This dominates the diagonal by the product of two complete nonnegative
  divisor sums. It does not assume signed cancellation.
- `sparse_diagonal_normalized_fourth`: if N>0 and
  1+log N, 1+log(floor(alpha*N)) <= L,

  |factorDiagonal/N|^4 <= alpha*(#commonDivisorSet/N)^2*L^38.

  The Mobius cutoff U is arbitrary. The estimate applies both to g=Lambda
  and to g=primeMangoldt.

### UniformPrimeFactorError.lean
Namespace Erdos972UniformPrimeFactorError.

Generalizes the earlier proper-prime-power support and fourth-moment
argument. The independent threshold Z>0 is sufficient if Z^3<=V; the
Mobius cutoff U is unrestricted.

`primeFactorError_normalized_fourth_general`:

  |primeFactorError(alpha,N,U,V)/N|^4
    <=16*alpha*(1+alpha)^2*L^38/Z^2.

The earlier argument was recovered by setting Z=U, but that identification
is not required.

### SparseDiagonalScales.lean
Namespace Erdos972SparseDiagonalScales.

Let Z=mobiusCutoff(u)=root64(root64(u)), N=scaleCutoff(alpha,u).

- `common_divisor_scale_density`: for V>=Z and the same admissible a/q,

  #commonDivisorSet/N <= 10/Z+2400*alpha*(1+log u)/u.

- `sparseDiagonalBudget(alpha,u)` is

  alpha * [6^19 * (10(1+log u)^19/Z
                 +2400*alpha*(1+log u)^20/u)]^2.

- `sparseDiagonalBudget_tendsto`: this tends to zero.
- `sparse_diagonal_scale_fourth`: |diagonal/N|^4 <= budget.
- `eventually_small_sparse_diagonal`: eventually, UNIFORMLY over all U,
  V>=Z, all admissible a/q, and all arithmetic functions 0<=g<=Lambda,
  the diagonal has absolute value <=epsilon*N.

### BalancedPrimeFactorErrorScales.lean
Namespace Erdos972BalancedPrimeFactorErrorScales.

- `smallCutoff_cube_le_balanced`: Z^3<=growingCutoff(u), for u>0.
- `smallCutoff_le_balanced`.
- `uniform_primeFactorError_scale_fourth`: the earlier primeFactorBudget
  bounds the fourth power for any U and any V>=Z^3.
- `eventually_small_uniform_prime_factor_error`.
- `eventually_small_balanced_prime_factor_error`: specializes to U=V=W,
  W=growingCutoff(u), giving |primeFactorError|<=epsilon*N eventually.

### CommonBalancedOffDiagonal.lean
Namespace Erdos972CommonBalancedOffDiagonal.

- `exists_two_sided_scale_small_balanced_diagonal`: selects the same
  reciprocal approximant as the two prime-row families, and bounds the
  prime diagonal at U=V=W. Includes joint small-divisor estimates.
- `exists_balanced_typeI_and_prime_offDiagonal_scale`: for alpha>1
  irrational, epsilon>0, and B, finds u,N with B<u, B<W, N=scaleCutoff(alpha,u),
  W^2<=root64(u)<=N, OutputPrimeScale(alpha,u), and simultaneously

  |Cov(A_WW,Lambda_output)| <=epsilon*N,
  |Cov(Lambda,A_WW_output)| <=epsilon*N,
  |Cov(A_WW,A_WW_output)| <=epsilon*N,
  |fourFactorRemainder(alpha,N,W,W,W,W)
     -primeFactorOffDiagonal(alpha,N,W,W)| <=epsilon*N.

These are common scales, not independently chosen subsequences. There is
no unproved distribution hypothesis in the existence theorem.

## Remaining gap

The replacement in the last theorem is RAW. When it is substituted into
the centered four-factor reduction, retain the original remainder means.
Nothing here controls the sign of primeFactorOffDiagonal or replaces
those means without proof.

The balanced cutoffs now align exactly with the original FourFactorReduction,
but the needed strict centered lower gap is still unproved. Do not present
the removal estimates or this common-scale theorem as a prime-pair lower
bound. No new equivalent conditional criterion was added in this phase.

Audit file: AuditSparseDiagonalBalanced.lean.
