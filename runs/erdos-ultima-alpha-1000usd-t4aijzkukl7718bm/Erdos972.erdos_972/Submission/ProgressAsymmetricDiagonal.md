# Asymmetric common-scale diagonal estimate — conjecture still unresolved

Spec.lean is unchanged with its original sorry. No proof or irrational
counterexample has been obtained, and no incomplete proof was submitted.

## New verified files

### AsymmetricDiagonalBudget.lean

Namespace Erdos972AsymmetricDiagonalBudget. All principal declarations
compile and audit with only propext, Classical.choice, and Quot.sound.

The new cutoffs are

    U(u) = mobiusCutoff u = root64 (root64 u),
    V(u) = mangoldtCutoff u = U(u)^3.

`mobiusCutoff_tendsto` proves U(u) tends to infinity.
`asymmetric_cutoffs_bounds`, for u>0, proves

    U>0,  U*V <= root64 u,  U^2 <= u.

In particular, these unequal cutoffs remain inside the already proved
Type-I divisor ranges. They are not substitutions of larger, unproved
sieve levels.

The normalized diagonal budget is

    D(alpha,u) = 1440*(1+log u)^2/U(u)
                   + 400000*alpha*(1+log u)^3/u.

`diagonalBudget_tendsto` proves D(alpha,u)->0 for alpha>0.
`normalized_budget_bound` is the numerical inequality used to dominate
the earlier finite weighted diagonal bound by this budget.

`scale_diagonal_bound` applies the actual finite arithmetic estimate at
N=scaleCutoff alpha u. For alpha>=1, alpha<=u, and a reduced a/q satisfying

    u^4 <= 2*alpha*q,   q <= 32*u^4,
    |alpha-a/q|*N <= 1,   N <= q^2,

it proves

    |vaughanDiagonal alpha N U(u) V(u)|/N <= D(alpha,u).

`eventually_small_diagonal` gives the corresponding epsilon*N bound,
uniformly over every such approximant at all sufficiently large u.

### CommonAsymmetricDiagonal.lean

Namespace Erdos972CommonAsymmetricDiagonal. Compiles with permitted axioms.

`inverse_diagonal_data` derives all the displayed approximation hypotheses
from the SAME reciprocal approximant used for the established prime rows:

    |1/alpha-r| <= 1/r.den^2,
    u^4 <= r.den <= 16*u^4,   4*alpha <= u.

It uses the reduced fraction r^(-1), not a separately chosen scale.

`exists_two_sided_scale_small_diagonal` proves that for alpha>1 irrational,
epsilon>0 and B, there is u>B with U(u)>B, OutputPrimeScale alpha u, both
prime-row orientations, all the required joint small-divisor estimates,
and

    |vaughanDiagonal alpha N U(u) V(u)| <= epsilon*N.

### AsymmetricTypeIScales.lean

Namespace Erdos972AsymmetricTypeIScales. Compiles with permitted axioms.

`eventually_asymmetric_double_budget` transfers the Mobius mean term to
U(u). The original and dual covariance error budgets were already uniform
for U*V<=root64 u.

`exists_asymmetric_typeI_and_diagonal_scale` combines everything on one
scale. For every alpha>1 irrational, epsilon>0 and B, it gives u,N with
B<u, B<U(u), N=scaleCutoff alpha u, U*V<=root64 u<=N,
OutputPrimeScale alpha u, and SIMULTANEOUSLY

    |Cov_N(A_UV, Lambda_output)| <= epsilon*N,
    |Cov_N(Lambda, A_UV_output)| <= epsilon*N,
    |Cov_N(A_UV, A_UV_output)| <= epsilon*N,
    |vaughanDiagonal alpha N U V| <= epsilon*N.

There is no unproved distribution hypothesis in this existence theorem.

## Remaining gap

The signed OFF-DIAGONAL four-factor sum is still uncontrolled. The earlier
compact-frequency Mellin estimates, multiplicity lemma, and this diagonal
estimate do not imply a lower gap for that signed sum. No sufficient
prime-pair lower bound was obtained.

The reindexed vaughanDiagonal is defined in VaughanDiagonalBound.lean, and
floor_diagonal_iff in FloorDiagonalCount.lean identifies its row condition
and unique multiplier exactly. A full finite-sum decomposition of the
original fourFactorRemainder into this diagonal and an explicitly defined
off-diagonal sum has NOT yet been added. No claim that such bookkeeping
would itself resolve the signed gap is intended.

The existing symmetric-cutoff reduction has not been replaced in Spec.lean.
These are genuine common-scale estimates, not a completed settlement.

Implementation note: these scratch files set root64 locally irreducible to
prevent excessive unfolding of iterated Nat.sqrt during elaboration. All
proofs are kernel-checked and their axiom audits contain only the allowed
three axioms. There are no pending compilation errors.
