# Full actual squarefree-support mean — conjecture still unresolved

The conjecture in `Submission/Spec.lean` is unchanged and still contains its
original `sorry`. No sufficient prime-pair lower bound or irrational
counterexample has been found. Do not submit these auxiliary results as a
settlement.

## SquarefreeDivisorExpansion.lean

Namespace `Erdos972SquarefreeDivisorExpansion`.

The file proves the exact identity

    |mu(n)| = sum_{d | Nat.floorRoot 2 n} mu(d),

using the equivalence `Squarefree n <-> Nat.floorRoot 2 n = 1`. For positive
n<=N, this is exactly the sum over 1<=d<=N with d^2|n.

Define the truncation at D and its scalar mean

    T_D(n) = sum_{d<=D,d^2|n} mu(d),
    c_D    = sum_{d<=D} mu(d)/d^2.

For a nonnegative input weight a(n)<=L on 1<=n<=N and 0<D<=N, the large-square
tail is retained and bounded explicitly:

    |sum a(n)|mu(n)| - sum a(n)T_D(n)| <= L*N/D.

This follows by interchanging finite sums, counting multiples of d^2, and the
reciprocal-square tail estimate. If the actual divisor rows at d^2 for d<=D
have error at most E relative to X/d^2, the full finite approximation is

    |sum a(n)|mu(n)| - X*c_D| <= L*N/D + D*E.

No sign cancellation of mu(n) against a(n) is asserted by this estimate.

## SquarefreePrimeOutputMean.lean

Namespace `Erdos972SquarefreePrimeOutputMean`.

- `squarefreeMeanTruncation_tendsto` proves c_D -> 6/pi^2, using the previously
  verified damped mean at parameter 1 and Mathlib's zeta(2) evaluation.
- `growingCutoff_log_div_tendsto` controls every fixed logarithmic power
  divided by W(u)=sqrt(root64(u)).
- `squarefree_row_budget_tendsto` proves W(u)*outputRowBudget(alpha,u)/N -> 0.
- `squarefree_tail_budget_tendsto` proves log(alpha*N)/W(u) -> 0.
- `squarefree_output_error` applies the full finite estimate with the actual
  prime-output weight a(n)=Lambda(floor(alpha*n)), the established divisor
  rows, D=W(u), and N=scaleCutoff(alpha,u). Both errors remain in the statement.

Define

    squarefreeOutputSum(alpha,N)
      = sum_{n<=N} |mu(n)| Lambda(floor(alpha*n)).

### Main actual result

`eventually_squarefree_output_mean` proves that, for every irrational alpha>1
and epsilon>0, every sufficiently large GOOD scale u satisfies

    |squarefreeOutputSum(alpha,N)/N - 6/pi^2| <= epsilon,
    N=scaleCutoff(alpha,u).

`exists_squarefree_output_mean` invokes the actual common-scale existence
result to supply arbitrarily large such N. There is no unproved distribution
hypothesis in that existential theorem.

`exists_moebius_output_euler_support_bound` consequently proves, at arbitrarily
large selected cutoffs,

    |sum_{n<=N} mu(n) Lambda(floor(alpha*n))| <= (6/pi^2+epsilon)*N.

Finally, `not_tendsto_squarefree_output_zero` proves that the normalized
ABSOLUTE-support sum does not tend to zero. This rules out obtaining o(N)
merely by discarding the signs, while leaving signed cancellation possible.

## Exact limitation

The new mean concerns |mu| (equivalently mu^2), not the signed mu sum and
not the source Mangoldt weight Lambda(n). Its positive constant does not
contradict finitude of primeSet(alpha). The original prime-pair lower bound
is still missing. No prime-detecting limit exchange is used or justified.

## Verification

Both new development files compile without errors. Their principal axiom
audits print only propext, Classical.choice, and Quot.sound. The signature
check file `CheckSquarefreeOutput.lean` also compiles. No new sorry or axiom
was introduced in either development file, and no incomplete proof was
submitted.
