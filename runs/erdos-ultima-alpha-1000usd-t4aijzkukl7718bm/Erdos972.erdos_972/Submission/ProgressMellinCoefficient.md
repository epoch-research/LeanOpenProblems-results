# Actual divisor-coefficient Mellin estimates — conjecture remains unsolved

`Submission/Spec.lean` is unchanged and retains its original `sorry`. There is
no completed proof or irrational counterexample. No final submission was made.

## New verified results

Write

    a_U(n) = (tail(mu, U) * zeta)(n)
    s_U = sum_{0<d<=U} mu(d)/d.

This a_U is the ACTUAL divisor coefficient in the four-factor remainder, not
an arbitrary coefficient sequence.

### MellinDivisorCoefficient.lean
Namespace `Erdos972MellinDivisorCoefficient`.

- `divisorCoeff_sum`: for 0<U<=N,

      sum_{n<=N} a_U(n) = 1 - sum_{d<=U} mu(d)*floor(N/d).

- `divisorCoeff_prefix_error`: for 0<U<=N,

      |sum_{n<=N} a_U(n) + N*s_U - 1| <= U.

- `divisorCoeff_interval_prefix`: for U<=M and j<=M,

      |sum_{M<n<=M+j} a_U(n)| <= |s_U|*M + 2U.

- `norm_weighted_prefix`: complex finite summation by parts with a bound on
  the weight's total variation. No monotonicity of the weight is assumed.
- `mellinPhase t x = exp(I*t*log x)` and its unit norm and variation bounds.
- `divisorCoeff_mellin_bound`: for 0<U<=M,

      ||sum_{M<n<=2M} a_U(n)*exp(I*t*log n)||
          <= (1+|t|)*(M*|s_U| + 2U).

- `divisorCoeff_mellin_uniform`: if U(k)->infinity, eventually U(k)<=M(k),
  and U(k)/M(k)->0, these sums are o(M(k)), uniformly for |t|<=T for every
  fixed finite T.

### MertensFromReciprocal.lean
Namespace `Erdos972MertensFromReciprocal`.

- `mertens N = sum_{0<n<=N} mu(n)`.
- `mertens_abel`: exact identity

      mertens N = N*s_N - sum_{0<=j<N} s_j.

- `mertens_div_tendsto_zero`: mertens(N)/N -> 0, obtained from the already
  verified reciprocal Mobius limit and the Cesaro lemma.
- `eventually_mertens_bound`: the epsilon-N form.

### UniformDivisorCoefficient.lean
Namespace `Erdos972UniformDivisorCoefficient`.

Handles the range where M is comparable to U, which the error 2U in the
first estimate cannot handle.

- `divisorCoeff_sum_short`: for L<=N<=L*U,

      sum_{n<=N} a_U(n)
        = sum_{k<=L} sum_{d<=N/k} mu_{>U}(d).

- `divisorCoeff_short_bound`: controlled using ordinary Mobius cancellation
  at endpoints >= U; endpoints below U give a zero tail sum.
- `divisorCoeff_long_bound`: elementary long-range bound using s_U.
- `eventually_divisorCoeff_prefix_small`: for each epsilon>0, eventually in U,

      for EVERY N>=U, |sum_{n<=N} a_U(n)| <= epsilon*N.

  Proof: choose L large; use the floor-sum bound for N>L*U and ordinary
  Mobius cancellation for U<=N<=L*U. Both estimates are uniform in N.

- `eventually_divisorCoeff_mellin_uniform`: for every fixed T>=0 and
  epsilon>0, eventually in U,

      for EVERY M>=U and EVERY |t|<=T,
      ||sum_{M<n<=2M} a_U(n)*exp(I*t*log n)|| <= epsilon*M.

  This removes the earlier restriction U/M->0.

All these principal results compile and their audits list only `propext`,
`Classical.choice`, and `Quot.sound`. Audit file:
`Submission/AuditMellinCoefficient.lean`.

## What this addresses, and the remaining gap

Multiplicative phases can obstruct blanket assertions of four-factor
cancellation for arbitrary separable coefficients. The new results establish
actual-coefficient cancellation against every fixed compact range of these
frequencies, uniformly over all dyadic blocks above the cutoff.

They DO NOT estimate the whole four-factor correlation. The thin floor
relation requires frequencies growing with the outer scale. Compact-frequency
uniformity cannot be silently extended to that growing range, and no bound
for its contribution has been obtained. In addition, the other factors and
all truncations must be retained when applying any spectral representation.

No strict four-factor lower gap, no N^s prime-correlation lower bound for
s>1/2, and no unbounded excess over the prime-power budget has been proved.
Those are still unproved targets, as recorded in `ProgressFourFactor.md` and
`ProgressSublinearCriterion.md`.

## Follow-up review: no further lower bound

A subsequent review did not produce a new prime-pair estimate or counterexample.

- Applying the coefficient prefix/Mellin bounds separately for each fixed
  choice of the other factors leaves too many summed errors; no valid o(N)
  estimate follows from that substitution.
- Smoothing the outer cutoff does not justify discarding the high frequencies
  conjugate to the multiplicative ratio. That ratio is unchanged under common
  scaling of the two arguments, while the floor strip remains microscopically
  narrow relative to their size.
- The Mathlib number-theory results concerning Beatty sequences include
  Rayleigh complementation, but no applicable two-prime lower bound was found.
  Complementation alone does not imply that the relevant indices are prime.

No new declarations were inserted into Spec.lean. The existing coefficient
estimates remain valid partial results, not a settlement.
