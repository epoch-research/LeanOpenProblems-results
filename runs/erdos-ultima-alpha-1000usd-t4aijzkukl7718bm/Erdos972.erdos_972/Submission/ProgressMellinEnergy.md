# Unrestricted-frequency Mellin energy bounds — conjecture still unresolved

`Submission/Spec.lean` is unchanged with its original `sorry`. No complete
proof or irrational counterexample was found, and no submission was made.

## New verified files

### MellinMeanSquare.lean
Namespace `Erdos972MellinMeanSquare`.

Definitions:
- `osc x t = exp(i*x*t)`.
- `kernel A B x = integral_{A..B} osc x t`.
- `frequencySum s f a t = sum_{n in s} a(n)*osc(f(n),t)`.
- `energy s a = sum_{n in s} |a(n)|^2`.
- `offKernel f m n = 0` on the diagonal and
  `2/|f(m)-f(n)|` off the diagonal.

Results:
- `frequencySum_integral_square`: exact finite Gram-matrix integral identity.
- `symmetric_row_bound`: a finite symmetric nonnegative matrix row-sum bound.
- `frequencySum_mean_square`: if f is injective on s and every offKernel row
  has sum at most C, then

      |integral_{A..B} |frequencySum(t)|^2 - (B-A)*energy(s,a)|
          <= C*energy(s,a).

  No growth restriction on A or B is imposed.

- `reciprocal_distance_row`: the reciprocal integer-distance row is bounded
  by twice the harmonic number; the zero-distance term is defined as zero.
- `nat_log_gap` and `log_offKernel_row`: for positive integers up to N,
  the log-frequency row sum is at most 4*N*(1+log N).
- `mellin_mean_square`: for s subset {1,...,N},

      |integral_{A..B} |sum_{n in s} a(n)*n^(it)|^2
         - (B-A)*sum_{n in s}|a(n)|^2|
          <= 4*N*(1+log N)*sum_{n in s}|a(n)|^2.

  This is a TWO-SIDED energy discrepancy bound, uniform in both endpoints.

- `actual_divisorCoeff_energy`: for the actual a_U = mu_{>U}*zeta,

      sum_{n in s} |a_U(n)|^2 <= N*(1+log N)^3.

- `actual_divisorCoeff_mean_square` and
  `dyadic_divisorCoeff_mean_square`: apply the unrestricted-frequency bound
  to those genuine coefficients, with all logarithmic factors explicit.
- `vonMangoldt_energy`:

      sum_{n in s} Lambda(n)^2 <= log(N)*psi(N).

### MellinRemainderEnergy.lean
Namespace `Erdos972MellinRemainderEnergy`.

For the actual Vaughan remainder R_UV = mu_{>U}*zeta*Lambda_{>V}:

- `remainder_abs_bound`:

      |R_UV(n)| <= tau(n)*log(n).

  The proof uses divisor inclusion and sum_{d|n} Lambda(d)=log(n), not a
  pointwise n^epsilon divisor estimate.

- `remainder_energy`: for s subset {1,...,N},

      sum_{n in s}|R_UV(n)|^2 <= log(N)^2*N*(1+log N)^3.

- `remainder_mellin_mean_square`: for A<=B,

      integral_{A..B} |sum_{n in s} R_UV(n)*n^(it)|^2
        <= (B-A+4*N*(1+log N))*log(N)^2*N*(1+log N)^3.

All principal theorems compile without warnings and depend only on
`propext`, `Classical.choice`, and `Quot.sound`.
Audit: `Submission/AuditMellinEnergy.lean`.

## Exact limitation

Unlike the preceding compact-frequency results, these estimates apply to
frequency intervals whose endpoints grow arbitrarily with the scale.
However, they are ENERGY bounds, not cancellation estimates for the signed
cross-correlation. Their logarithmic losses remain explicit. A direct
Cauchy--Schwarz use does not supply the o(N) estimate or the strict lower gap
required by `FourFactorReduction.lean`.

No full Mellin representation of the floor strip, with a controlled signed
high-frequency contribution, has been asserted as a consequence. The new
bounds must not be substituted for such a theorem. No positive N^s
prime-correlation lower bound (s>1/2) or unbounded excess over the prime-power
budget has been proved.

The next mathematical task is still the signed two-prime/four-factor gap,
not another one-prime estimate or an unsigned energy budget.
