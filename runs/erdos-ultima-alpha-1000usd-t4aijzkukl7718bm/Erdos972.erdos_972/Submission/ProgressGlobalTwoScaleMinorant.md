# Global two-scale minorant and its fixed-parameter mean

## Status

The original conjecture in `Submission/Spec.lean` is still unresolved.
Neither of the results below is a proof or a counterexample to it.

## Verified pointwise result

`GlobalTwoScaleMinorant.lean` defines, for `t > 0`,

- `E_t(n) = expDivisorSum t n`,
- `S_t(n) = smoothMangoldt t n`,
- `z_t(n) = exp(-(t/2) log n)`,
- `H_t(1) = 0`, and otherwise
  `H_t(n) = ((1+z_t(n))^2 E_t(n)-E_(2t)(n))/(2t z_t(n))`.

It proves, with no restriction on `t log n`,

1. `H_t(n) <= 0` off prime powers;
2. `H_t(n) <= Lambda(n)` for every natural input;
3. `H_t(p) = S_t(p)` at genuine primes.

Proper prime powers are not claimed to have positive minorant value.

## Verified mean diagnostic

`GlobalMinorantMean.lean` proves the exact identity

```
z_t(n) H_t(n) = S_t(n)/2 - S_(2t)(n)
                 + (z_t(n)+z_t(n)^2/2) S_t(n).
```

With the genuine prime-input weight `primeWeight(n)`, and `alpha >= 1`,
the last term is nonnegative and at most

```
(3/(2t)) log(n) exp(-(t/2) log(n)).
```

For fixed `t > 0` this bound tends to zero. Its ordinary Cesaro mean
therefore tends to zero, without requiring irrationality.

For each irrational `alpha > 1`, each fixed `t > 0`, and each positive
error tolerance, the normalized mean

```
(1/N) sum_(1<=n<=N) primeWeight(n) z_t(floor(alpha*n)) H_t(floor(alpha*n))
```

is arbitrarily close, at arbitrarily large actual scales `N=u^6`, to

```
(dampedMean(t)-dampedMean(2t))/(2t).
```

The two smoothing estimates use ONE common good-row selector after all
thresholds are fixed, not an intersection of independently existential
scale sets. The displayed scalar is strictly negative by the previously
verified strict monotonicity of `dampedMean`.

The theorem `exists_negative_global_mean_scale` gives explicitly
arbitrarily large `u` at which the average is less than half this strictly
negative scalar.

## Meaning and limitations

The global minorant removes the earlier pointwise restriction on the
smoothing parameter. However, its positively damped fixed-parameter
average is negative on these scales. It does not produce a positive
prime-pair correlation lower bound.

This diagnostic does not exclude all other averaging procedures,
parameter choices, or proof methods. It does not concern a moving
parameter tending to zero with `N`.

## Verification

Both Lean files compile. Principal axiom audits for
`globalMinorant_le_mangoldt`, `globalMinorant_prime`,
`correctionMean_tendsto`, `exists_global_mean_scale`, and
`exists_negative_global_mean_scale` use only `propext`, `Classical.choice`,
and `Quot.sound`.

`Submission/Spec.lean` is unchanged and still contains its original
`sorry`. No completed proof has been submitted.
