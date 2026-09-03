# Logarithmic dilation check — original conjecture remains unresolved

`Spec.lean` is unchanged and still contains its original `sorry`. No proof or
irrational counterexample was obtained, and no proof submission was made.

## New verified results

### CesaroLogarithmicMean.lean
Namespace `Erdos972CesaroLogarithmicMean`.

- `weighted_mean`: for nonnegative weights of divergent total mass, the
  weighted means of a convergent real sequence tend to the same limit.
- `logarithmic_abel`: exact finite reciprocal summation-by-parts identity.
- `cesaro_to_logarithmic`: if ordinary Cesaro means converge to L, the
  reciprocal-weighted means normalized by harmonic numbers also tend to L.
- `harmonic_div_log_tendsto`: H_N/log N tends to one.
- `cesaro_to_logarithmic_log` and `cesaro_Ioc_to_logarithmic`: transfer to
  conventional logarithmic normalization, including positive-index sums.

### LogDilatedMangoldtObstruction.lean
Namespace `Erdos972LogDilatedMangoldtObstruction`.

- `distinct_prime_dilates_log_mean`: for distinct primes r,s,

      (1/log N) sum_{1<=n<=N} Lambda(rn)Lambda(sn)/n -> 0.

- `moebius_mangoldt_log_mean`:

      (1/log N) sum_{1<=n<=N} mu(n)Lambda(n)/n -> -1.

- `not_unrestricted_log_dilation_criterion`: explicitly negates the proposed
  unrestricted implication from vanishing distinct-prime dilation means of
  a real sequence f to vanishing logarithmic correlation with mu.

Both files compile. Their printed principal axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.

## Scope and limitation

This rules out merely repairing the earlier unbounded Katai-style inference
by changing ordinary means to logarithmic means. It does NOT rule out a
criterion with additional prime-output-specific hypotheses. In particular,
one-prime divisor distribution for Lambda(floor(alpha*n)) is information
not present for the diagnostic sequence Lambda(n).

Trying to exploit that information still leaves the cross products
Lambda(floor(alpha*r*n))*Lambda(floor(alpha*s*n)) after Cauchy--Schwarz.
No adequate estimate for these products, or for the original signed
four-factor remainder, was established. No prime-pair lower bound follows
from the new summability transfer lemma alone.

A bounded request to the public problem reference again failed with DNS
resolution failure. No external literature settlement was independently
verified.
