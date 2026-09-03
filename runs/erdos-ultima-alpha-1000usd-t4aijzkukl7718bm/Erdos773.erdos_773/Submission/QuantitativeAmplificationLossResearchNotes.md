# Quantitative amplification-loss continuation

This is NOT a settlement of Erdős 773. The conjecture in Spec.lean is unchanged
and still admitted for 0 < epsilon <= 1/3. No proof submission was made.

## Verified new module

`QuantitativeAmplificationLoss.lean` imports the already clean
`PowerAmplificationBarrier` module, not Spec.lean. All six printed audits use
only propext, Classical.choice, and Quot.sound. The module builds without
warnings or admissions; its .olean is built.

Write M(N) for the actual square-Sidon maximum and rho(N)=M(N)/N.

`frequently_primorial_loss` proves, for every c>0, at arbitrarily large N,

    M(N^2) < c N M(N) exp(-log N/(1024 log log N)).

The existing frequent density-gain barrier with theta=3/2 and constant c/2
is combined with the existing upper bound

    rho(N) <= 2 exp(-log N/(512 log log N)).

The auxiliary half-power inequality uses sqrt(2)<=2. Multiplication by N^2
then gives the actual cardinality statement.

`eventually_log_power_le_primorial` proves, for every fixed real a<1,

    (log N)^a <= log N/(1024 log log N)

at all sufficiently large N. It applies the GLOBAL (not Real-namespaced)
Mathlib theorem `isLittleO_log_rpow_atTop` with exponent 1-a, composes with
log of the natural-number cast, and multiplies by (log N)^a.

Consequently `frequently_log_power_loss` proves, for every a<1 and c>0,

    M(N^2) < c N M(N) exp(-(log N)^a)

at arbitrarily large N. `no_log_power_amplification` explicitly negates the
existence of an eventual lower bound of that form for a positive constant c.

## Scope

These statements prohibit amplification schemes with these particular losses.
They do not prohibit all subpower losses, nor do they negate the original
near-linear conjecture. The previously proved equivalence with arbitrary
subpower amplification remains an equivalence between two unproved claims.

A further review of bounded-multiplicity extraction and polynomial integer
specialization produced no valid new selector. Neither bounded multiplicity,
small pair codegrees, nor formal polynomial Sidonness supplies the required
near-linear integer Sidon set by itself. No new impossibility theorem for
all such constructions is asserted here.

The strongest completed actual lower bound remains

    eventually M(N) >= (5/4) N/(N log N)^(1/3).

It still has a logarithmic loss, and no original exponent improved in this
continuation.

Log: /tmp/quantitative-amplification-loss.log.
