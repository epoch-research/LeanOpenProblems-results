# Adaptive detector's divisor tail — verified obstruction, not a settlement

The original conjecture remains unresolved. `Submission/Spec.lean` is unchanged with its original `sorry`. No proof or irrational counterexample was obtained, and no incomplete proof was submitted.

## New file

`Submission/LogDegreeDivisorTail.lean`, namespace `Erdos972LogDegreeDivisorTail`, compiles without warnings/errors. All six printed principal axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.

The file analyzes the ACTUAL adaptive logarithmic-degree detector from `LogDegreePrimeDetector.lean`, not a model sequence.

Let

    A(n) = (4/3)^(4 L(n)),
    c(n,d) = profileCoeff (fun m => E_(tau(n))(m)^(4 L(n))) d.

It proves the exact finite Mobius-inversion identity, for n>1:

    logDetector(n) = A(n) * sum_(d|n) c(n,d).

Also `c(n,1)=1`, and `n < A(n)` for every natural n.

## Exact prime-output cancellation

For every prime q,

    A(q) c(q,q) = 1 - A(q).

Thus the divisor q itself cancels the normalization factor down to the detector's exact value one.

If `1 <= D < q`, truncating to divisors at most D retains only the unit divisor:

    truncatedDetector(D,q) = A(q),
    |truncatedDetector(D,q) - logDetector(q)| = A(q)-1 > q-1.

The error is consequently unbounded on prime outputs for every fixed cutoff D>=1. This is an unconditional result using ordinary prime infinitude.

## Energy obstruction

For every prime q and every `1 <= D < q`,

    (q-1)^2 < sum_(1<=n<=q) |truncatedDetector(D,n)-logDetector(n)|^2.

In particular, for every fixed D>=1 and every real C, there is N>0 such that this squared-error prefix sum exceeds C*N. This disproves the direct adaptive-detector analogue of a uniform L2 small-divisor-tail bound.

## Scope

The existing `UniformSmoothCorrelationTail.exists_uniform_correlation_cutoff` fixes t>0 before choosing the cutoff. Its hypotheses do not cover the adaptive parameter, degree, and normalization. The exact calculation above shows that simply transferring its uniform energy conclusion to this detector would be false.

This does NOT rule out averaged SIGNED cancellation, an alternative expansion, or another proof route. In particular it does not refute the original conjecture. A sufficient signed large-divisor estimate or another pointwise prime-pair lower bound remains missing.
