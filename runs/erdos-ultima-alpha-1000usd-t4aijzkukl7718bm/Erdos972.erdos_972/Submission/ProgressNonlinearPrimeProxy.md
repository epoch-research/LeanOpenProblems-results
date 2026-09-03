# Fixed-parameter nonlinear prime proxy — verified, not a settlement

The conjecture in `Submission/Spec.lean` is still unproved and undisproved.
Its import, statement, and original `sorry` are unchanged. No completed
proof was submitted.

## New file

`Submission/NonlinearPrimeProxy.lean`
Namespace: `Erdos972NonlinearPrimeProxy`.

Write

    E_t(n) = sum_{d|n} mu(d) exp(-t log d).

Define

    P_t(n) = exp(-t log n)/(1-E_t(n))  if n>1,
             0                       otherwise.

The file proves, for t>=0:

* The denominator is strictly positive for n>1.
* P_t(n)>=0.
* P_t(p)=1 at EVERY genuine prime p.
* For a nonprime n>1, P_t(n)<=exp(-(t/2)log n).

The composite bound uses minFac(n)^2<=n and the Euler-product bound

    1-E_t(n) >= exp(-t log(minFac(n))).

It includes proper prime powers; it is not merely a non-prime-power bound.
At the fixed parameter t=4, every nonprime input satisfies

    P_4(n) <= 1/n^2,

with the usual Lean zero-inverse convention and the explicit proxy value
zero at n=0 and n=1.

## Actual prime-input summability equivalence

For alpha>=1 set

    w_alpha(n) = P_4(floor(alpha*n)) if n is prime, and 0 otherwise,
    i_alpha(n) = 1 if n and floor(alpha*n) are prime, and 0 otherwise.

The file proves for every n

    0 <= w_alpha(n)-i_alpha(n) <= 1/n^2.

Thus the error series is summable, without an irrationality hypothesis
or a selected-scale restriction. It follows that

    Summable(w_alpha)
      iff {p : p prime and floor(alpha*p) prime} is finite.

Consequently nonsummability of this one FIXED nonlinear series would
settle the original conjecture. Nonsummability has NOT been proved.

## Positive expansion and its precise limitation

For n>1,

    P_t(n) = sum_{j>=0} exp(-t log n) E_t(n)^j.

This is a verified nonnegative geometric-series identity. It avoids a
moving smoothing parameter in the pointwise prime approximation.
However it does not supply a uniform arithmetic estimate over the
moment index j.

Indeed, at a genuine prime p, the file proves

    sum_{j<J} exp(-4 log p) E_4(p)^j <= J/p^4,

whereas the FULL sum is exactly one. Capturing a fixed positive fraction
at p therefore requires J of order p^4. Fixed-moment mean estimates
cannot simply be interchanged with the full geometric series to obtain
a prime-input lower bound.

This is a new fixed-parameter criterion, not a proof of the required
correlation estimate and not a counterexample.

## Verification

The file compiles without errors or warnings. All seven principal
printed axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`.

Command:

    lake env lean -o .lake/build/lib/lean/Submission/NonlinearPrimeProxy.olean Submission/NonlinearPrimeProxy.lean
