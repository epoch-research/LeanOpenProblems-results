# Signed linear-tail comparison (verified; not a settlement)

`SignedLinearTailComparison.lean` compiles and has a built olean.
Both main axiom audits list only `propext`, `Classical.choice`, and
`Quot.sound`.

Define t(n) = -2 at even n, and t(n) = -2n-1 at odd n.
Set c(0)=0 and c(n)=n*t(n-1)-t(n) for n>0. Then

* c(n)=1 at every odd n;
* for positive even n, c(n)=-(n-1)(2n+1)+1;
* n divides c(n+1)-1 for every n;
* c(p)=1 for every prime p>=3;
* sum c(n)/n! = -2;
* the factorial-scaled tail is exactly t(n), which is negative;
* |t(n)| <= 2n+2.

Thus the prime unit coefficients and predecessor congruences, even with
absolute tails bounded linearly, do not imply irrationality. In particular,
an operation that carries Lambert coefficients into small signed tails
cannot be fed into the existing positive-tail criteria without an additional
sign argument. The even coefficients of this comparison are negative.

The original positive-coefficient conjecture is not disproved. Spec.lean
still contains its original sorry; no settlement has been obtained.
