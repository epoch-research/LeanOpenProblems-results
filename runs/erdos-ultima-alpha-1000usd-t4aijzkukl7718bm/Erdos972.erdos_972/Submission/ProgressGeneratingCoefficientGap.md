# Generating-function coefficient diagnostic — conjecture unresolved

`Submission/Spec.lean` remains unchanged and contains its original `sorry`.
No proof, sufficient prime-pair lower bound, or irrational counterexample
was obtained. No incomplete proof was submitted.

## New verified file

`Submission/GeneratingCoefficientGap.lean`, namespace
`Erdos972GeneratingCoefficientGap`, imports only `FormalConjecturesUtil`.

For natural k define real polynomials

    P_k(X) = X^2 (1+X)^k,
    Q_k(X) = P_k(X) - X^2.

The file proves:

* Both families have nonnegative coefficients at every degree.
* The degree-two coefficients are respectively one and zero, for every k.
* For every FIXED real t>0,

      Q_k(t)/P_k(t) = 1 - (1+t)^(-k) -> 1.

* Pointwise, for t>0,

      0 <= Q_k(t)/P_k(t) <= k*t.

* For the explicit positive shrinking parameter t_k=1/(k+1)^2,

      Q_k(t_k)/P_k(t_k) -> 0.

The file compiles, and all three printed principal axiom audits list only
`propext`, `Classical.choice`, and `Quot.sound`.

## Scope

These are actual finite polynomials, not numerical experiments. They show
that coefficient positivity and fixed-positive-parameter asymptotic
equivalence, by themselves, do not preserve the first relevant coefficient
or justify a shrinking-parameter substitution.

The polynomials are an abstract diagnostic model, NOT generating functions
proved to enumerate the arithmetic floor-prime pairs. Their coefficients
are not asserted to count the conjecture's pairs. No theorem specific to
the genuine prime-pair generating function is refuted here.

The attempted generating-function route still needs a genuine uniform
arithmetic estimate in the prime-detecting parameter range. This diagnostic
does not supply that estimate or settle the original conjecture.
