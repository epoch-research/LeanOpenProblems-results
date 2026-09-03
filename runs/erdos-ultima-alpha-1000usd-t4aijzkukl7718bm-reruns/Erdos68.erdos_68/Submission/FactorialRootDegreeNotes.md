# Rational degree cost of factorial-root cancellation

Verified auxiliary work, NOT a proof or disproof of Erdős 68.
`Submission/Spec.lean` remains unchanged with its original `sorry`.

`FactorialRootDegree.lean` imports only `FormalConjecturesUtil`, compiles
without warnings, and has a built olean. All five printed principal axiom
audits list only `propext`, `Classical.choice`, and `Quot.sound`.

## Verified results

For each d >= 2, Bertrand's postulate provides a prime p with

    p <= d < 2*p.

Its valuation in d! is exactly one. Eisenstein and Gauss's lemma therefore
prove that

    X^d - d!

is irreducible over the rationals. If x is any real number satisfying
x^d=d!, its minimal polynomial is exactly this polynomial.

For a finite set s of distinct integers d >= 2, choose real numbers x_d
with x_d^d=d!. Every nonzero rational polynomial P satisfying

    P(x_d)=0 for every d in s

has degree at least sum_(d in s) d. The same bound holds under

    P(1/x_d)=0 for every d in s.

The first assertion uses pairwise coprimality of the irreducible binomials,
product divisibility, and additivity of degree. The reciprocal assertion
uses polynomial reversal, whose degree cannot exceed the original degree.
No positivity or particular choice of the real roots is required.

Principal new declarations:

* `degree_ge_of_inv_factorial_root`
* `factorial_binomials_coprime`
* `degree_ge_sum_of_factorial_roots`
* `degree_ge_sum_of_inv_factorial_roots`

## Scope

Selecting only one real reciprocal root from each Lambert row does not
reduce the rational constant-coefficient polynomial degree cost to one per
row: the costs still add to the sum of the row periods. This is an exact
vanishing result only. It does not give an approximation-height bound,
control variable-coefficient operators, or establish nonvanishing of an
integrally cleared form in the original target.

A further review of multi-row detection and root-of-unity boundary values
provided no compatible arithmetic bridge. More detected phases still have
to be made integral; algebraicity of boundary values under rationality does
not supply an interior analytic-continuation argument. The original
conjecture has not been settled or submitted.
