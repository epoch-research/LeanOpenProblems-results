# Quadratic-floor recurrence check — conjecture remains unresolved

`Submission/Spec.lean` remains unchanged with its original `sorry`. No proof or
irrational counterexample has been obtained.

New standalone file: `Submission/QuadraticFloorRecurrence.lean`, importing only
`FormalConjecturesUtil`, namespace `Erdos972QuadraticRecurrence`.

Lean-verified results:

* If alpha > 1, k >= 2 is natural, and alpha^2 + 1 = k*alpha, then, with
  T(n) = Nat.floor(alpha*n), one has T(T(n)) + n = k*T(n) for every n.
* If k is odd, p > 2 is prime, and T(p) is prime, then T(T(p)) is not prime.

Both declarations compile and their printed axiom dependencies are exactly
`propext`, `Classical.choice`, and `Quot.sound`.

This does NOT disprove the conjecture. It rules out chains of three prime
values for these slopes, but allows infinitely many separate prime pairs.
The recurrence has infinitely many starting orbits; no argument reducing
all prime pairs to finitely many orbits, or otherwise proving finiteness,
was found. It also provides no prime-pair lower bound.
