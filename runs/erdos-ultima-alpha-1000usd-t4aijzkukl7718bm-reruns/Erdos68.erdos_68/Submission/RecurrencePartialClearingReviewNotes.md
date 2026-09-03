# Recurrence and partial boundary-clearing review

Informal review only, NOT a new Lean theorem and NOT a settlement of Erdos 68.
`Spec.lean` remains unchanged with its original `sorry`.

## Rationality propagation

The exact recurrence d_(n+1)=(n+1)d_n+n, d_n=n!-1, gives rational ordinary
remainders under a hypothetical rational value of alpha. Clearing them by
the product of the original denominators gives the known rapidly growing
integer continuant solution, not a descending height. No new reduced-height
estimate or rationality propagation to derivatives was obtained.

The direct generating-function and Borel identities introduce factorial-power
constants or derivatives. Rationality of F(1) alone is not a proof of their
rationality. The existing exact shifted-tail identities do not remove this
issue. No new functional-relation argument was established in this pass.

## Partial boundary clearing

A possible variation on the boundary lattice is to clear a rational boundary
only into (1/p)Z rather than Z. If the remaining denominator genuinely contains
a fresh prime p, multiplying by p can give an integer form whose nonvanishing
under rationality is detected modulo p.

The unresolved selection step is essential: pigeonholing modulo C/p need not
produce a vector whose aggregate boundary is nonintegral. It may produce a
vector already clearing into Z, including a zero coefficient pair. No bounded
lift in the required nonzero quotient class was proved.

Restricting all final support indices to primes makes the last-coefficient
criterion applicable to a nonzero bounded vector, but reduces the number of
available coordinates. A nonuniform variant allowing general final indices
would require additional unit/congruence information for their Lambert
coefficients. Neither version supplied compatible height, integrality, and
error estimates here. These observations are not impossibility theorems for
all partial-clearing constructions.

## Status

No complete proof or disproof, new infinite residue violation, or usable
small nonzero integer-form family was obtained. No new numerical search or
submission check was run. Nothing is running or pending compilation.
