# Finite mixed-count thinning

## Status

The original conjecture in `Spec.lean` remains unresolved and unchanged.
This is a finite selection lemma, not a proof of the existential limit.

## Checked result

`MixedThinningExplore.lean` proves that, given a finite abelian group G,
a set B, and a finite family C_i, one can choose D subset B such that all
mixed counts D*C_i simultaneously approximate theta times B*C_i whenever

    theta * (B*C_i)(z) <= V,
    2 * |I| * |G| * exp(-epsilon^2 * V / 8) < 1.

The resulting error is strictly less than epsilon*V at every (i,z).
The retention parameter satisfies 0<=theta<=1, and 0<epsilon<=1.
The theorem is `Erdos66MixedThinning.exists_mixed_thinning`.

The proof uses independent singleton Bernoulli monomials and the existing
finite exponential-potential selection theorem. It also supplies the generic
`exists_simultaneous_linear_thinning` statement.

The file compiles and has a built olean. `MixedThinningAxiomCheck.lean`
checks the principal declarations; only propext, Classical.choice, and
Quot.sound occur.

## What it does and does not supply

For a self-flat B of mean mu, mixed counts D*B have mean approximately
 theta*mu. The expected self-count scale for D is instead theta^2*mu
(with a diagonal correction). Thus mixed-count concentration may be useful
at a retention level where self-count concentration is still critical.

No self-flatness conclusion for D has been proved in this file. At desired
self mean c*log|G|, the ordinary self-count concentration criterion still
does not allow relative error tending to zero for fixed c. Passing to a
much denser intermediary also spends more representation-count budget than
is available at the same integer scale. No compatible infinite thinning
construction has been obtained.
