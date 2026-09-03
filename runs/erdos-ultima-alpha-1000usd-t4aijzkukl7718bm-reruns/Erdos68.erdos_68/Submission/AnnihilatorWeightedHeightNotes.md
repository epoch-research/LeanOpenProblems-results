# Weighted height and shift-length trade-off

Verified auxiliary work, not a settlement of Erdős 68. `Spec.lean` remains
unchanged with its original `sorry`.

`AnnihilatorWeightedHeight.lean` compiles and its three principal axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

For integer weights z_i, offsets e_i <= L, and x >= 1, define

    W = sum_i |z_i| / x^e_i.

The triangle inequality gives |sum_i z_i| <= x^L W. If the weights
annihilate all the factorial-geometric rows d=4m^2,...,4m^2+m-1,
m>=5, and their retained sum is nonzero, the previously verified
arithmetic height bound therefore gives

    m^(m^3) <= x^L W.

Consequently W<=1 and x<=m^a imply m^3<=aL. Actual sample indices
and norm offsets are separate arguments, so arbitrary starting indices
are allowed. This prevents treating lower-degree variable-coefficient
annihilation as free of coefficient cost. It does not prove that every
useful construction has W<=1, does not bound actual errors from below,
and does not exclude partially cancelled or signed constructions.
