# Weighted endpoint obstruction

`WeightedEndpointObstructionExplore.lean` now compiles. The principal theorems
were audited in `WeightedEndpointAxiomCheck.lean`; they use only `propext`,
`Classical.choice`, and `Quot.sound`.

For an infinite set A, positive antitone weight w, and nonnegative g with
w(n)g(n) tending to infinity, its weighted self-convolution times g has
arbitrarily large peaks. Fix a in A and pair it with arbitrarily large b in A.
The single contribution w(a)w(b) supplies the lower bound.

In particular, for any alpha > 0, with w(n)=(n+2)^(-alpha), the weighted
self-convolution cannot have a finite limit after multiplication by
(n+2)^(2 alpha)/log(n+2).

This rejects the proposed pointwise transfer to a weighted fractional
profile. It does NOT disprove the original, unweighted conjecture.
`Spec.lean` remains unchanged and unresolved.
