# Cyclic modulus padding

The original conjecture is not settled. `Spec.lean` is unchanged.

`CyclicPaddingExplore.lean` compiles. If a subset B of ZMod M has all cyclic
self-counts within E of a nonnegative mean mu, repeat its representatives K
times and embed them in ZMod N, where N=M*K+d and 0<=d<M. The resulting set
has all cyclic self-counts within

    2*K*E + 3*mu + 2*E

of K*mu. In particular K=N/M gives a theorem at every positive destination
modulus, with no divisibility condition between source and destination.

The proof periodizes the integer triangular profile at the two lifts n and
n+N. Their coarse quotients differ by K or K+1; the two triangular weights
sum to within one of K. The error bound is independent of the padding d.

Principal results:
- Erdos66CyclicPadding.padded_cyclic_error
- Erdos66CyclicPadding.padding_to_any_modulus

Both were axiom-audited in CyclicPaddingAxiomCheck.lean and use only propext,
Classical.choice, and Quot.sound.

This is a finite transfer result, not an infinite-prefix extension theorem.
In particular it gives no control on mixed counts of independently chosen
templates at different scales.
