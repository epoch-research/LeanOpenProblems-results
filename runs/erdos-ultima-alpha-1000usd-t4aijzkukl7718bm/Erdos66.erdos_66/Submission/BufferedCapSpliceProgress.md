# Buffered-cap finite-prefix splicing

The original conjecture remains unresolved; Spec.lean is unchanged.

`BufferedCapSpliceExplore.lean` compiles, with a current olean. Its audit
checks the main declarations using only propext, Classical.choice and
Quot.sound.

For q : Nat -> Nat and A : Set Nat, assume additive headroom:

    for every m, eventually r_A(n)+m <= q(n).

Every finite F which itself satisfies the cap can then be spliced onto
the distant tail of A. At any prescribed minimum cutoff there is L beyond
that cutoff and the support of F such that

    B = (A intersect [L,infinity)) union F

is globally capped. Below L its representation counts equal those of F;
above L they are at most r_A(n)+2|F|. The required headroom is chosen
before selecting L. B agrees with F below L and with A above L.

Separate elementary lemmas show that agreement of A,B at all a>=L gives

    |r_A(n)-r_B(n)| <= 2L

at every target. Consequently their normalized logarithmic limits are
identical whenever either exists.

This removes a purely fixed-additive blocking problem when headroom is
available. It supplies no new lower bounds and no compatible chain of
accurate finite prefixes. In particular it cannot be iterated as a proof
of the conjecture without a new simultaneous lower-bound construction.
