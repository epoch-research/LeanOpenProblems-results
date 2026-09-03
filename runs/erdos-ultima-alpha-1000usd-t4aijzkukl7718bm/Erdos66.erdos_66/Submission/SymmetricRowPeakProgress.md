# Reflection peaks in literal whole-row encodings

## Status

`SymmetricRowPeakExplore.lean` compiles. Its seven principal results pass the
permitted-axiom audit in `SymmetricRowPeakAudit.lean`. The original conjecture
is still unresolved; `Spec.lean` is unchanged.

## Exact finite statement

Let X be a finite subset of ZMod p invariant under x -> t-x. Place its natural
representatives in [a,a+p), giving R. Exact cyclic periodization and natural
translation give

    |X| = r_R(t.val+2a) + r_R(t.val+p+2a).

Consequently any A containing R has a target 2a <= n < 2(a+p) with

    |X| <= 2 r_A(n).

A global envelope r_A(n) <= K+C log(n+2), C>=0, thus forces

    |X| <= 2(K+C log(2(a+p)+2)).

These statements do not assume that A is finite.

## Actual parabola rows and phases

For the existing union of curves y=x^2/u, every fixed horizontal fiber is
invariant under x -> -x. Translating that fiber by s changes the reflection
center to 2s and preserves its cardinality. Hence every whole such translated
fiber placed in a natural row has the displayed integer peak. Arbitrary
horizontal phases do not remove this peak.

This gives an additional diagnostic for growing-height literal encodings:
large full rows have an actual representation cost, beyond the previously
noted weakness of the available interval error bounds.

## Scope limitations

The statement concerns whole reflected rows (or sets containing them). It
does not assert symmetry for an arbitrary clipped interval of a row. A
translation of a full cyclic template can cause a specified natural interval
to cross old row boundaries, and that interval cannot silently be treated as
one whole symmetric row. Independently varying phases within a row can also
break the hypothesis. Origin repairs and dense completion are not asserted
to preserve exact row symmetry; the peak still applies if the resulting set
contains the symmetric row in question.

No universal obstruction or compatible infinite construction was proved.
