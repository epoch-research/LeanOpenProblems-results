# Literal template limit obstruction

`LiteralTemplateLimitExplore.lean` compiles. Its main declarations depend only
on `propext`, `Classical.choice`, and `Quot.sound` (see
`LiteralTemplateLimitAxiomCheck.lean`).

For a prime p and positive K,J, let

    A = blockSet ((p*K)^2*J)
          (fun i => outerLift ((p*K)^2) J (thickenedSet p K (B i))).

If every B i is empty or a union of unshifted nonzero-parameter parabolas,
then n<p and n in A imply n=0 (`template_small_mem`). Indeed the low digit
is n mod p and the row digit is zero; a nonzero-parameter parabola intersects
that row only at zero. The lemma covers the repaired one-curve-per-label
construction and, more generally, arbitrary unions of such parabolas.

Consequently, if p tends to infinity, any eventual coordinatewise limit of
these literal sets is contained in {0} (`limit_subset_zero`). Neither K,J nor
the coarse templates need remain fixed.

This rules out only direct coordinatewise compactness of these unshifted
encodings. Translations, different encodings, and other infinite constructions
are not covered. This is not a negation of the conjecture in Spec.lean.
