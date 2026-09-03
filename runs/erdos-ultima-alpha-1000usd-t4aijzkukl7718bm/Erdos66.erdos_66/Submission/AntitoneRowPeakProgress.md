# Antitone row profiles retain directed reflection peaks

## Status

`AntitoneRowPeakExplore.lean` compiles, and its seven principal declarations
pass the permitted-axiom audit in `AntitoneRowPeakAudit.lean`. The conjecture
in `Spec.lean` remains unresolved and that file is unchanged.

## Stronger hypothesis than arbitrary rows, weaker than full symmetry

For X subset ZMod p and a reflection x -> t-x, define

    U = {x in X : (t-x).val < x.val}.

Assume every x in U has its reflected partner in X. Full symmetry of X is
NOT required. U and its reflected image are disjoint, their union has exactly
2|U| points, and that union is symmetric. The earlier exact two-carry identity
therefore yields, for any natural set A containing the row X placed at a,

    exists n, 2a <= n < 2(a+p), |U| <= r_A(n).

In particular a global envelope r_A(n)<=K+c log(n+2), c>=0, gives

    |U| <= K+c log(2(a+p)+2).

The bound is for U, not for the whole potentially nonsymmetric selected row.

## Position-dependent antitone palettes

Let C_i be a palette indexed by the natural position, with

    i<=j<p implies C_j subset C_i,

and suppose every C_i has the SAME reflection x -> t-x. Select x precisely
when x belongs to C_(x.val). If x is a selected upper endpoint, its partner
belongs to C_(x.val) by symmetry and to C_((t-x).val) by antitonicity. Thus
it too is selected, and the directed peak theorem applies.

This allows varying palette levels within the row. It does not assume that
the final selected row is itself invariant under reflection.

## Actual curve specialization

Horizontal parabola fibers are monotone under inclusion of their parameter
sets and are invariant under negation. A shared horizontal phase s moves
the common reflection center to 2s. Consequently any antitone parameter
family in such a row satisfies the directed peak theorem.

For zero center, the exact identity

    (-x).val < x.val iff p < 2*x.val

identifies U with the selected points strictly in the upper half.

## Scope and remaining gap

One common reflection is essential. Arbitrary clipped pieces need not obey
the partner implication. Independent phases at different positions may
break it, as can a different encoding. No lower bound on |U| for every
conceivable construction is proved here. These results do not contradict
the finite bounded-profile operator theorem, whose accuracy is normalized
by the full-modulus logarithm and whose hypotheses do not assert a common
reflection for an arbitrary selected natural interval.

This is another construction-specific diagnostic, not the negation of the
original existential proposition. No compatible infinite witness has been
constructed and no main proof has been submitted.
