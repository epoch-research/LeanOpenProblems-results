# Exact reciprocal boundaries in shifted-multiplier constructions

Verified auxiliary work, NOT a proof or disproof of Erdos 68. Spec.lean
remains unchanged with its original sorry. No complete solution or new
submission check resulted from this continuation.

ShiftedMultiplierBoundary.lean compiles without warnings, has a built olean,
and all three printed axiom audits use only propext, Classical.choice,
and Quot.sound.

## Verified statement

For natural A,q,Q at least two, start with the rational remainder

    r=1/(q*A-1),    r'=r-1/(Q*A-1),    A'=Q*A.

If r'>0, then Q>q. Moreover every Q>q satisfies

    A'*r' > 1/q.

The exact difference has the positive expression

    A'*r'-1/q =
      [q*Q*(Q-q-1)*A^2+(q+Q)*A-1]
        / [q*(q*A-1)*(Q*A-1)].

Thus no positive step from this exact boundary can have normalized
remainder at most 1/q. This is no_positive_small_step.

## Scope and review outcome

The old rational shifted-chain construction permits bounded multipliers
between two and six. It does not automatically extend to multipliers
bounded above and below by constant multiples of the index. Proposed
shrinking remainder intervals have gaps near reciprocal boundaries; the
lemma above verifies one exact obstruction to assuming interval coverage.

No rational comparison with linearly growing multipliers was constructed.
Conversely, no irrationality theorem for that general class was proved.
This lemma does not assert that every rational orbit reaches an exact
reciprocal boundary. Existing nonterminating rational examples prevent
silently importing ordinary Engel termination arguments. The target's
infinite remainder strictly exceeds its next individual reciprocal row,
so this boundary lemma is not an arithmetic contradiction for the target.

The library search supplied no applicable general reciprocal-series
irrationality theorem. No new complete informal argument is awaiting
formalization, and no computation or compilation is pending.
