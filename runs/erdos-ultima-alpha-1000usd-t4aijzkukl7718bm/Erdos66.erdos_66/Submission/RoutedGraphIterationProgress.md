# Arbitrary graph functions do not repair fixed color routing

## Original task status

The original conjecture is unchanged and unresolved. This result is a
finite-product-group obstruction, not a natural-number disproof.

## Verified extension of the line-lift obstruction

RoutedGraphIterationExplore.lean replaces every new-color line graph by an
ARBITRARY graph function f(v,x). No polynomiality, bounded-sum property,
or relation between consecutive graph families is assumed.

The routing is still

    old color = new color - alpha * row,

with alpha nonzero. Every point in the assigned old color is copied to the
corresponding graph row. This routing alone implies:

* Every old mixed representation count survives in any prescribed pair
  of new colors at an explicit new target.
* An old count between distinct colors contributes twice to a new
  same-color representation count.
* Two successive lifts can double an inherited self-count.
* Arbitrary colorwise additions after each lift preserve the lower bound.

For recursive fixed-field spaces

    Space(0)=G,
    Space(n+1)=Space(n) x (F x F),

any nonempty seed forces a self-count at least 2^k at depth 2k. The union
of the colors therefore eventually has a target exceeding EVERY fixed

    K+C log |Space(2k)|.

The recursive group and finite-type structures are those explicitly
checked in LineRecoloringIterationExplore.lean.

## What is and is not excluded

Changing line fibers to nonlinear graph fibers, even separately for every
new color and at every stage, does not fix this particular scheme.

The theorem does NOT cover point-dependent routing within an old color,
clipping inherited copies, arbitrary changes of field or color alphabet,
or general natural-number sets. Its exponential peak is not claimed for
all conceivable graph-based constructions.

## Verification

RoutedGraphIterationExplore.lean compiles and has a current olean.
RoutedGraphAudit.lean audits eight principal declarations; its saved log
uses only propext, Classical.choice, and Quot.sound. No production sorry
or new axiom is present. The two unused-section-variable warnings in the
production file are harmless.

This completes the arbitrary-graph direction left open in the earlier
LineRecoloringProgress.md notes, within the stated fixed routing pattern.

## Related varying-field line result

ChangingFieldLineProgress.md now rules out an eventual logarithmic cap for
full AFFINE-LINE iteration with injective color/field changes and additions.
Its extra field-size peak uses line geometry. It is not a varying-field
extension for arbitrary new-color-dependent graphs.
