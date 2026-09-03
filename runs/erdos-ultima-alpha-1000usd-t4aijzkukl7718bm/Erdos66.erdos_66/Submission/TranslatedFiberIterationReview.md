# Follow-up review: translated fibers and recoloring

## Status

This is mathematical review, not a new Lean theorem or a solution.
Spec.lean remains unchanged with its original sorry. The completed new
Lean development is recorded in ResidueProjectionProgress.md.

## Why translations are worth distinguishing

Translated copies of an old cyclic palette need not retain a fixed proper
residue support. Thus the already checked fixed-support obstruction does
not itself exclude an iteration that changes translations. Similarly,
keeping only the old zero slice, rather than a full old cylinder, avoids
the full-lift cardinality objection at a much larger ambient scale.
Neither observation supplies estimates on the intermediate natural scales.

## The existing unit-mean affine-line theorem

AffineLineAssemblyExplore proves a finite product-group transfer with error
at most 2 q g, where q is the field size and every old same-color self-count
is at most g. It preserves the global convolution mean exactly. The old
zero slice is not preserved: only old color zero appears there.

The existing theorem does not return a coloring with equally good bounds.
For illustration, put L_u={(x,ux+u^2)} and recolor a lifted point by
v=u+alpha*x, with alpha nonzero. For a fixed new color v,

    x=(v-u)/alpha,
    y=u*v/alpha+(1-1/alpha)*u^2.

For two new colors and a fixed target, the old labels satisfy a polynomial
of degree at most two. In the nondegenerate case, bounding the resulting
counts therefore needs old MIXED-color bounds, not just the old same-color
hypothesis. At alpha=1, different new colors give a linear condition but
equal colors can be degenerate. A degree bound alone neither proves the
needed mixed regularity nor regenerates the original invariant.

Even an available upper bound with a fixed multiplicative loss per step
would not automatically suffice: the allowed error is sublogarithmic,
while the ambient logarithm increases only by 2 log q at this lift. This
is a warning about a particular iteration budget, not a universal lower
bound or an impossibility theorem for other recolorings.

## Previously established facts that must not be overextended

SidonColorProgress excludes a sublogarithmic number of genuine Sidon
colors on a witness's long prefixes. It does not exclude all bounded-self-
count color systems. DenseSidonGridProgress already shows that a small
self-count cap need not yield a bounded Sidon coloring. Thus one cannot
turn the Sidon-color theorem into a general obstruction for the current
same-color cap hypothesis.

The joint residue-pair density-one theorem likewise provides no pointwise
mixed-color cap for the successive finite palettes of a construction.

## Remaining requirements

No recoloring invariant, prefix-preserving natural carry transfer,
intermediate-scale profile estimate, or compatible density-adjusted chain
has been constructed. The new all-modulus energy/density results do not
close these gaps and do not settle the original conjecture.

## Subsequent verified update

LineRecoloringProgress.md now records an actual one-step recoloring with
joint mixed cap 2g, a through-origin variant retaining each old color on
the zero slice, and the exact extra representation mass at that slice.
It also proves exponential lower peaks in literal fixed-field iterations,
even with arbitrary colorwise additions. Thus the earlier absence of a
recoloring theorem is no longer the precise limitation of this branch;
unchanged iteration of the now-checked recoloring is itself obstructed.
This does not settle the original conjecture or rule out clipped/refreshed
or genuinely different changing-field constructions.
