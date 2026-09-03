# Review of shared products and nested-field alternatives

The original conjecture is unresolved. This document records mathematical
review, not new Lean-verified construction or impossibility theorems.

## Shared-label Cartesian products

The existing two-factor construction preserves a group slice and keeps its
mean at h^2, rather than h^4. The literal encoding gap and Cartesian-cube
peak remain genuine. Letting h grow can exceed a fixed number of cube
peaks, but retaining arbitrarily many full factors requires checking 2^k
against log of the actual integer scale. No such all-scale construction
was found.

A shear of the new parabola replaces its single first-row point with at
most two points per parameter. This may remove a literal empty interval,
but it does not automatically supply the square-root growth of prefix
mass through an entire first row. Reordering coordinates or thinning a
set cannot be treated as preserving natural pair counts without proof.

## Nested finite fields

A potentially different idea is one parabola over a tower of finite fields,
not a Cartesian product of separate parabolas. One quadratic equation then
has at most two roots regardless of extension degree, avoiding the direct
product-cube argument. Parameters outside the old field add no new points
to the old field-plane slice except the common origin.

However, odd-degree extensions are needed to preserve quadratic characters
of old nonzero parameters. In an even-degree extension every old nonzero
parameter becomes a square, so the previously low-energy signed parameter
pattern cannot be assumed to persist. Odd extensions of degree at least
three leave a large interval between consecutive field sizes.

Literal encodings through nested coordinate subspaces face a separate
problem. To retain a full square graph on V x V requires V to be closed
under squaring (or an appropriate twisted condition). In odd characteristic,
a vector subspace containing 1 and closed under squaring is closed under
multiplication by polarization. In a finite ambient field it is a subfield.
Thus one cannot assume full square-graph prefix inheritance at an arbitrary
chain of intermediate vector-space dimensions.

This observation does not yet quantify partially retained curves, allow
arbitrary nonlinear orderings, or exclude arbitrary witnesses. No new
all-scale lower bound or compatible density-adjusted field-tower chain has
been established.
