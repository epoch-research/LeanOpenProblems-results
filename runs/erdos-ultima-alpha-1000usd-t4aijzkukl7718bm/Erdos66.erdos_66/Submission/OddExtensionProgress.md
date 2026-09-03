# Odd-degree field extension: exact slice and error-budget preservation

## Original task

The original conjecture remains unresolved. Spec.lean is unchanged with its
original sorry. No valid proof or disproof has been submitted.

## Verified production files

* OddFieldExtensionExplore.lean
* OddExtensionCharacterFiberExplore.lean
* OddExtensionFlatSetExplore.lean
* SquareClosedSubspaceExplore.lean

All four compile with current oleans. OddExtensionAudit.lean audits sixteen
principal declarations using only propext, Classical.choice, and Quot.sound.

## 1. Square classes and exact old slices

For an algebraic field map F -> K with odd finrank, the checked norm argument
proves

    IsSquare(map x) iff IsSquare(x).

The direct proof uses that a square odd power of x makes x a square. For
finite fields the quadratic characters are therefore equal on old elements.

The parabola y=x^2/u over K has exactly the corresponding F-parabola in its
old coordinate-plane slice. A parameter u outside the range of F has NO
nonzero point in that slice. These are membership assertions, not assertions
that all K representations at an old target have old endpoints.

## 2. Character error is preserved exactly

For U subset F, its mapped signed additive fibers are the same on mapped
old targets and zero off the old-field range. Consequently

    sum_(w in K) |charFiber(map U,w)|
      = sum_(w in F) |charFiber(U,w)|.

At EVERY K-plane target, the old parameter-multiplicity graph count thus
retains its old absolute error budget about |U|^2. There is no factor
depending on the extension degree or the new field cardinality.

## 3. Actual repaired finite sets

Keep an old unused auxiliary parameter w and old partial repair T, and map
both into K. The mapped partial repair is exactly the image of the old
repair, including its negative half. The actual set

    B_K = parabolaSet(map U) union repairPoints(map w,map T)

has EXACT old slice B_F. Assuming nonzero parameters, no opposite parameter
pairs, nonempty U, and the stated unused-parameter repair hypotheses:

    r_(B_K)(0) = 1+2|T|,
    |r_(B_K)(z)-|U|^2| <= oldCharacterBudget+10|U|+8  (z != 0).

Thus a previously tuned origin repair and finite flatness budget survive an
odd-degree extension of ONE parabola model. This is different from a
Cartesian product of separate curves, so the earlier product-cube bound
cannot simply be applied to it.

## 4. Coordinate-subspace limitation

In characteristic other than two, a vector subspace V containing 1 and
closed under squaring is closed under multiplication by polarization. If
the ambient extension is algebraic, V is exactly an intermediate field.
For finite-dimensional extensions, the checked consequence is

    finrank_F(V) divides finrank_F(K).

This applies to full square-graph inheritance on a coordinate subspace.
It is not a bound for arbitrary partially retained curves or nonlinear
integer encodings.

## Missing main step

The extension keeps the same U and the same mean |U|^2. It does not produce
a growing logarithmic mean, an integer encoding with the required
inhomogeneous prefix mass, or correct natural counts through intermediate
scales. Enlarging U with outside parameters preserves old slice membership,
but no suitable growing-family error estimate was proved. Odd extensions
also have large size jumps; arbitrary vector-space prefixes cannot silently
be treated as subfields.

No compatible infinite natural-number witness or universal logarithmic
fluctuation contradiction follows from these finite results.

## Subsequent non-Cartesian quadratic-lift check

QuadraticFieldLiftProgress.md records a checked 22-declaration investigation
of a genuine quadratic-field parabola lift. Its individual joint cap stays
two and its old slice is exact, so it is not the full affine-line model.
But all old scalars become squares in the quadratic extension; unchanged
old label unions have exact off-slice holes and a double nominal count at
an old target. This does not exclude fresh-label or density-changing
constructions and does not settle Spec.lean.

## Subsequent growing-label finite extension

See `GrowingFieldExtensionProgress.md`. There is now a checked fresh-block
extension with a growing parameter set and growing origin repair, exact old
field-plane slice, and explicit relative-error bounds. It improves the
unchanged-label limitation in this finite setting. It does not supply
ordinary integer carry control, logarithmic scale tuning, or intermediate
natural-prefix estimates, and does not settle Spec.lean.
