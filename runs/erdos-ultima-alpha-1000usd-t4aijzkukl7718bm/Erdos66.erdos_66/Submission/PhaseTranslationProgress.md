# Independently translated finite palettes

## Status and verification

The original conjecture remains unresolved; `Spec.lean` is unchanged.
`TranslatedPrefixPaletteExplore.lean`, `PhaseCompletePaletteExplore.lean`, and
`PhaseHeightRealizationExplore.lean` compile. The nine principal declarations
listed in `PhaseTranslationAudit.lean` use only `propext`, `Classical.choice`,
and `Quot.sound`.

## Exact translation and endpoint bounds

For `shift(C,s) = {s+x : x in C}`, cardinalities and actual mixed means are
unchanged, and the cyclic mixed count at z becomes the old count at z-s-t.
A translated endpoint prefix is either one old interval, or the union of a
terminal and an initial interval. Exact wraparound identities give error at
most 3E if every old endpoint prefix has error at most E. This is uniform in
both independent translations, the target, and the endpoint.

## Phase closure

Closing the prefix-balanced complete palette under all cyclic translations
therefore gives a palette Q with at most M(M+1) members, containing the full
group, with the same minimum cardinality, sparse logarithmic mean, and
multiplicative cardinality coverage. Starting at tolerance eta/3 gives final
mixed endpoint error eta. There is no density or coefficient inflation.

Q is NOT asserted to be nested. The fitting version additionally accommodates
any fixed weight capacity W before choosing the modulus.

## Mixed integer assemblies

A checked two-family assembly estimate controls independent choices C_i,D_i
from a joint palette. The unconditional height-realizer selects one list C_i
before the interval arrangements and before two arbitrary lists of phases.
For every later pair of disjoint interval arrangements and independent phases
on their pieces, its actual natural-number mixed count divided by log M is
within delta of the exact weighted discrete overlap profile.

Phases are constant on each specified interval piece. This does not allow an
arbitrary phase at each individual point while keeping a fixed error budget.
The finite family and heights are fixed before the modulus.

## Still missing

All mixed estimates use one modulus. Phase closure does not supply spatial
error relative to a short interval's own mean, compatibility between changing
moduli, or finite-prefix feasibility with thresholds chosen independently of
the final cutoff. No infinite witness or universal contradiction follows.
