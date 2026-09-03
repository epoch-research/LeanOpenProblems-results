# Multi-row arithmetic continuation: unresolved

This is informal review, not a new Lean theorem or a settlement of Erdos 68.
Spec.lean remains unchanged with its original sorry. No proof or disproof
has been obtained, and no submission check was run in this continuation.

## Congruence review

The previously verified predecessor, prime-power Dold, and combined-column
congruences concern different normalizations. There is still no construction
preserving all needed congruences in the exact target while retaining tail
bounds sufficient for the available irrationality criteria. Increasing a
carry modulus increases the available tail interval. The rational comparison
constructions already show that merely polynomial bounds with several of
these congruences cannot be silently substituted for the sharper bounds.
No new inheritance or infinite residue-violation theorem was obtained.

## Multi-row detection review

The exact annihilator height theorem suggests detecting several successive
rows when the integer coefficient height exceeds the first row's factorial
budget. Such a detection argument has not been proved here. In particular,
the small-nondivisible-first-row examples cannot be treated as exact factors.

Even a hypothetical simultaneous detection theorem would need an arithmetic
application: detecting more row phases also requires clearing more output
boundaries, or a different argument selecting an integral detected output.
The present counting estimates do not supply that selection. This review
proves no impossibility theorem for alternative multi-row constructions.

For a single output, short consecutive weights can annihilate a rational
row response without annihilating that row in all phases. Thus the existing
all-phase invertibility theorem does not establish nonvanishing at the
particular phase cleared by scalar pigeonholing. No new single-phase height
bound compatible with boundary clearing was established.

## Other checks

The exact conjecture was reread; no change to its statement or imports was
made. A local Mathlib search supplied no applicable theorem. Another attempt
to retrieve the problem reference failed at DNS resolution. No new numerical
search, Lean declaration, or complete informal solution resulted. There are
no computations or compilations pending from this continuation.
