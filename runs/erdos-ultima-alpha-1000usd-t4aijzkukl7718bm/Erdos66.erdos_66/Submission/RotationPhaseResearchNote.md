# Possible next direction: short-orbit carry averaging

This is an unproved research proposal, not a Lean result or a solution of
Spec.lean. Existing phase results use outer repetition or full residue
cycles; the following more refined idea has not been developed here.

Use row phases b*k mod p, retaining phase zero on the old first row.
For a fixed sum of row indices q, the sum of the phases is b*q, independent
of the individual row. For two constant row templates A,B, this lets one
first fix an old pair at low target t-b*q, then count how often its first
coordinate plus b*k lies in a carry interval as k varies.

A rotation with short-orbit interval discrepancy D(q)=O(log q) would make
the carry error at most D(q) times the old complete mixed count, with no
union bound over all p low targets. For varying monotone row levels, pairs
of levels occur on intervals of k; a finite partition could retain this
advantage, with explicit level-dependent errors. A rational approximant to
a badly approximable irrational could support useful ranges q much smaller
than p. These statements need proofs, including endpoints and both carries.

Potential benefit: one may average carries at q growing slowly, rather than
requiring q comparable to p or using a target-by-target probabilistic union
bound. This does not yet solve the density or changing-modulus problem.
In particular complete/empty row copying is already excluded; row levels
must taper. A fixed palette has a sparse minimum, and a new argument is
still needed to reset or transfer that minimum while preserving the old
natural prefix. Do not infer an infinite witness from this proposal.

## Subsequent formalization

The proposed short-orbit estimate and both ordinary carry transfers are
now proved, including antitone activity intervals and an explicit phase
floor(M sqrt(2)) mod M. See ShortOrbitCarryProgress.md and its saved
51-declaration axiom audit. The changing-modulus and sparse-minimum
compatibility issues described above remain unresolved.
