# Complete finite palettes starting at an actual logarithmic sparse member

The original conjecture in Spec.lean remains unresolved and unchanged.

## Checked theorem

`Erdos66SparseStartCompletePalette.exists_sparse_start_complete_palette`
returns, for c,tau,eta,epsilon>0 with eta,epsilon<=1 and every lower bound
N0, an odd M>N0, a nonempty B0 subset ZMod M, and a finite nested palette P
such that:

* B0 belongs to P and is contained in every member;
* all mixed counts have relative error <=eta about |B||C|/M;
* the full group belongs to P and |P|<=M+1;
* |(|B0|^2/M)/log M-c|<tau;
* for every |B0|<=x<=M, some B in P satisfies x<=|B|<=(1+epsilon)x.

Coverage therefore begins at an ACTUAL logarithmic sparse member, not only
at the much larger algebraic level where dense completion is attached.

## Proof and files

`MinimumIndexedPaletteExplore.lean` exposes a prescribed lower bound on
that attachment index. `ActualCardinalityCoverageExplore.lean` derives
actual cardinality brackets from self-count bounds and proves adjacent
level coverage. `SparseStartCompletePaletteExplore.lean` combines them.

Choose I=ceil(4/epsilon)+1, tune the nominal base coefficient to c/I^2,
and make the nominal relative error sigma small compared with eta,
epsilon, and tau/(c+1). The actual mean at C_I is then close to c log M.
Above I, adjacent actual cardinalities have ratio at most 1+epsilon.
Attach dense completion above C_H, then keep only palette members
containing C_I. Nesting ensures the full coverage remains available.

All three files compile and have built oleans. SparseStartPaletteAudit.lean
checks the principal declarations; only propext, Classical.choice, and
Quot.sound occur.

## Scope

This removes the large-starting-index limitation from the older complete
palette statement. The earlier placement bound was genuine, but its
application to that large index is not a universal obstruction to a sparse
starting palette. Dense members still incur their genuine integer placement
costs. This theorem is within one finite modulus; it does not provide
compatible integer prefixes, changing-modulus estimates, or an infinite
witness for the conjecture.
