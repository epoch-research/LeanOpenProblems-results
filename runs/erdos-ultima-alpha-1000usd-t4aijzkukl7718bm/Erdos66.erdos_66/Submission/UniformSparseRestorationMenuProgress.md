# Uniform sparse restoration menu

The original conjecture is unresolved. Submission/Spec.lean is unchanged
and retains its original sorry. No auxiliary statement below settles it.

## Verified result

SparseRankTransversalExplore.lean exposes a single replacement set F for
a negligible prescribed deletion set D in an exact-bracket host A. Its
rank assignment bijects F with a tail of D; F is disjoint from A, replacement
locations and deleted locations are within a factor of two, and the full
insertion increment into A is o(log n).

UniformSparseRestorationMenuExplore.lean selects this same F before every
tolerance and every subsequent subset E of D. For every epsilon>0, once E
is supported sufficiently far out, the rank-selected subfamily of F restores
all exact prefix brackets and has insertion increment, measured FROM A\E,
between zero and epsilon*log(n+2) at EVERY target. Its increment/log(n) also
tends to zero. The cutoff depends on epsilon, not on the later subset E.

This follows from monotonicity of insertion increments and the location
bound: remote selected replacements cannot affect small targets, while the
full F increment controls every large target. No summation of packet error
budgets is used.

## Audit

UniformSparseRestorationMenuAudit.lean audits all seven theorem/lemma
declarations in these two files. Its saved log reports only propext,
Classical.choice, and Quot.sound.

## Remaining gap and continuation review

This theorem assumes a negligible master deletion set. Neither such a set
clipping all upper exceptions nor a simultaneous upward repair of all lower
exceptions has been constructed. The comparison is with the deleted core,
not the original host, and cannot be used to ignore deletion losses.

The existing rank-extension and first-window optimization diagnostics do
not establish convergence or impossibility. Their finite numerical outputs
are not Lean certificates of an asymptotic assertion.

The subsequent review of slowly varying periodic constructions did not
close the mixed-period transition gap. The finite cyclic theorem permits
any divergent sublinear mean, but supplies independent finite templates,
not compatible integer prefixes. Complete-product-period averaging and
same-prime thickness compatibility do not give the missing short-interval
mixed estimate for changing fields.

No valid replacement for the original sorry has been obtained.
