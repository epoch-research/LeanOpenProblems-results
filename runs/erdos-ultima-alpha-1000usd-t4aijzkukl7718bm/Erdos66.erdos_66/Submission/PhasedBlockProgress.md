# Arbitrary block phases and occurrence-ranked phase balancing

## Conjecture status

The original conjecture remains unresolved. Spec.lean is unchanged.
No proof or disproof has been submitted.

## Verified results

`PhasedBlockOperatorExplore.lean` extends the fixed disjoint cyclic-palette
natural-number operator to arbitrary phases s(n) in ZMod M, one phase for
each coarse block. The phase translates the union of active palette colors
before the existing outer repetition by K. Its exact membership is

    a in A iff some i has floor(a/(MK)) in B_i and
      reduceDigit(a)-s(floor(a/(MK))) in P_i.

The old uniform representation bound remains unchanged:

    |r_A(n MK+digit(t,r))
       - mu [r F(n)+(K-r)F(n-1)]|
       <= mu (K eta+1+eta) [F(n)+F(n-1)].

Here F is the self-convolution of the integer active-color count. The fine
palette is selected before all coarse inputs, all phase sequences, all K,
and all targets. Coarse prefix agreement together with phase agreement
preserves the corresponding natural prefix exactly. Both carry terms are
retained; no product-group identification is used.

`OccurrencePhaseBalanceExplore.lean` constructs a deterministic phase
schedule for any sequence f of types from a finite alphabet alpha and any
fixed template C_t in ZMod M. At the j-th occurrence of type t, use phase
j modulo M. For every N and residue z:

    |sum_(k<N) 1_{z in phase(k)+C_(f(k))}
       - (1/M) sum_(k<N) |C_(f(k))|| <= |alpha| M.

The phase depends on the number of occurrences of the CURRENT TYPE, not
on k modulo a fixed period. Every full cycle of M occurrences covers each
residue |C_t| times. The occurrence-sum identity and incomplete-cycle error
are checked explicitly. `PhasedResidueCountingExplore.lean` then checks the actual natural count
identities for a general block set of modulus M:

    count(A,NM) = sum_(k<N) |C_k|,
    count(A intersect residue z,NM) = sum_(k<N) 1_{z in C_k}.

For occurrence-phased templates this gives the same discrepancy bound at
block boundaries. At EVERY natural cutoff X it gives the fixed bound
(|alpha|+2)M, including the partial last block. If the resulting set is
infinite, its ordinary residue fractions therefore tend to 1/M. This is
proved without assuming any representation-count asymptotic. These natural
count statements use the direct modulus-M phased block set; the arbitrary-K
representation operator is separately checked above.

All three production files compile with current oleans. PhasedBlockAudit.lean
checks thirteen main declarations, using only the permitted axioms.

## Scope

A fixed PALETTE need not force a fixed residue support if arbitrary block
phases are permitted. The earlier fixed-support obstruction applies to the
unshifted operator, not automatically to this phased extension. This is
not a new witness: the scalar input profile F is still unconstructed, and
the fixed eta and carry errors have not been made to vanish in one output.
There is also no changing-modulus compatibility theorem here. Balancing
single-residue counts does not establish pointwise representation accuracy.
