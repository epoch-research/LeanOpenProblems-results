# Further compatibility review

This is mathematical review, not a new formal theorem or a solution.
Spec.lean is unchanged and the conjecture remains unresolved.

## Existing extension theorems do not compose as needed

PalettePrefixExtensionExplore fixes its palette before the admissible old
pieces. Its exact preservation is genuine, but applies within that one
system. An old prefix constructed using a different palette is not thereby
an admissible old piece in the next system.

LinearPrefixExtensionExplore fixes the old prefix first, but requires a
predictive-mean estimate for the new window and an explicit summed tail
budget. The logarithmic specialization requires epsilon^2*b>=16. No
invariant supplying predictive means with shrinking errors at fixed c has
been found. Neither global upper control nor past accuracy is a substitute
for that invariant.

The power annuli, same-source clipping, and whole-coarse-block repair remain
finite results. Their accuracy thresholds do not furnish the simultaneous,
cutoff-independent thresholds in conjecture_iff_finite_prefixes.

## Fixed digit padding is not a coefficient-reduction step

Consider the already formalized binaryBlocks(M,B,D) construction. Its exact
formula at qM+t, q>0, is

    r_new(qM+t) = lower_B(t) r_D(q) + upper_B(t) r_D(q-1).

If r_D(q)/log q tends to c, the residue-t subsequence therefore has leading
coefficient c times the cyclic self-representation count of B at t. This
limit observation was reviewed here, not added as a new Lean declaration.

A proper fixed B is already excluded as a permanent support of a witness
by the verified residue-support theorem, independently of this calculation.
For B equal to the full residue set, lower_B(t)+upper_B(t)=M, so padding
increases the coefficient by M rather than reducing it. Thus this operation
cannot convert the existing fixed-relative-accuracy constructions, whose
coefficients grow as accuracy improves, into one fixed-c witness.

No assertion about arbitrary colored or nonstationary digit assignments
follows. Those still need their own mixed-count and compatibility proofs.

## Other reviewed possibilities

Exact unit-mean mixed digit families face the already verified
ComplementaryFamilyBarrier tradeoff: small self caps cannot remain bounded
as the number of exactly complementary colors grows. Replacing lines by
small perturbations does not by itself remove this tradeoff.

Nested-field curves still lack the required intermediate prefix mass and
restricted mixed counts; shared parameters do not resolve this. These
observations repeat the scope of the existing verified results, rather than
supply a new universal impossibility theorem.

No new production theorem was obtained in this review. There is still no
complete proof or exact-negation theorem for Erdos66.erdos_66.

## Subsequent capped-history obstruction

CappedHistoryLookaheadExplore.lean now proves that even a strict global
upper cap plus arbitrarily long accurate history is insufficient for a
universal exact-prefix next-window extension. The old prefix is fixed
first; all later sets preserving every old bit fail at a prescribed
lookahead distance H beyond its cutoff. This uses the first lower-bound
failure of a finite annulus and an initial gap. It is not an obstruction
to a specially selected compatible chain. See CappedHistoryLookaheadProgress.md
for the statement, proof, verification, and quantifier distinctions.
The main conjecture in Spec.lean remains unresolved and unchanged.
