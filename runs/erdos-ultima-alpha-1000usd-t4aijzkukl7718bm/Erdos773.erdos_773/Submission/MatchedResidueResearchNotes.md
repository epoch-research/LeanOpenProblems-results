# Matched-residue lifting and full-fiber bounds

This continuation does NOT settle Erdős 773. Spec.lean is unchanged, and the
same admission remains for 0 < epsilon <= 1/3. No proof has been submitted.

## Verified sufficient criterion

`MatchedResidueLifting.lean`, namespace `Erdos773.MatchedResidueLifting`, defines

    roots q H R = {q*k+r : r in R, 0 <= k <= H}.

`PairMatching q R` says square-sum congruences modulo q identify the unordered
pair of root residues (including repeated summands). `ShortProducts q H R`
says `(r,k) -> 2*r*k mod q` is injective on `R x [1,H]`. The factor two is
explicit; cancellation by two is not silently assumed.

`squares_sidon`: if q>0, H<=q, gcd(q,2r)=1 for every r in R, and both criteria
hold, the union of ALL these fibers has Sidon squares. This is a sufficient
union criterion, unlike the old per-fiber criterion, which was false.

Proof: modular matching first aligns the residues. Within a repeated residue,
use the verified unit-progression theorem. Across distinct residues, a
nontrivial equality forces opposite index differences. Reducing the normalized
square identity modulo q produces equal short products, a contradiction.

Other public results:
- `roots_card`: cardinality |R|*(H+1), for canonical residues 0<=r<q.
- `roots_subset`: positive canonical residues give roots in [1,q*(H+1)].
- `finite_lower`: the actual Sidon maximum at that root height is at least
  |R|*(H+1), subject to ALL of the sufficient hypotheses.
- `three_fiber_example`: q=101, H=3, R={1,4,13} meets the criterion; its 12
  roots have Sidon squares. Finite checks use trusted `decide +kernel`.

## Two-thirds ceiling for the sufficient criterion

- `pairMatching_card`: |R|^2 <= 2q.
- `shortProducts_card`: |R|*H <= q.
- `criterion_card_ceiling`: for H>=1 and canonical residues, writing
  m=|roots q H R| and N=q*(H+1),

    m^3 <= 4*N^2.

The first bound injects ordered residue pairs into (square-sum residue,
order bit). The second simply counts distinct short products. Neither bound
uses a Sidon assumption for arbitrary integer root sets. This ceiling applies
ONLY to this sufficient full-fiber construction.

## Relaxing short-product injectivity still leaves a full-fiber ceiling

`FullResidueFiberBound.lean`, namespace `Erdos773.FullResidueFiberBound`, uses
the four indices

    a=2r+3q+2, b=2r+7q+3, c=4r+9q+2, d=4r+11q+3.

`fiber_identity` is the exact polynomial identity

    (q*a+r)^2 + (q*d+r)^2 = (q*b+r)^2 + (q*c+r)^2.

`indices_order` proves a<b<c<d for q>0. Thus `long_fiber_not_sidon` shows any
union containing that full fiber through index d is not Sidon after squaring.

For canonical r<q, d<15q. Consequently:
- `full_fiber_length_bound`: a nonempty full-fiber union with Sidon squares
  has H<15q. No PairMatching or ShortProducts hypothesis is needed here.
- `full_fiber_card_bound`: if it additionally has PairMatching (but NOT
  necessarily ShortProducts), then

    m^4 <= 60*N^3,  N=q*(H+1).

This is a three-quarters ceiling for this weaker full-fiber construction,
NOT an upper bound for the original square-Sidon maximum. It says nothing
comparable about arbitrary partial fibers, which need not contain the four
explicit indices, or about constructions without modular pair matching.

## Audits and main status

Both new modules compile without admissions. All thirteen printed axiom
audits contain only propext, Classical.choice, and Quot.sound. Logs:

    /tmp/matched-residue-final.log
    /tmp/full-fiber-final.log

No actual main-gap lower bound was improved; no fixed-power upper bound for
the original maximum was obtained. Nothing from these modules was consolidated
into Spec.lean.

## Pending digit-statistic distinction

The older inversion-count-14 base-eight counterexample in CurrentGapNotes.md
rules out exact inversion count alone, but does not have common end digits.
The newer full-alphabet fixed-end counterexample rules out inversion parity
(all four inversion counts are odd). The fixed-end PLUS exact inversion-count
variant has neither a proved sufficient theorem nor a counterexample here.
Finite screens at bases eight and nine did not establish a general result.
No new digit-statistic theorem was formalized in this continuation.
