# Banded multi-curve origin repair

## Status

Erdős 66 remains unresolved. `Submission/Spec.lean` is unchanged and still
contains its original `sorry`. No proof submission has been made.

## Completed finite results

1. `PartitionCurveRepairExplore.lean`
   - A finite partition can be injected into nonzero points on distinct
     parabolas if every fiber has size smaller than the field.
   - For an injective point map f with no opposite image points, the mixed
     origin count of f(R) union -f(S) and f(R') union -f(S') is exactly
     |R intersect S'|+|S intersect R'|.
   - If repair pieces use m and n curves, their nonzero-target collateral
     cost against main parameter sets U,V is at most
         4|U|n + 4m|V| + 8mn.

2. `GridBandPartitionExplore.lean`
   - Partition the 2H by H grid by
         min(floor(row/(2g)), floor(column/g)).
   - Each band has at most 4gH cells.
   - The first 2i rows and the first i columns meet only the first i/g+1 bands.
   - Hence the whole grid embeds into nonzero points on H/g+1 curves if
     the field has more than 4gH elements.

3. `SeparatedParametersExplore.lean`
   - Select L injectively enumerated nonzero parameters, mutually nonopposite
     and disjoint from both signs of U, if 2(|U|+L)+1 is smaller than the field.

4. `BandedRepairFamilyExplore.lean`
   - For nested main parameter sets |U_i|=2i, produce nested B_i with
         r_{B_i,B_j}(0)=1+4ij.
   - At every nonzero target, the added count is nonnegative and at most
         8i(j/g+1)+8(i/g+1)j+8(i/g+1)(j/g+1).
   - This only needs p>4gH and p>2(2H+(H/g+1))+1, not p>2H^2.

5. `EveryPrimeBandedRelativeExplore.lean`
   - `every_prime_banded_relative_family`:
     For every eta>0 and maximum level H, choose positive D,g. Every prime
         p > max(8DH+3, 4gDH)
     admits nested B_i (with B_0 empty) such that every mixed sum count
     at levels i,j<=H differs from 4D^2ij by at most eta*4D^2ij.
   - The proof chooses T>max(1,1/eta), D=1024(H+1)T^2, and g=68T.
   - The repair-cost estimate for indices a,b>=g is at most
         (17/g)*4ab,
     including the linear correction between graph weights and sets.

All listed files compile. Principal declarations were axiom-audited in
`BandedRepairAxiomCheck.lean` and `BandedRelativeAxiomCheck.lean`; only
propext, Classical.choice, and Quot.sound occur.

## Scope and remaining obstruction

The new relative theorem controls mixed SUM counts only. Unlike the older
EveryPrimeRelativeFamily theorem, its statement does not yet include
nonzero mixed DIFFERENCE counts.

D still depends on the maximum level H through the simultaneous character
energy selection. The origin-repair threshold has genuinely improved, but
no claim of a level range linear in p at fixed precision has been proved.

More importantly, widening the density range does not by itself provide
uniform integer-prefix estimates. Existing carry averaging uses a period
which grows with the final scale. It still does not control a fixed initial
threshold as that cutoff tends to infinity, nor the mixed counts between
patterns based on different fields. No compactness argument yielding the
original conjecture follows from these finite improvements.
