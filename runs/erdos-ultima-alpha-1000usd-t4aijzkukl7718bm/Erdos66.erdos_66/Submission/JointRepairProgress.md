# Joint finite and infinite repairs

`Spec.lean` is still unchanged and unresolved. These are auxiliary results;
no proof or disproof of the original existential statement has been submitted.

## Main checked result

`Erdos66JointInfiniteRepair.prescribed_spikes`, in
`JointInfiniteRepairExplore.lean`, constructs an infinite superset B of A
with a prescribed even representation-increment profile and o(log z)
collateral. All ten new pipeline files compile and have built oleans.
`JointInfiniteRepairAxiomCheck.lean` reports only propext, Classical.choice,
and Quot.sound.

Here is the precise mathematical setup. Write ell(z)=log(z+2), and assume

    r_A(z) <= K + C*ell(z),   K,C >= 0.

There is one independent coordinate for each natural i. It supplies a pair

    x_i = a_i + omega_i,
    n_i - x_i,

where omega_i ranges over {0,...,q_i-1}, q_i>0, and every choice satisfies
0<=x_i<=n_i. Centers n_i may repeat. Let

    V = K/log(2) + 2*C,
    D = 2*sqrt(2*V).

Assume one finite Q bounds all prefix sums

    sum_(i<L) 1/sqrt(q_i) <= Q,

and every prefix has total cost at most 1/2:

    sum_(i<L) 4*(i+1)^2/q_i
      + sum_(i<L) 16*(i+1)^4/q_i
      + sum_(i<L) D*sqrt(ell(n_i))/sqrt(q_i) <= 1/2.

Finally assume that, for every z, the number of occurrences of z among the
first L centers stabilizes to a prescribed natural m(z).

Then there exists B containing A such that, at every z,

    r_B(z) >= r_A(z) + 2*m(z),

and, for every epsilon>0, eventually

    r_B(z) <= r_A(z) + 2*m(z) + epsilon*ell(z).

Thus the total collateral is o(log z), not a sum of independent worst-case
per-packet bounds. No restriction on the target z to a finite cutoff remains
in the conclusion.

## Pipeline

1. `HeterogeneousSelectionExplore.lean` (about 170 lines)
   Finite independent choice spaces may have different cardinalities.
   For S_i in coordinate i, define

       hitMass(S) = sum_i |S_i|/q_i.

   The hit MGF is bounded by exp(exp(t)*hitMass(S)). One-fiber bad events
   cost the reciprocal of the particular coordinate used to avoid them.
   The selection theorem permits separate masses, thresholds, and tilts
   for every test.

2. `MultiPacketExplore.lean` (about 190 lines)
   Labels (i,false),(i,true) denote x_i,n_i-x_i. A designated pair uses
   both labels of the same coordinate. For a collision between two
   disjoint non-designated pairs, EVERY coordinate that occurs has a
   nonzero coefficient. Hence the largest-scale coordinate can pay for
   the collision event.

   If points are distinct and all such collisions are avoided, then

       2*#{i:n_i=z} <= r_F(z) <= 2*#{i:n_i=z}+2.

   The upper error is TWO for the entire combined family, not six times
   the number of packets.

3. `MultiPacketSelectionExplore.lean` (about 150 lines)
   Combines heterogeneous MGF selection with point-collision and
   non-designated-pair collision avoidance. A caller selects the paying
   coordinate in each event.

4. `JointFiniteRepairExplore.lean` (about 105 lines)
   Converts the selected labels to a finite repair F disjoint from an old
   finite integer set. Mixed counts are bounded by twice the joint hit
   count. The total increment at z lies between the designated contribution
   and that contribution plus 4*R(z)+2.

5. `PacketCollisionCostExplore.lean` (about 120 lines)
   For coordinates indexed by Fin L, pay using the maximum index occurring
   in each event. Weighted collision costs are bounded by

       sum_i 4*(i+1)^2/q_i
       sum_i 16*(i+1)^4/q_i.

   These coarse bounds are uniform in the prefix length L.

6. `JointRepairPotentialExplore.lean` (about 90 lines)
   If the joint hit mass is at most B*sqrt(ell(z)), use tilt 4/epsilon and
   threshold epsilon*ell(z). Its exponential potential is bounded by

       exp(exp(4/epsilon)*B*sqrt(ell(z)) - 4*ell(z)).

   This is eventually bounded by 1/(z+2)^2 and is summable. For each
   accuracy level, one tail threshold makes the sum over ANY finite set
   of later targets arbitrarily small. These thresholds are chosen before
   the finite coordinate prefix or finite test set.

7. `JointWindowExplore.lean` (about 130 lines)
   The old set in a mixed-hit test at z can be truncated at z, even when
   some repair centers are much farther away. Its local representation
   bound is V*ell(z), yielding

       hitMass(S_z) <= D*sqrt(ell(z))*sum_i 1/sqrt(q_i).

   Forbidden-choice masses use the individual center cutoff n_i rather
   than the largest center in the entire family.

8. `FiniteChoiceCompactnessExplore.lean` (about 65 lines)
   Compactness of a product of finite choice spaces turns compatible
   finite-prefix feasibility into one global choice. It also proves that
   discarding coordinates can only decrease hit counts.

9. `InfinitePacketSelectionExplore.lean` (about 180 lines)
   Allocates a geometric potential budget among accuracy levels
   epsilon_k=1/(k+1). Uniform finite prefix costs <=1/2 and uniform masses
   <=B*sqrt(ell(z)) give a single infinite choice with distinct points,
   unique non-designated unordered sums, avoidance of the old set, and
   uniformly o(log z) mixed hits for EVERY finite coordinate prefix.

10. `JointInfiniteRepairExplore.lean` (about 175 lines)
    Transfers the global selection to natural sets. The increasing union
    of finite packets has each fixed representation count attained at a
    finite stage. Stabilized center multiplicities then give the stated
    prescribed-spike theorem.

Audits: `JointRepairAxiomCheck.lean`, `InfinitePacketAxiomCheck.lean`, and
`JointInfiniteRepairAxiomCheck.lean` all pass.

## Completed applications / remaining gap

The application pipeline is now checked in four further files:

1. `SummableSpikesExplore.lean` uses the full candidate interval [0,n_i],
   discards finitely many coordinates, and derives asymptotically prescribed
   spikes from three summable coordinate-cost series.
2. `RepeatedCentersExplore.lean` enumerates positive finite target
   multiplicities and transfers block-level summability to coordinate costs.
3. `SparseGrowthCostsExplore.lean` proves the required series summable for
   O(log n_k) multiplicities when n_k is monotone and eventually at least
   (k+1)^12.
4. `PolynomialSparseCompletionExplore.lean` clips the deficits of a base
   profile and completes it, assuming a sharp upper coefficient and a sharp
   lower coefficient away from the exceptional targets. It includes the
   powers-of-two specialization.

All four compile and have built oleans; the main theorems pass the permitted
axiom audit in `PolynomialSparseCompletionAxiomCheck.lean`. See
`PolynomialSparseCompletionProgress.md` for details.

No appropriate base has been constructed. Existing power annuli leave dense
intervals uncontrolled, and there is still no valid mixed-period gluing
argument. The original conjecture has not been settled.


## Subsequent matching-based engine

The Sidon uniqueness requirement has now been relaxed. The new engine bounds
unintended self counts by a matching partition function, giving o(log z)
collateral from reciprocal-square-root masses rather than index-four costs.
This yields superquadratic (any p>2) sparse completion. See
`MatchingRepairProgress.md`. No appropriate base set has been constructed.
