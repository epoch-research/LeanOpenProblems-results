# Coordinated sub-square-root exact-bracket repairs

## Original conjecture status

Erdos66.erdos_66 remains neither proved nor disproved. Submission/Spec.lean
is unchanged and retains its original sorry. No valid proof submission is
available. The new results concern positive increments on a controlled
number of prescribed targets, not arbitrary exceptional sets.

## Verified production files

* AdaptiveHitSelectionExplore.lean
* AdaptivePacketAlgebraExplore.lean
* AdaptivePacketChoiceExplore.lean
* AdaptiveAssignedRepairExplore.lean
* AdaptiveRepairBudgetExplore.lean
* ShortSupportSwapTailExplore.lean
* GlobalAdaptiveRankRepairExplore.lean

All seven compile without warnings and have current oleans.
AdaptiveRankRepairAudit.lean checks all 49 lemma/theorem declarations.
The saved audit log lists only propext, Classical.choice, and Quot.sound.
No production source introduces a placeholder or a new axiom.

## 1. History-dependent selection

exists_adaptive_small_hits permits the available candidate set to depend
on the entire current state. Its invariant, availability, hit-degree, and
load-increment assumptions are explicit.

If every available set has cardinality at least q>0, each target's hit set
has size at most K(z), and one selected hit increases its load by at most
one, then a prepaid potential

    sum_z exp(t load_k(z) + (m-k)b(z) - tR(z))

has a nonincreasing conditional mean whenever

    exp(t) K(z)/q <= b(z).

An initial potential below one yields a final state with every tested load
below R(z). This is a deterministic finite averaging argument; no false
independence assertion is made about history-dependent choices.

## 2. One joint packet load

At step k insert the symmetric pair {x,n_k-x}, assigning each point to its
old deletion point. The current load includes

    2 r_(F,A)(z) + 2 r_(assign(F),A)(z) + r_F(z)
      - 2 occurrences(n_0,...,n_(k-1);z).

After division by 14, this load increases by at most one whenever either
an old mixed hit or an undesignated new/new hit occurs, and by at most zero
otherwise. Both diagonal new/new pairs are included. The proof uses exact
finite union identities, not Sidon uniqueness or a sum of per-repair errors.

All old mixed hits and undesignated new/new hits are excluded at every
prescribed center. Consequently the central increments are EXACT, including
when the center list repeats.

## 3. Availability charged per step

Candidates are excluded if an endpoint is old, an assigned deletion point
was already used, or a protected center receives an unintended hit.
For current F, assignment fibers at most H, and center set C, the blocked
candidate count is bounded by

    B + 2H |assign(F)| + |C| (Kc + 2|F| + 2).

Thus for m total packets, availability at least q follows from

    q+B+4Hm+|C|(Kc+4m+2) <= |alphabet|.

This is a per-step bound. There is no quadratic union bound over all
assignment collisions, and no fourth-power Sidon-collision term.

The finite theorem exists_adaptive_assigned_repair returns D,F with

* D subset A, F disjoint from A;
* |D|=|F|=2m, D=assign(F), assign injective on F;
* prescribed exact central increments 2 occurrences(z);
* at every tested noncentral z, absolute signed collateral <14R(z).

It retains the selected endpoint shape needed for localization and brackets.

## 4. Demand-scale calculation

If S(N)>=0 eventually and

    S(N) log N / sqrt N -> 0,

then both the normalized availability cost and common-potential mean cost
vanish when m<=S(N), H<=G sqrt N, |C|<=m, and the old candidate degrees are
at most B sqrt N log N.

The tilt is fixed after the requested epsilon and polynomial horizon are
fixed. Every fixed power S(N)=N^a with a<1/2 satisfies the condition.
No assertion is made that the actual exceptional sets have such demand.

## 5. Short support, rather than edit count, controls the far tail

If all deleted and inserted points are below U, and z>=2U, then

    |r_new(z)-r_A(z)| <= 2 count(A intersect [z+1-U,z+1)).

The estimate is independent of the number of edits. New/new pairs vanish
at this target, and a fixed old partner determines at most one modified
point in each signed direction.

For antitone p and prefix discrepancy at most delta, this is bounded by

    2 [U p(z+1-U) + 2 delta].

For the exact harmonic brackets, eventually in N, all edits supported at
most 15N have error at most SIX at every z>=N^33+1. The horizon exponent is
not optimized. The existing polynomial profile bounds prove this uniformly
in the host and in the edited cardinalities.

This avoids the old generic bound 4m, which would not suffice for polynomial
packet demand at a fixed polynomial far-target horizon.

## 6. Global coordinated exact-bracket theorem

uniformly_eventually_global_adaptive_rank_repair chooses its large-N
threshold BEFORE the host A and BEFORE the entire center list. For fixed
K,C>=0, epsilon>0, and S as above, eventually N has the following property.

For EVERY A satisfying

    floor(P(L)) <= count(A,L) <= ceil(P(L)) for every L,
    r_A(z) <= K+C log(z+2) for every z,

and EVERY list n_0,...,n_(m-1) with

    m<=S(N),  16N<=n_k<=17N,

there are equal-size finite deletions and insertions D,F such that

* |D|=|F|=2m;
* all modifications lie in [2N,15N];
* ALL original floor/ceiling brackets survive exactly;
* at each listed center z,

      r_new(z)=r_A(z)+2 occurrences(z);

* at EVERY other natural target z,

      |r_new(z)-r_A(z)| <= epsilon log(z+2).

The finite test set is [0,N^33+1). Below 2N nothing changes. The remaining
finite targets use the common potential. Beyond the test set the separate
short-support theorem applies. The infinite tail is therefore checked.

The rank map is fixed from the original host throughout the entire batch.
Its injectivity on the inserted set gives distinct cumulative-rank cells,
so the previously proved rank-family exchange theorem supplies exact
bracket preservation. This is no longer merely a one-target result.

The fixed-host and fixed-power versions are also exposed as

    eventually_global_adaptive_rank_repair
    eventually_global_adaptive_rank_power.

## What remains missing

The existing probabilistic host gives, for each fixed tolerance, a power
saving whose exponent tends to zero with the tolerance. That estimate
still permits many more than square-root-order exceptional targets. If each
deficit costs order log N packets, the displayed repair needs substantially
less than sqrt(N)/log(N)^2 such targets per comparable-scale batch.

These are limitations of available UPPER estimates, not a proof that every
host has too many exceptional targets. No universal impossibility is claimed.

The new theorem only makes positive central increments. It does not provide
a sharp all-target asymptotic upper coefficient, general downward tuning,
or an infinite repair of arbitrary dense exceptions. Uniformity over hosts
and finite center lists is not itself an infinite shrinking-tolerance chain.

Thus a coordinated repair tool has been established below the square-root
capacity range, but the original existential conjecture is still unresolved.
