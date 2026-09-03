# Explicit short-orbit carry averaging

## Original task status

Erdos66.erdos_66 remains unproved and undisproved. Spec.lean is unchanged
with its original import, statement, and sorry. No solution is claimed.

## Checked pipeline

Ten production files compile, with current oleans and no warnings:

* AntitonePairIntervalsExplore.lean
* ShortOrbitCarryExplore.lean
* ShortOrbitNaturalExplore.lean
* QuadraticRotationApproxExplore.lean
* HermiteFloorExplore.lean
* RationalRotationGridExplore.lean
* RotationFloorPerturbationExplore.lean
* ShortRotationLogBoundExplore.lean
* DiscreteRotationBridgeExplore.lean
* ExplicitPhaseCarryExplore.lean

ShortOrbitCarryAudit.lean checks 51 declarations. The saved audit log
reports only propext, Classical.choice, and Quot.sound. The production
files have no sorries or new axioms.

## Antitone activity intervals

For antitone finite row families C,D and a fixed old pair (a,z-a), its
active row indices k, satisfying a in C_k and z-a in D_(q-k), form an
integer interval inside [0,q]. Every active pair belongs to

    {a in C_0 : z-a in D_floor(q/2)}
      union {a in C_floor(q/2) : z-a in D_0}.

Thus the number of possibly nonempty activity intervals is bounded by
TWO half-row mixed counts, rather than by all pairs of the largest row.

## A single explicit phase

For EVERY positive integer M choose

    m=floor(M sqrt(2)),  b=m mod M.

For Q^2<=M, every a mod M, every t<M and 0<=l<=u<=Q,

    |sum_(l<=k<u) 1_[(b*k+a).val<=t] -(u-l)(t+1)/M|
      <=25 log(Q+1).

The phase depends only on M, before every target, interval, or horizon.
The floor bridge uses width (t+1)/M exactly; no endpoint is discarded.
The arbitrary interval is shifted to a new starting phase, so it has no
extra discrepancy factor of two.

The proof uses Dirichlet approximation of sqrt(2), with a reduced rational
r of denominator d satisfying 0<d<=N and N+1<=5d. The elementary lower
bound 1<=5d^2|sqrt(2)-r| supplies denominator comparability. Exact Hermite
floor sums give rational-block error at most one. Perturbing the slope
by d^2|alpha-r|<=2 gives block error at most five. Greedy blocks reduce
the remaining length plus one by at least a factor 4/5, producing the
uniform bound 25 log(N+1). Finally |m/M-sqrt(2)|<=1/M.

## Actual ordinary representations

Put C'_k=b*k+C_k. Then C'_0=C_0 exactly. For q>0, t<M and
(q+1)^2<=M, define

    phaseMass(q,t)=sum_(k<=q) r_(C_k,C_(q-k))(t-b*q),
    halfMass(q,t)=r_(C_0,C_floor(q/2))(t-b*q),
    rho=(t+1)/M.

The natural block set with rows C'_k satisfies

    |r(qM+t)-rho phaseMass(q,t)-(1-rho)phaseMass(q-1,t)|
      <=50 log(q+2)[halfMass(q,t)+halfMass(q-1,t)].

Both ordinary carries, their different row sums and low targets, and the
exact endpoint are retained. This is deterministic, not an average over
phases or a separate phase choice for each target.

## Scope and unresolved issue

If a tapered joint palette supplies halfMass=O(V/sqrt(q)), the displayed
carry error is O(V log(q)/sqrt(q)). This consequence still needs whatever
palette hypotheses yield the stated half-mass estimate; no such data
are created by the rotation lemma alone.

The old IntegerBlockExplore.block_brackets already handles unphased
antitone actual rows. The new result is for phased rows, which are not
antitone as spatial sets, while preserving row zero.

A fixed palette still has a sparse minimum. An actual constructed prefix
at the next, larger modulus is not automatically a member of a new flat
nested palette. The theorem does not reset that minimum or compare the
mixed counts of different moduli. It therefore supplies neither the
cutoff-independent finite feasibility nor the compatible infinite chain
required for Spec.lean, and it is not a disproof of arbitrary witnesses.
