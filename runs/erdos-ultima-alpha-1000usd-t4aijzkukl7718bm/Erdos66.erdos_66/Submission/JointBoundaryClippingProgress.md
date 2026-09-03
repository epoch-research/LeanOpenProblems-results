# Joint boundary/triple control and unconditional one-target clipping

## Original conjecture status

The original existential conjecture is still unresolved. Spec.lean is
unchanged, with its original sorry and SHA256

    32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0

No proof/disproof has been submitted. The results below remove the endpoint
eligibility hypothesis from the previous ONE-TARGET downward correction.
They do NOT control cumulative loss or prove an all-target lower asymptotic.

## Main checked result

`Erdos66JointLogarithmicClipping.exists_uniform_central_log_clipping`:
there is ONE set A with every harmonic-profile prefix error at most one
and all reciprocal-integer two-sided power potentials summable, such that:

For every real c>0 and natural g, there are d>=2 and a threshold N0 so that,
for every n>=N0 and EVERY subset B of A, a finite D can be chosen with

* D consists of upper-half endpoints of B-pairs at n;
* both endpoints of each such pair are at least n/d^2;
* r_(B\D)(n) <= floor(c log n);
* r_(B\D)(n) >= min(r_B(n), floor(c log n)-1);
* for every z<=n^g with z!=n,

      r_B(z)-r_(B\D)(z) <= 2*tripleCap(g+1),

  where tripleCap(h)=144*(32*(h+2)+1)+2.

The collateral constant is deliberately loose. It is independent of c,
n, the current subset B, and the number of deleted endpoints. The threshold
and the relative central-window parameter d may depend on c and g.

This is a finite local correction theorem, not a convergent repair scheme.
It only decreases counts, and later deletions may spoil earlier lower
bounds. No summation of the constant collateral over all corrections has
been shown to be o(log n).

## Boundary mass and selection

`BoundaryPairMeanExplore.lean` proves for d>=2 and n>=d^2:

    sum_{a<n/d^2} profile(a)*profile(n-a)
       <= (4/d)*(1+log(n+1)).

It uses the existing profile-square and prefix-square bounds. No uniform
pointwise claim is inferred from prefix discrepancy alone.

`BoundaryPairCountsExplore.lean` defines the actual boundary finset and
its continuous Boolean encoding, and identifies it with the finite
realized disjoint-pair family. `DisjointMatchingPolynomialExplore.lean`
proves that a matching polynomial on disjoint supports equals the
exponential of the realized-support count.

`BoundaryPairPotentialExplore.lean` sets

    cutoff(j)=max(2,ceil(4 exp(j+1))).

The independent raw boundary exponential mean, for n>=cutoff(j)^2, is at
most exp(1)*(n+1). A direct summable-penalty construction was first completed
in FiniteBoundarySelectionExplore, BoundaryCompactnessExplore,
BoundarySparseCostsExplore, and BoundarySparsePowerProfileExplore. These
construct a boundary-controlled set with the power costs, but by themselves
do NOT retain the previous triple bounds.

`BoundaryCorrectionEligibilityExplore.lean` proves

    r_B(n) <= 2*|upperCentralEndpoints(B,n/d^2,n)|
                +2*|boundary(B,d,n)|+1.

Thus if the desired cap q is at least 2*|boundary|+2, enough central
upper-half endpoints exist to clip to q with at most one unit of overshoot
below q. BoundaryLogarithmicClippingExplore obtains this eligibility
eventually for any positive logarithmic cap, uniformly over subsets.

## General positive-pattern interface

The following new infrastructure avoids applying separate selectors and
mistakenly claiming their properties hold for one common set:

* NaturalPositivePatternExplore: Pattern is a finite positive multilinear
  polynomial in natural-number coordinates. Arbitrary finite families lift
  to the ordered compensated rounding interface; all support cutoffs are
  accounted for explicitly.
* PositivePatternCompactnessExplore: prefix discrepancies, finite pattern
  budgets, and summable representation costs pass jointly to one set.
* PatternSparseCostsExplore and PatternSparsePowerProfileExplore: the
  existing two-sided cost/power interfaces work with any pattern family
  whose finite independent-mean sums are at most 1/4.
* MatchingNaturalPatternExplore: matching polynomials are such patterns;
  zero patterns and positive scaling are included.
* PolynomialPatternBudgetExplore: if pattern m has independent mean at
  most 3(m+2), there are A and M with all the same prefix/power properties
  and Boolean pattern value at most (m+M+2)^4 for every m. The normalization
  uses a shifted summable cubic tail, not a geometric weight.

The polynomial index budget matters: geometric index weights would give
bounds much too weak to recover constant triple counts.

## Joint boundary and arbitrary-comparability triple construction

GeneralCentralTripleMeanExplore extends n<=4N to n<=C*N, for every fixed C:

    tripleMean <= (2C+2)*(1+log(N+1))^2/sqrt(N+1).

With tilt=log(N+1)/4, the tilted mean tends to zero; the raw matching
polynomial mean is eventually at most exp(1), uniformly in the coordinate
cutoff and in the third target z.

JointBoundaryTriplePatternsExplore encodes both test families using Nat.pair:

    boundaryCode(j,n) = pair(0,pair(j,n));
    tripleCode(C,h,N,n,z)
       = pair(1,pair(C,pair(h,pair(N,pair(n,z))))).

Inactive tests are the zero pattern. Boundary tests are active once
n>=cutoff(j)^2; triple tests once N is above the C-dependent mean threshold
and n<=C*N. Every test mean is at most 3(index+2), so the universal
polynomial budget imposes both families on ONE A.

RarePatternCodeGrowthExplore checks that, eventually in the scale:

    boundaryCode+M+2 <= (n+1)^5;
    tripleCode+M+2 <= (N+1)^(32(h+2)+1)

when C,h,M<=N, n<=C*N, and z<=N^h.

NaturalPatternRestrictionExplore transfers all finite coordinate tests to
actual set counts. JointBoundaryTripleCountsExplore then constructs ONE A,
with the same prefix and power-cost properties, satisfying:

* for every j, eventually

      (j+1)*|boundary(A,cutoff(j),n)| <= 20 log(n+1);

* for every C,h, eventually in N, uniformly when n<=C*N, z<=N^h, n!=z,

      |centralTripleFiber(A,N,n,z)| <= tripleCap(h).

These bounds are inherited by all subsets of A. This is genuinely joint,
not an intersection of independently selected witnesses.

For clipping at a target n, use scale N=n/d^2 and C=2d^2. Eventually n<=C*N.
For a requested horizon z<=n^g, eventually C^g<=N, hence n^g<=N^(g+1).
The joint triple bound therefore controls the off-target deletion loss.

## Audits and remaining gap

All production files named here compile and have built oleans.
BoundarySparseAudit.lean and JointClippingAudit.lean audit the principal
results using only propext, Classical.choice, Quot.sound.

The main unresolved issue has not changed: a one-target correction with
constant collateral does not provide a uniform o(log n) bound on the
accumulation of corrections at many centers. The weak power-saving
exception estimates can still permit too many centers. Downward clipping
also cannot fill deficits. None of these local correction theorems is a
proof or a disproof of the original existential conjecture.
