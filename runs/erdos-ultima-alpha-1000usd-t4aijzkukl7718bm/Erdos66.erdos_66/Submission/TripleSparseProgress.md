# Prefix-balanced triple-sparse rounding and downward corrections

## Original task status

`Submission/Spec.lean` remains unchanged with its original `sorry`. The
existential conjecture is neither proved nor disproved; nothing has been
submitted. Its SHA256 remains

    32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0

## New infinite-set result

`Erdos66TripleSparsePowerProfile.exists_triple_sparse_power_potentials`
constructs ONE set A and a cutoff function N0 : Nat -> Nat such that:

* every prefix discrepancy from the exact harmonic profile is at most one;
* all reciprocal-integer two-sided power representation potentials are
  summable (the same powerCost family as before);
* for every h and every N >= N0(h), if n <= 4N, z <= N^h, and n != z,

      #{a : a <= n, N <= a, N <= n-a, a <= z,
             a in A, n-a in A, z-a in A} <= 36(h+4)+2.

The third point is NOT required to lie in the same dyadic window. The
horizon exponent h is arbitrary but fixed before its cutoff N0(h).

`exists_triple_sparse_power_exceptions` also states the previous weak
power-saving exception estimate for this SAME set. It does not claim
local-difference bounds: those were not included in this joint selector.

## Matching-polynomial mechanism

`BernoulliMatchingPolynomialExplore.lean` defines

    sum_{M matching} (exp(t)-1)^|M| product_{i in union supports M} p_i.

This is a positive multilinear polynomial and hence can be retained by
ordered compensated rounding alongside two-sided representation costs.
Its expectation is itself, and its value is at most

    exp((exp(t)-1) sum_e product_{i in support(e)} p_i).

With support-conflict degree D, a Boolean cost below exp(t(k+1)) bounds the
number of realized supports by D*k.

`MatchingPolynomialSelectionExplore.lean` proves the generic joint finite
selection theorem. Instance-sensitive matching finsets are identified by
extensionality rather than expensive definitional equality.

## Geometry and mean

`TripleIntersectionGeometryExplore.lean` uses triples (a,b,c) with

    a+b=n, a+c=z, a,b >= N,

and all three distinct. First and third coordinates are injective; each
coordinate lies in at most three triples; each triple conflicts with at
most nine others.

`TripleIntersectionMeanExplore.lean` proves, for n <= 4N, uniformly over
coordinate truncation L and over ALL z,

    tripleMean <= 10(1+log(N+1))^2/sqrt(N+1).

The third-coordinate mass is bounded by the initial profile prefix because
it is injective into an interval of length at most n+1 and the profile is
nonincreasing. No unjustified distant-window difference estimate is used.

With tilt = log(N+1)/4, exp(tilt)*tripleMean tends uniformly to zero.

`TripleIntersectionPotentialExplore.lean` chooses weight
(N+1)^(-h-4). The weighted mean is eventually at most
exp(1)/(N+1)^(h+4). Summing over n <= 4N and z <= N^h gives the summable
row bound

    rowTail(N) = 10 exp(1)/(N+1)^3.

A weighted Boolean cost below one bounds the nondegenerate count by
36(h+4).

## Joint selection and compactness

`FiniteTripleIntersectionSelectionExplore.lean` assigns horizon h the tail
budget (1/2)^h/8. The total triple budget is at most 1/4, leaving a
compensated representation budget of 1/2. Its coordinate cutoff L and test
horizon H are separate. It produces prefix brackets, total representation
cost at most one, and every triple bound for h,N <= H.

`CentralTripleCountsExplore.lean` identifies the actual regular natural
fiber with the realized finite triples. At distinct targets only a=n-a
and a=z-a are possible repeated-coordinate exceptions, adding at most two.
The full count has a continuous finite-coordinate Boolean encoding.

`TripleIntersectionCompactnessExplore.lean` passes these constraints and
countably many nonnegative continuous cost budgets to an infinite set.
`TripleSparseCostsExplore.lean` instantiates the two-sided exponential-cost
interface. `TripleSparsePowerProfileExplore.lean` supplies the power-cost
and power-exception corollaries.

## Exact downward corrections

`CentralTripleDeletionExplore.lean` proves for finite D subset A:

    r_A(z)+r_D(z) = r_{A\D}(z)+2*#{a in D : a<=z, z-a in A}.

If D consists of upper-half endpoints of central n-pairs, its self count
at n is zero and every point has a partner. Therefore

    r_A(n) = r_{A\D}(n)+2|D|.

Any requested cardinality k up to the number of eligible endpoints can be
selected. At every other target the loss is at most twice the central
triple count, independent of k.

`TripleSparseDownwardCorrectionExplore.lean` combines the infinite witness
with this result. The same conclusion holds for EVERY subset B of the
constructed A, since triple counts are monotone under taking subsets:

    loss at z <= 72(h+4)+4

for z <= N^h, n != z, N >= N0(h), n <= 4N. Eligibility must still be
checked in the CURRENT subset B. The theorem does not promise that any
particular prescribed decrement is eligible.

For multiple repaired centers T, the checked cumulative estimate is

    loss at z <= 2 sum_{n in T} centralTripleCount(A,N(n),n,z).

A uniform bound R gives only 2|T|R. This is the unresolved quantitative
issue, not an omitted inference.

## Builds and audits

All production files named above compile and have built oleans.
`TripleAudit.lean`, `TripleSparseAudit.lean`, and
`TripleSparseDownwardAudit.lean` report only propext, Classical.choice,
Quot.sound for the principal statements. Auxiliary debug files are not
production results and should not be blanket-built.

## Main unresolved problem

The weak power-saving exceptional-set estimates still permit far more than
o(log n) corrections per comparable scale. A constant bound for EACH
correction does not control their sum. Removing all endpoints incident to
all bad targets can also erase most of the base set; it is not a justified
repair. Downward corrections alone do not fill deficits or preserve the
original prefix discrepancy.

No compatible infinite two-sided repair schedule, improved exceptional
sparsity sufficient for the existing completion criterion, mixed-modulus
scale construction, or universal obstruction has been proved. None of the
new theorems settles the original existential conjecture.
