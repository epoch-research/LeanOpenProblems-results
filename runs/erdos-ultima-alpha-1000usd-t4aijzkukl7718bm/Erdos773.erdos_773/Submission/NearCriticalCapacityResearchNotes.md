# Bounded-capacity obstructions near square-root ambient density

This continuation does NOT settle Erdős 773. Spec.lean is unchanged, with its
sole admission at line 2031 for 0 < epsilon <= 1/3. The examples below are
ordinary integer VALUE sets, not sets of squares. No incomplete proof was
resubmitted.

## Exact bounded-capacity exponent

`CapacityEndpointObstruction.polynomial_obstruction` proves, for n>=1000,
log n>=5, and every fixed integer g>=1, the existence of

    B subset [1, n^(100(2g+1))],
    |B| >= n^(100g)/8,
    B is three-AP-free,
    every positive difference has at most g increasing representations,
    every Sidon subset of B has size < n^(40(2g+1)).

Put N=n^(50(2g+1)). The ambient interval is [1,N^2]. The cardinality lower
bound is exactly (1/8) N^(2g/(2g+1)), the usual bounded-capacity alteration
exponent on this root-height scale. The Sidon maximum M_B satisfies

    M_B^5 <= N^4.

For every fixed g>=3, 2g/(2g+1)>4/5, so this is a genuine fixed-power loss.
As g increases, the carrier exponent approaches one, but the upper exponent
for its Sidon subsets remains 4/5.

`eventual_endpoint_obstruction` packages these at unbounded heights N>=n,
for every sufficiently large parameter n, with the cardinality stated in
the exact integral form

    N^(2g) <= 8^(2g+1) |B|^(2g+1).

This does not assert examples at every integer height N.

## Explicit near-critical formulation

The earlier parameterization in the same continuation is retained in
`NearCriticalCapacityObstruction`:

    B subset [1,n^(100k)],
    |B| >= n^(50k-1)/8,
    positive difference capacity <=25k,
    every Sidon subset has size <n^(40k),

for every fixed k>=1 and all sufficiently large n.

`near_critical_obstruction` proves: for every epsilon>0, there is a FIXED
capacity g such that eventually in n there are N>=n and B subset [1,N^2]
with

    |B| >= N^(1-epsilon),
    B three-AP-free,
    positive difference capacity <=g,
    (maxSidonSubsetCard B)^5 <= N^4.

All constants, natural/real power conversions, and the fixed-capacity
quantifier order are checked. The capacity is not allowed to vary with n
inside a fixed epsilon instance.

## Proof organization

Seven completed modules:

1. DenseSidonPartitionScales: for ambient length R^100, Sidon seed size
   R^36, cutoff R^90, fugacity 1/(4R^50), and base 1+1/R^60, the seed
   difference-graph partition function is <=exp((5/4)R^40). Its branch
   degree is 12 floor(R^2/48) R^60, bounded by R^62/4.
2. DenseSidonSeedWitnesses: separate the witness weight x from R. Bernoulli
   density is 1/(4R^50 x); the weight x makes the partition fugacity exactly
   1/(4R^50). Penalize Sidon subsets of size >=R^40. For x,R>=1000 and
   log x>=5, expected penalty is <=exp(-R^40), and multiplying it by R^100
   costs at most one. The entropy estimate uses log R<=R, so no unproved
   relation between x and R is needed.
3. IntegerDifferenceCapacityGeneral: for every g, there are at most m^(g+2)
   relevant supports of size 2(g+1). After excluding APs, g+1 distinct
   increasing representations of one positive difference have disjoint
   endpoints and create one of these supports.
4. DenseCapacityScales: exact scalar reward bounds, for both relations
   R^50=x^(2g) and R^50=x^(2g+1). At the endpoint, the expected capacity
   deletion cost is R^50/(4^(2(g+1)) x), a small constant fraction of the
   retained mass. This is not treated as a negligible smaller power.
5. DenseGenericCapacityObstruction: maximize the finite Bernoulli reward
   cardinality minus retained AP/capacity supports minus R^100 times the
   large-Sidon penalty. Positive reward forbids large Sidon subsets before
   deletion. The no-large-Sidon property survives deleting forbidden edges.
6. NearCriticalCapacityObstruction: the first polynomial parameterization
   and the explicit real-power near-critical theorem.
7. CapacityEndpointObstruction: take x=n^50 and R=n^(2g+1) to satisfy
   R^50=x^(2g+1) exactly and attain the bounded-capacity exponent.

No sampling solver, untrusted computation, or assumed rounding theorem is
used. These proofs do not import Spec.lean.

## Relevance and limitation

This closes the possible generic shortcut that a carrier sufficiently close
to square-root ambient density, together with a fixed difference capacity,
might automatically have a near-linear Sidon subset. The counterexamples
can attain precisely the same cardinality exponent as the existing
bounded-capacity selection for squares.

It does NOT show that the actual square-specific bounded-capacity carriers
are bad. It supplies no upper bound for the first N squares and no lower
exponent above two thirds. Any successful conversion must use further
structure or a specially selected carrier, not just the displayed generic
properties.

## Short-translate review

The finite translated-cube and adjacent-quadratic reductions were reviewed
again. Sidonness at the extracted shifts still does not imply Sidonness at
every affine shift. No fixed-power upper bound for these sparse translated
patterns was proved, and no such bound is claimed by the new generic
counterexamples.

## Verification

`NearCriticalCapacityAudit.lean` prints 37 axiom audits. All use only
propext, Classical.choice, and Quot.sound (one uses a subset). The seven
modules compile without admissions, and their oleans are built.

Combined log: /tmp/near-critical-capacity-audit.log.
Individual logs: /tmp/dense-sidon-partition.log,
/tmp/dense-sidon-witnesses.log, /tmp/general-integer-capacity.log,
/tmp/dense-capacity-scales.log, /tmp/dense-generic-capacity.log,
/tmp/near-critical-capacity.log, /tmp/capacity-endpoint-obstruction.log.

Main check: /tmp/spec-near-critical-capacity-check.log. The original file
still has SHA-256
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
