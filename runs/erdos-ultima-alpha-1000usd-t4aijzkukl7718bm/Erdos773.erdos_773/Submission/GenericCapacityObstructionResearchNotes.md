# Generic bounded-difference capacity does NOT give near-linear Sidon extraction

This is NOT a disproof of Erdős 773. The constructed sets consist of ordinary
integer values and are not asserted to be squares. Spec.lean is unchanged,
with its single sorry for 0 < epsilon <= 1/3.

## Completed result

`GenericCapacityObstruction.finite_obstruction` proves that, whenever
n >= 1000 and log n >= 5, there exists B contained in [1,n^40] such that:

* |B| >= n^16/8;
* B is three-term-progression-free;
* every positive difference has at most two representations in B;
* every Sidon subset of B has fewer than n^15 elements.

`finite_power_gap` gives the integral form

    (maxSidonSubsetCard B)^16 <= 8^15 |B|^15.

`eventual_obstruction` proves these examples exist for all sufficiently
large n. Their cardinalities are unbounded. Thus a generic capacity-two to
Sidon conversion with only a subpower loss is impossible. This does NOT
rule out a conversion theorem using additional square-specific structure.

## Proof modules

1. SidonPartitionFunction: weighted independent-set branching. If every
   induced graph above w vertices has maximum degree at least D, and
   z <= (c-1)c^D, then Z(G,A,z) <= c^|A| (1+z)^w.
2. SidonDifferenceGraph: for a Sidon seed T, translates intersect in at
   most one point. Cauchy-Schwarz gives

       (|W||T|)^2 <= 2m |W| (|T|+d)

   when all induced difference-graph degrees on W are <= d.
3. SidonPartitionScales: with m=n^40, |T|=n^14,
   z=1/(4n^23), w=n^38, c=1+1/n^25, and
   D=3 floor(n/12)n^25, obtain Z <= exp(5n^15/4).
4. BernoulliCarrier: exact finite weighted counts on arbitrary finite
   ambient carriers, including weighted_family and weighted_uniform_count.
5. SidonSeedWitnesses: weight every independent remainder I by n^|I|,
   sum over all Sidon seeds of size n^14, and divide by
   n^(n^15-n^14). A Sidon subset of size >= n^15 forces penalty >= 1.
   At Bernoulli density p=1/(4n^24), expected penalty is <= exp(-n^15).
   Also n^40 exp(-n^15) <= 1.
6. IntegerDifferenceCapacity: at most m^2 AP supports of size 3 and
   at most m^4 supports of size 6. Once AP supports are absent, three
   representations of one positive difference are disjoint, hence create
   a forbidden six-support.
7. GenericCapacityObstruction: maximize

       |B| - retained_APs - retained_sixes - n^40 penalty(B).

   Expected reward is at least n^16/8, using the exact scales
   p m=n^16/4, p^3 m^2=n^8/64, p^6 m^4=n^16/4096.
   Positive reward excludes all large Sidon subsets. Delete retained
   AP/six obstructions; the reward inequality pays the deletion cost.
   The no-large-Sidon property is hereditary under deletion.

## Verification

All seven modules compile, with built oleans. Printed axiom audits contain
only propext, Classical.choice, Quot.sound. No admissions or unsafe
computation are used. Combined audit: GenericCapacityObstructionAudit.lean.
Logs: /tmp/generic-capacity-obstruction-audit.log and the corresponding
module-specific /tmp logs.

No proof submission has been made. This result only closes a proposed
GENERIC route. It neither improves the square-Sidon exponent nor gives
an upper bound for arbitrary subsets of the full square interval.

## Subsequent square-specific review

Rechecked the finite q=3 and q=5 checksum certificates and their recorded
limitations. The q=5 checksum is an arbitrary lookup table, not a uniform
algebraic family; the q=3 cubic does not extend even to q=5. No valid
concatenation or exponent amplification was obtained. Also reconsidered
the formal Gaussian irreducibility construction: its already verified
specialization counterexample still prevents treating polynomial Sidonness
as integer Sidonness without carry control. No new square-specific theorem
resulted from this review.

Latest main-file check: /tmp/spec-generic-capacity-check.log. It still reports
the admitted original conjecture. SHA-256 remains
917b6c178fa6b0ff7325ec3027dda121a1138cc1198ba712cac9352f5dca5c14.
