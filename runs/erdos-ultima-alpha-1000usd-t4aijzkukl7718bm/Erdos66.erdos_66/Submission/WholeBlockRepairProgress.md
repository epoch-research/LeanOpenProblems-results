# Completed finite whole-coarse-block repair

## Original task status

The conjecture in `Submission/Spec.lean` is **not settled**. The file is
unchanged, still with its original `sorry`, and no proof or disproof has been
submitted. Its SHA256 is

    32d7caa914aad816045b3efa978ba8171e246a4dc01a8e77f192008b25ff41a0

This pass completes the three finite steps proposed at the end of
`TripleDeletionProgress.md`: joint packet instantiation, balanced curve
attachment with an exact aggregate decomposition, and transfer to actual
natural-number blocks. It does NOT provide compatible infinite scales.

## Main new theorem: actual finite integer blocks

`Erdos66RepairedIntegerBlocks.eventually_repaired_integer_blocks` in
`RepairedIntegerBlocksExplore.lean`:

Fix 0<epsilon<=1 and positive natural K,J. Put

    s(m) = ceil(exp(4m)),
    L(m) = floor(exp(12m)),
    q0(m,epsilon) = ceil(64*s(m)^2/epsilon^2),
    mu = m^3,
    M = (p*K)^2*J.

For every sufficiently large real m, and EVERY odd prime

    p > 8*(L(m)+1)+16,

there is a finite A subset [0,(L(m)+1)*M) with the GLOBAL bound

    r_A(n) <= (J+1)*(K^2+2K)*(1+4epsilon)*mu

for every natural n, and with

    |r_A(n)-J*K^2*mu|
      <= ((J+1)*(K^2*(5epsilon)+2K*(1+5epsilon))+K^2)*mu

at EVERY target in

    (q0+1)*M <= n < (L+1)*M.

There are no exceptional coarse or fine targets in this interval.
The upper bound includes the initial coarse block q=0 and all targets
outside the useful interval. The prime is quantified after the m threshold;
its size does not enter a hidden concentration union bound.

The theorem is a finite statement. It is not a logarithm-normalized
infinite limit theorem, and no inference of compactness compatibility is
made from it.

## Main plane theorem

`Erdos66RepairedPlaneProfile.eventually_repaired_plane_profiles`:
under the same epsilon,m,p conditions, there is a family B_i of plane sets,
empty for i>L, such that each B_i is either empty or ONE full parabola with
nonzero parameter. Define

    R_B(q,z) = sum_{i=0}^q pairCount(B_i,B_(q-i),z).

Then

    R_B(q,z) <= (1+4epsilon)*mu                for all q,z,
    |R_B(q,z)-mu| < 5epsilon*mu               for q0<=q<=L, all z.

The one-curve-per-coarse-label property is retained explicitly. The repair
does not replace a coarse color by a union of many curves.

## Construction details

### 1. Repair only the useful exceptional centers

The previous deleted profile is (D,T0,a), with all sums in T0 killed, the
unsigned profile accurate outside T0, and the signed profile small at every
q<=2L. Set

    T = T0 intersect [q0,L].

Only T is refilled. Holes outside the useful interval are harmless for the
global upper bound and are left empty. This permits a larger common choice
width than was suggested in the previous progress note.

There are k=floor(mu/4) groups per target and two packet types per group.
The coordinate type is

    Coord(T,k) = (T x Fin k) x Bool,

and each coordinate has two endpoint labels, giving four new points per
group. The number of coordinates is O_epsilon(m^5).

### 2. Common width W=s(m), not the earlier proposed exp(2m)

`WholeBlockPacketParametersExplore.lean` now proves the scalar estimates for

    W=s(m)=ceil(exp(4m)), t=m, mixed-hit threshold R=14.

For Kc packet coordinates with 0<=Kc<=C*m^5 and at most
3*exp(12m) target tests, the selection budget is eventually below one,
uniformly in Kc and in the number of tests.

The old-set envelope is V=2*m^3. If H is the total mixed-hit/avoidance mass,

    H = Kc*2*sqrt(2WV)/W,

then the checked bounds are

    H <= 8*C*m^7*exp(-2m),
    exp(m)*H <= 8*C*m^7*exp(-m),
    collision cost <= 32*C^4*m^20*exp(-4m).

The remaining target-test contribution is at most 3*exp(1-2m) once the
last tilted hit mass is <=1. All these quantities tend to zero.

`start_width` proves the exact inequality

    12*s(m)+48 <= q0(m,epsilon)

for 0<epsilon<=1. Thus every repair center admits the common width inside
its middle-third choices; no extra asymptotic location argument is needed.

### 3. Natural labelled packets

`NaturalLabeledPacketsExplore.lean` proves the casting and support bridge
from integer uniform-width packets to natural labels. It returns an
injective endpoint map d, with

* d(label)<=L and d(label) not in D;
* each designated pair sums to its prescribed center;
* all undesignated unordered pairs are Sidon across the ENTIRE repair;
* the mixed coarse count pairs(image(d),D,q) is <28 for every natural q.

The last conclusion is global. Counts outside [0,2L] vanish by support.

`ExceptionalLabeledPacketsExplore.lean` proves
`eventually_exception_packets`, uniformly over all eligible D,T. It handles
the cardinality of `(T x Fin floor(mu/4)) x Bool` and instantiates the
scalar budget. The constant C can be taken as 25088/epsilon^2+1.

### 4. Exact weighted aggregate accounting

`WeightedPacketAlgebraExplore.lean` defines finite weighted coarse fibers.
It proves reindexing under the endpoint injection, the exact designated
sum, and an upper bound of 2 on the number of unintended ordered edges.
When every fine edge weight lies in [0,2], the unintended new/new weight is
therefore at most 4.

`BalancedWeightedPacketExplore.lean` combines this with the mixed count
bound and the balanced two-type identity. At every coarse target q,

    0 <= total_weight(q)-old_weight(q)-4k*1_T(q) < 116.

The mixed coarse count <28 gives weighted mixed count <56 in each
orientation; the unintended new/new contribution is <=4. Crucially, 116 is
independent of |T| and k.

### 5. Actual curve families

`CurveFamilyPacketExplore.lean` defines the new family using
`Function.extend`: at an injected repair label it is the assigned repair
curve, and elsewhere it is the old colored family.

The fixed four parameters u,v,x,y from the previous pass satisfy

    u+v=x+y=1,
    chi(uv)=+1, chi(xy)=-1,

with no zero parameters or opposite pairs, including opposites to the old
parameter palette. The plus and minus designated root counts sum exactly
to 2; reverse orientations give 4 per group. Every other new/new or new/old
curve pair has at most 2 representations, INCLUDING the fine origin.

`extendedCurves_collateral` proves the bound 116 for these ACTUAL plane
counts, not merely for an abstract model. Support-reindexing lemmas also
extend the old affine plane estimate to q>=L+1, retaining all upper-tail
targets.

### 6. Filling holes and transferring carries

At q in T, the old unsigned count is zero, so its entire plane aggregate is
exactly zero. The new aggregate lies between 4k and 4k+116. Since

    mu-4 < 4k <= mu,

the repaired error is <120 there. Elsewhere, unsigned and signed errors are
each <2epsilon*mu. Once 120<=epsilon*mu, the stated global upper and local
flatness bounds follow.

`AggregateUpperTransferExplore.lean` adds a global collective upper bound
for the carry transfer, with q=0 proved separately rather than omitted.
It also supplies a general finite-support lemma for block sets.

The pre-existing collective plane/cyclic/integer error transfer gives the
flatness bound in the main theorem with no sum over individual color-pair
errors.

## Verification

All nine new production files compile and have built oleans:

1. WholeBlockPacketParametersExplore.lean
2. NaturalLabeledPacketsExplore.lean
3. ExceptionalLabeledPacketsExplore.lean
4. WeightedPacketAlgebraExplore.lean
5. BalancedWeightedPacketExplore.lean
6. CurveFamilyPacketExplore.lean
7. RepairedPlaneProfileExplore.lean
8. AggregateUpperTransferExplore.lean
9. RepairedIntegerBlocksExplore.lean

`RepairedIntegerBlocksAxiomCheck.lean` audits the principal theorems. All
use only propext, Classical.choice, Quot.sound. There are no sorries or
new axioms in the new production files.

The two small `WeightedPacketChecks.lean` and `IntegerRepairChecks.lean`
files were name-search scratch files; they intentionally contain some
failing #check commands and are not production dependencies.

## Remaining mathematical gap

No compatible infinite family is constructed. In particular:

* a good finite block cannot simply be joined to a preceding one: the
  mixed representation counts between different primes are not controlled;
* literal cyclic compactness does not preserve the needed lower bounds at
  every natural target;
* row sparsity can protect a short prefix, but the existing row argument
  leaves a large support/transition gap;
* the completed finite construction does not contradict any previously
  proved placement-cost or transition-budget barrier.

The next essential advance is a genuine infinite-scale compatibility
principle or a different global construction, not merely a further
optimization of the finite repair constants. No disproof of the existential
statement has been obtained.
