# Square-collision codegrees and integral linearization

This does NOT settle Erdős 773. The main file is unchanged and still has its
sole admission for 0<epsilon<=1/3. No actual Sidon lower exponent improved.

## Clean new modules

1. `GaussianDivisorBound.lean`
2. `SquareSumRepresentations.lean`
3. `SquareCollisionCodegrees.lean`
4. `SquareCollisionIntersections.lean`
5. `HypergraphLinearization.lean`
6. `SquareCollisionLinearization.lean`

None imports the admitted Spec theorem. All compile without warnings or
admissions, all have built .olean files, and every printed audit uses only
propext, Classical.choice and Quot.sound.

## Gaussian arithmetic

`GaussianDivisorBound.factor_submultisets_subpower` proves that for every
positive delta the number of submultisets of the normalized Gaussian prime
factors of nonzero z is at most C_delta*norm(z)^delta. The proof repeats the
elementary divisor argument: all Gaussian primes have integral norm >=2;
there are finitely many of bounded norm; large factors absorb each exponent
count (e+1) into norm(p)^(delta*e). The multiset interval cardinality formula
counts DISTINCT submultisets, not the duplicate-rich multiset powerset.

`SquareSumRepresentations.reps N T` consists of ordered positive roots
(a,b) in [1,N]^2 with a^2+b^2=T. Positive first-quadrant Gaussian integers
cannot be distinct associates. Sending (a,b) to the normalized factors of
a+ib injects these representations into factor submultisets of T, since
(a+ib) divides T in the Gaussian integers. The norm of T is T^2.

The results `reps_subpower` and `reps_height_subpower` give respectively

    reps(N,T) <= C_delta*T^delta                         (T>0),
    reps(N,T) <= C_delta*N^delta                         (0<T<=2N^2).

The constants may change between these statements. No prime-factor
classification formula for r_2(T) is assumed.

## Collision codegrees

`SquareCollisionCodegrees.edges A` counts unordered four-element root
supports, once each, admitting an equal square-pair sum. `pairEdges A a b`
filters for supports containing both prescribed roots.

For a<b, `pairEdges_card_bound` proves

    |pairEdges([1,N],a,b)|
      <= reps(N,a^2+b^2) + squareDifferenceReps(N,b^2-a^2).

The first term covers a,b on the same side, the second covers opposite
sides. The complement order costs no further factor. In particular
`pair_codegree_subpower` bounds the codegree by C_delta*N^delta uniformly
for 1<=a<b<=N. `eventually_pair_codegree_bound` absorbs the constant and
handles either order: eventually every distinct pair in [1,N] has codegree
at most N^delta. Subset monotonicity and pair symmetry are also public.

## Three-root intersections

`SquareCollisionIntersections.eq_of_three_common` proves: if A's square
values are ThreeAPFree, two collision edges sharing at least three roots
must be identical. Thus distinct edges intersect in at most two roots.

For a fixed triple a,b,c, the fourth square must be one of

    a^2+b^2-c^2,  a^2+c^2-b^2,  b^2+c^2-a^2.

Two distinct choices produce a three-term progression involving their
fourth square values and one of the original triple. AP-freeness excludes
this. The Lean proof uses sums of the four-element support to verify all
three possible pair partitions and does not assume a chosen ordering.

## Finite hypergraph linearization

`HypergraphLinearization.ambient_alteration` provides the existing Bernoulli
alteration bound on an arbitrary finite ambient set, using subtype transport.

For a four-uniform H on A, assume distinct edges intersect in at most two
vertices and every two-vertex subset is contained in at most K edges. Each
pair of distinct edges overlapping twice has union of size SIX. The number
of such union supports is at most |A|^2*K^2 (ordered edge pairs may overcount,
which is harmless). Deleting these supports gives an actual B subset A with

    |B| >= p*|A| - p^6*|A|^2*K^2,

and any distinct surviving edges intersect in at most one vertex. This is
`HypergraphLinearization.finite_selection`; K can be real. It does not assert
that B has no edges.

## Actual square-root selection

`SquareCollisionLinearization.finite_selection` applies the finite theorem
to an AP-free square-value family of roots A subset [1,N]. It replaces
|A|^2 in the cost by N^2 and retains AP-freeness.

`linear_collisions_four_fifths` proves that for each epsilon>0, eventually
there is an actual B subset [1,N] with

    |B| >= N^(4/5-epsilon),
    ThreeAPFree(B^2),
    distinct four-root collision supports intersect in at most ONE root.

Parameters: start with |A|>=N^(1-epsilon/4), take
K=N^(epsilon/4), p=N^(-1/5-epsilon/2), and
S=N^(4/5-3epsilon/4). The overlap-deletion term equals
S*N^(-7epsilon/4); the desired bound is S*N^(-epsilon/4).
Both small factors eventually are at most 1/2.

## Scope and remaining obstruction

The new 4/5 exponent is for a RELAXED property, not Sidonness. Even one
collision edge is compatible with linearity. Generic linear four-uniform
hypergraphs can still have much smaller independent sets, so no subpower-
loss extraction is implied. This does not establish epsilon=1/3 or any
part of the remaining original range. No statement was added to Spec.lean,
and no proof or disproof of the original conjecture has been submitted.

Potential next work: a selection argument beyond independent sampling would
need extra arithmetic structure, or a rigorously proved sparse-hypergraph
selection theorem with its actual quantitative loss tracked. Do not assume
that pair codegrees or linearity alone give near-linear independence.

## Logs

    /tmp/gaussian-divisor-bound.log
    /tmp/square-sum-representations.log
    /tmp/square-collision-codegrees.log
    /tmp/square-collision-intersections.log
    /tmp/hypergraph-linearization.log
    /tmp/square-collision-linearization.log
