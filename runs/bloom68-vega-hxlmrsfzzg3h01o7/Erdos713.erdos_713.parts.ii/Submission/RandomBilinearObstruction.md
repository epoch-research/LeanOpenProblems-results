# Growing-rank bilinear incidence: exact copy counts and a rational first-moment barrier

## Status

**This is not a counterexample to Erdős 713(ii).** No fixed ordinary graph with a proved irrational extremal exponent, even in the Theta sense, is produced. No matching upper bound for arbitrary ordinary H-free graphs is claimed. The target `Submission/Spec.lean` and all pre-existing files are unchanged.

This attempt tests a different construction class from a fixed tensor template or fixed finite-state word relation: the number of bilinear constraints and the vector-space dimension both grow. The new results in this workspace are:

1. an exact finite-type formula for the expected number of ordinary labelled bipartite H-copies in a random vector-valued bilinear incidence graph;
2. a rational boundary for what the direct expected-edge-minus-copy deletion certificate can achieve, even allowing unbounded ambient rank;
3. for the cube Q_3, an explicit exact formula and a proved sharp coarse threshold at constraint ratio 2/3 for the *uncleaned random graph*.

For the cube, these results rule out the uncleaned uniform-random route to an extremal irrational exponent. For general connected H, they rule out a genuine irrational exponent obtained solely by the stated first-moment deletion certificate. They do not rule out specially designed bilinear maps, stronger deletion arguments, or nonuniform code families. There is no claim of priority over the literature.

The cube calculation below is a failure test, not a revival of the previously rejected scrambled tensor or biaffine F_8 candidate. It uses an independently specified uniform distribution on all bilinear maps over F_2.

## 1. The construction being tested

Fix a prime power q. Let U = V = F_q^d, W = F_q^c, with c >= 1, and fix b != 0 in W. Choose a uniformly random linear map

    B : U tensor V -> W,

or equivalently c independent uniformly random d-by-d scalar matrices. Form the ordinary simple bipartite graph G_B with disjoint vertex classes

    U minus {0},    V minus {0},

and edge xy precisely when B(x tensor y) = b. There are

    N_d = 2(q^d - 1)

vertices. Every potential edge has probability q^(-c), so

    E e(G_B) = (q^d - 1)^2 q^(-c).                    (1)

For q = 2 the edge indicators are pairwise independent. Indeed, two different pairs of nonzero vectors have different nonzero rank-one tensors, and two different nonzero vectors over F_2 are linearly independent. Thus

    Var e(G_B) <= E e(G_B).

In particular, if c/d -> theta in (0,1), then with probability tending to one

    e(G_B) = (1 + o(1)) (2^d - 1)^2 2^(-c)
           = N_d^(2-theta+o(1)).                    (2)

Equation (2) is NOT an all-n exact power asymptotic, nor even a fixed leading constant along every d. Rounding c can cause a bounded multiplicative oscillation. More importantly, H-freeness must be proved independently.

## 2. Exact finite-type formula for every fixed H

Fix a labelled bipartite graph H with left vertices 1,...,l, right vertices 1,...,r, and nonempty edge set E. Count injections of the two parts into the corresponding parts of G_B; extra host edges are permitted. Write X_H for this number of labelled, side-preserving ordinary copies.

Let E_L = F_q^l with standard basis e_i, and E_R = F_q^r with basis f_j. A subspace K <= E_L is *admissible* if it contains none of

    e_i,                 e_i - e_j  (i != j).

These are exactly the kernels of linear maps taking the standard basis to distinct nonzero vectors. Define admissible L <= E_R similarly. Put

    s = dim(E_L/K),       t = dim(E_R/L).

For an admissible pair K,L, define

    T_(K,L) : F_q^E -> (E_L/K) tensor (E_R/L),
    T_(K,L)(e_(ij)) = [e_i] tensor [f_j].

Let rho = rank T_(K,L), and let epsilon : F_q^E -> F_q send every edge basis vector to 1. Call the pair *consistent* if

    ker T_(K,L) <= ker epsilon.                     (3)

For k <= d set

    P_k(d) = product_(i=0,...,k-1) (q^d - q^i),

and set P_k(d) = 0 for k > d. Then the exact formula is

    E X_H = sum_(admissible, consistent K,L)
                P_s(d) P_t(d) q^(-c rho).           (4)

### Proof

An injective assignment x_1,...,x_l of nonzero vectors extends uniquely to a linear map E_L -> U. Its kernel is an admissible K. For a fixed K, such assignments correspond exactly to injective linear maps E_L/K -> U, of which there are P_s(d). The same argument gives P_t(d) for the other side.

For a fixed assignment, the edge conditions prescribe the value b on every edge tensor. They are consistent exactly when every linear relation among those tensors has coefficient sum zero: this is (3), since b != 0. When consistent, they prescribe one linear map on the rho-dimensional span of the edge tensors. A uniform B has that restriction with probability q^(-c rho). The embeddings of the two quotient spaces induce an injective map on their tensor product, so the rank and consistency test depend only on K,L, not on their ambient embeddings. Summing proves (4).

This is an injective-copy formula, not a homomorphism-count surrogate. The admissibility conditions exclude zero vertices and identifications within either vertex class.

## 3. What direct random alteration can certify

Assume now that H is connected and has at least two edges. Every consistent pair in (4) has rho >= 2. Otherwise all edge tensors, having the same prescribed nonzero value and lying on one line, must be equal. Two adjacent edges then identify their two distinct endpoints on one side, contradicting admissibility.

Define

    R_(H,q) = max_(admissible, consistent K,L)
                    (s+t-2)/(rho-1).                (5)

The maximum is nonempty: K=L=0 is consistent, with s=l, t=r, rho=e(H). Thus R_(H,q) is a rational number.

If c/d -> theta, (4) gives

    lim (1/d) log_q E X_H
        = max_(K,L) (s+t-theta rho).

Consequently theta > R_(H,q) ensures the strict first-moment condition

    E X_H = o(E e(G_B)),

whereas theta < R_(H,q) makes this ratio tend to infinity. At theta = R_(H,q), lower-order terms in c-R_(H,q)d can decide whether the ratio tends to zero; for example a positive offset tending to infinity does so. Thus R_(H,q) is the leading-power boundary, not an assertion excluding useful sublinear corrections at equality. These conclusions concern this expectation condition, not every possible deletion algorithm or exceptional deterministic B.

There is also an endpoint lower bound. If R = R_(H,q) < 1, take

    c = ceil(R d) + C,

where C is a sufficiently large constant depending only on H,q. From (1) and (4), using P_s(d) <= q^(ds) and (q^d-1)^2 >= (1-1/q)^2 q^(2d),

    E X_H / E e(G_B)
      <= (1-1/q)^(-2)
         sum_(K,L) q^((s+t-2)d-c(rho-1))
      <= (1-1/q)^(-2)
         sum_(K,L) q^(-C(rho-1)).                   (6)

Choose C so that twice the last expression is at most 1/2. The factor two accounts for the two possible orientations of a connected bipartite H in a bipartite host; the transposed orientation has the same expectation. Some B therefore satisfies

    e(G_B) - (number of labelled copies in both orientations)
       >= (1/2) E e(G_B).

Delete one edge from every original labelled copy, deleting repeated chosen edges only once. All ordinary H-copies are destroyed and at least the displayed number of edges remains. Hence

    ex(N_d,H) >= A N_d^(2-R)

for a fixed A > 0 and all sufficiently large d. Since N_(d+1)/N_d -> q, padding the preceding construction with isolated vertices gives

    ex(n,H) = Omega(n^(2-R)) for ALL sufficiently large n.    (7)

Connected H with at least two edges has no isolated vertices, so this padding is harmless.

### Consequence and precise scope

An irrational exponent a obtained by using a strict choice theta > R, with a=2-theta, cannot be the extremal exponent: (7) gives a strictly larger rational power, so

    ex(n,H)/n^a -> infinity.

At the boundary the certified exponent 2-R is rational. This closes the direct expected-edge-minus-copy route, not the entire class of bilinear maps.

Even changing q cannot make the best boundary of this method irrational: R_(H,q) always belongs to the fixed finite set

    { (s+t-2)/(rho-1) :
      1<=s<=l, 1<=t<=r, 2<=rho<=e(H) }.

A minimum over the R_(H,q), as q ranges over prime powers, is therefore attained and rational. This does NOT assert that the optimal deterministic bilinear incidence construction has such a rational rate.

## 4. An explicit ordinary-cube calculation over F_2

Let H=Q_3=K_(4,4) minus a perfect matching, with edges i-j exactly when i != j. Let

    P_3(d) = (2^d-1)(2^d-2)(2^d-4),
    P_4(d) = P_3(d)(2^d-8),

with the earlier zero convention when d is too small. Formula (4) specializes to

    E X_(Q_3)
      = [P_4(d)^2 + 2 P_3(d) P_4(d)] 2^(-12c)
        + P_3(d)^2 2^(-9c).                        (8)

### Complete classification behind (8)

Four distinct nonzero binary vectors have rank at least 3. If their rank is 3, their unique nonzero relation has weight 3 or weight 4.

A weight-3 relation makes a cube copy impossible. Some opposite cube vertex is adjacent to precisely those three indexed vertices. Applying B to their zero sum would give b+b+b=b != 0, a contradiction.

A weight-4 relation is allowed and says that the four vertices form an affine plane not containing zero. Thus on each side only two kernel types are consistent: no relation, or the relation 1111. There are four pairs of types:

    left rank  right rank  edge-tensor rank
        4          4             12
        3          4             12
        4          3             12
        3          3              9.

For a weight-4 relation, the three required incident values b in any column force the missing diagonal value also to equal b. All four tensors in that column are spanned by its three off-diagonal tensors. If the other side has rank 4 this gives rank 3*4=12. If both sides have rank 3, all sixteen rectangle tensors are spanned, giving rank 3*3=9. The prescribed value is consistent: the functional taking each of the four affine-plane points to 1 is linear on their three-dimensional span. These observations prove the table and (8).

Although X counts one orientation, X>0 is equivalent to an ordinary cube copy: Q_3 has an automorphism interchanging its two bipartition classes.

For direct alteration the three ratios in (5) are

    6/11, 5/11, 1/2.

Thus its boundary is R_(Q_3,2)=6/11, and its endpoint lower exponent is 16/11. No irrational boundary is hidden by growing d and c.

## 5. A sharp coarse threshold for the uncleaned random graph

Let d tend to infinity and c/d -> theta. Then

    theta < 2/3  ==>  P(G_B contains Q_3) -> 1,
    theta > 2/3  ==>  P(G_B is Q_3-free) -> 1.       (9)

No claim is made about the critical window c=(2/3)d+O(1).

### Upper side of the threshold

If c >= (2/3+epsilon)d, (8) gives

    E X_(Q_3)
      <= 2^(-12 epsilon d)
         + 2*2^(-d-12 epsilon d)
         + 2^(-9 epsilon d) -> 0.

Markov's inequality proves cube-freeness with probability tending to one.

### Lower side: second moment, not just a large expectation

Let Z count ordered linearly independent triples x_1,x_2,x_3 in U and y_1,y_2,y_3 in V such that

    B(x_i,y_j)=b for all 1<=i,j<=3.

Then

    E Z = P_3(d)^2 2^(-9c).                        (10)

Any successful configuration gives an ordinary K_(4,4), hence Q_3: append x_1+x_2+x_3 and y_1+y_2+y_3. Each appended vertex is nonzero and distinct from its three predecessors, and every one of the sixteen bilinear values is b (sums involve an odd number of b's).

For two ordered configurations, let s and t be the dimensions of the intersections of their respective three-dimensional left and right spans. The intersection of their constraint spaces has dimension st, because

    (A tensor B) intersect (A' tensor B')
        = (A intersect A') tensor (B intersect B').

This identity follows by choosing bases adapted to the two left subspaces and separately to the two right subspaces; the tensor subspaces are spanned by rectangular sets of common ambient basis tensors.

If st=0, the two events are independent. If st>0, their prescribed maps on the intersection may disagree; otherwise their joint probability is exactly

    2^(-c(18-st)).

It is therefore always at most this quantity.

For each s,t in {0,1,2,3}, the number of ordered pairs of configurations with those intersection dimensions is at most

    C 2^((12-s-t)d),                               (11)

where C is absolute. To prove (11), fix the first left triple. There are constantly many choices for the s-dimensional intersection inside its 3-space. Choose at most 3-s additional arbitrary ambient vectors, then choose an ordered basis for the resulting 3-space (at most |GL(3,2)| choices). This gives at most a constant times 2^((3-s)d) second triples. Multiply by at most 2^(3d) first triples and repeat on the right.

Since P_3(d) is bounded below by a fixed positive multiple of 2^(3d), (10)--(11) give

    Var Z / (E Z)^2
       <= C' sum_(1<=s,t<=3) 2^(-d(s+t)+cst).       (12)

For 1<=s,t<=3, s+t >= (2/3)st. Thus if c <= (2/3-epsilon)d every summand in (12) is at most 2^(-epsilon d). The variance ratio tends to zero. Chebyshev's inequality implies P(Z=0)->0 and proves the lower side of (9).

This verifies actual injective copies. A large first moment alone would not have justified this part of the conclusion.

## 6. Why neither regime can give the requested counterexample

If theta<2/3, the uncleaned random graph is not cube-free with high probability. If theta>2/3, its raw edge exponent is 2-theta<4/3. Such a graph is far from cube-extremal.

For a self-contained comparison, over every finite field F_Q take the bipartite graph on two copies of F_Q^2 minus {0}, with

    (x_1,x_2) ~ (y_1,y_2)  iff  x_1 y_1+x_2 y_2 = 1.

It has 2(Q^2-1) vertices and (Q^2-1)Q edges and is C_4-free. Two independent left vectors have at most one common neighbor; two dependent but distinct left vectors cannot have a common neighbor, since the proportionality factor would have to be 1. Since Q_3 contains a C_4, this is also Q_3-free. Taking Q=2^k and padding the preceding size proves

    ex(n,Q_3) = Omega(n^(3/2))

for all sufficiently large n. This comparison is an elementary standard lower construction, not a new claimed extremal theorem. It also dominates the 16/11 alteration exponent.

There is a particularly important scope check: for Q=2^k, the dot-product map above is itself F_2-bilinear with d=2k and c=k. It is therefore an exceptional deterministic map in the EXACT SAME model, at theta=1/2, below the random cube-appearance threshold 2/3. Thus replacing (9) by a statement about every bilinear map would be false. This is a concrete obstruction to upgrading a random-model calculation into an ordinary-H upper bound.

## 7. Verification and remaining gaps

`Submission/random_bilinear_obstruction.py` independently checks:

- all admissible binary kernel pairs for the four vertices on each side;
- their consistency and edge-tensor ranks in (8);
- exact labelled cube counts in all 512 scalar bilinear graphs with d=3;
- the expected cube count for d=4,c=1, using all five possible matrix ranks and exact rank multiplicities (covering all 65,536 scalar matrices);
- independent direct ordinary-copy enumeration against an inclusion-exclusion cube counter on small fixtures;
- edge pairwise independence in a complete small distribution;
- the tensor-space intersection dimension identity used in the second moment;
- the finite-field C_4-free comparison on small prime fields;
- explicit coordinate matrices for the exceptional deterministic maps over F_4, F_8, and F_16, verified in the binary model with (d,c)=(4,2),(6,3),(8,4), respectively.

Run from `/workspace/leanproject`:

    python3 -m py_compile Submission/random_bilinear_obstruction.py
    python3 Submission/random_bilinear_obstruction.py

The test log is `/tmp/RandomBilinearObstruction.tests.log`. Exact expectation checks give 441/8 labelled cubes for d=3,c=1 and 1091475/8 for d=4,c=1. The exceptional binary maps have (vertices,edges)=(30,60),(126,504),(510,4080), all C_4-free. The preservation manifest `/tmp/RandomBilinearObstruction.before.json` records all 21 pre-existing files; the final check leaves every one unchanged.

The script validates finite identities and implementations. The all-d first/second-moment arguments are proved above, not inferred from finite testing. No Lean formalization of this note is claimed.

Essential missing bridges for a disproof are still:

1. a specially structured growing-rank/coding construction avoiding ONE fixed ordinary H at a genuinely new irrational rate;
2. a sharp upper bound for EVERY ordinary H-free graph, not just hosts of the incidence form;
3. an exact positive coefficient and convergence for ALL n.

The finite-type expectation identity does not upper-bound the number of copies in each deterministic B. In particular, it does not exclude rare algebraic maps. Nor does an optimal code rate, if found, automatically bound arbitrary H-free graphs. These are substantive mathematical gaps, not omitted routine steps.
