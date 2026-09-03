# Finite-profile and density-transfer investigations

These are supporting results and limitations, **not a proof or disproof of
`Erdos713.erdos_713.parts.ii`**. `Spec.lean` remains unchanged. Except for the
exact finite tensor bound identified below, this note is mathematical working
material, not a Lean formalization.

## 1. Exact kernel profiles and products

For a finite graph H, let Pi be the partitions of V(H) into independent sets.
Let H/pi have parallel edges simplified, and set

    kappa_pi(G) = inj(H/pi,G).

These count homomorphisms H -> G with exactly kernel pi. For rho in Pi,

    hom(H/rho,G) = sum_{pi coarser than rho} kappa_pi(G).

Consequently logarithmic limits, allowing minus infinity for zero counts,
satisfy a finite max-plus system. Ordinary H-freeness sets the discrete
kernel coordinate to zero. The other kernel exponents are additional unknowns;
they cannot be replaced by expressions in the edge exponent without proof.

The categorical-product rule is

    kappa_rho(G tensor G')
      = sum_{pi meet sigma = rho} kappa_pi(G) kappa_sigma(G').

This follows by intersecting the kernels of the two coordinate maps. For a
bipartition (A,B) of H without isolates, collapsing A and collapsing B gives
two star quotients whose partition meet is discrete. Thus large-degree graphs
can have H-free factors but an H-containing product. If the profile includes
all quotients, another H-free host cannot realize the same coordinatewise
product hom profile: inversion would give the same positive injective count.

The general rational-polyhedrality of tropical graph profiles is explicitly
an open question in `/corpus/src/2004.05207/newGraphProfiles.tex`, following
Theorem `thm:tropGU`. The Hadamard-product argument there concerns hom densities
of unrestricted graphs, not ordinary H-free graphs.

## 2. A two-parameter polynomial model of universal identities

Fix a cyclic H and finitely many graph coordinates, with all orders at most K.
For a nontrivial tree T define the integer polynomial

    R_T(D) = D product_{v in T} (D-1)_(deg_T(v)-1),

where the subscript is a falling factorial. Put R_K1=1. For connected F put

    Q_F(D) = sum_{pi: F/pi is a loopless tree} R_(F/pi)(D),
    Phi_F(N,D) = N Q_F(D).

For disconnected F, multiply Phi over its connected components. In particular
Phi_K1=N, Phi_K2=ND, and Phi_T=N D^e(T) for a tree.

If B is D-regular of girth greater than K, a homomorphic image of any connected
F under consideration is a tree. Rooted tree embedding counts give exactly
hom(F,B)=Phi_F(|B|,D). For every fixed integer D>=2, a finite D-regular graph
B_D of arbitrarily prescribed fixed girth exists. Disjoint unions of r copies
of B_D are H-free and realize Phi_F(r|B_D|,D).

Therefore every polynomial identity P in N and the finitely many hom counts
which holds on ALL H-free graphs vanishes identically after substitution Phi:
for each fixed D it vanishes at infinitely many N=r|B_D|, and then its
coefficients vanish for infinitely many D. The identity ideal leaves N and D
independent. This argument does not include extremality equations or arbitrary
polynomial inequalities.

Formal injective counts obtained by partition inversion vanish identically
for every cyclic F. For a forest with k components and e edges they equal

    N^k D^e [1 + O_F(1/D + 1/N)].

Indeed identifications either merge components, lowering the N-degree, or
lower the D-degree. Formal induced counts of forests are

    N^k D^e [1 + O_F(1/D + D/N)],

by inclusion-exclusion over added forest edges; cyclic supergraphs have zero
injective count. Hence the finitely many scalar counts are nonnegative for
D -> infinity and D=o(N), with their universal counting equalities intact.
At integer N,D they are integers. Choosing D divisible by K! also supplies
finite automorphism divisibility: all terms involving an edge are divisible
by D; the edgeless terms are ordinary falling factorials.

For example, choose D_N=K! floor((2c/K!)N^beta), where c>0 and 0<beta<1.
Then the formal edge count ND_N/2 is asymptotic to c N^(1+beta), and all
nonzero fixed hom coordinates have exact leading constants and exponents of
the form k+j beta. Irrational beta is not excluded by these identities.

For C8 one obtains

    Phi_C8(N,D) = N(14D^4 - 28D^3 + 20D^2 - 5D),
    formal inj(C8) = 0.

For irrational 1/5<beta<1/4, this also satisfies the usual C8 closed-walk
lower bound D^8 <= Phi_C8 for sufficiently large N. It does NOT assert
realizability, global extremality, or all other graph inequalities. In
particular, enlarging the coordinate list and imposing more inequalities
can reject this particular tree model; no finite-inequality impossibility
claim is being made.

Parent verification: `/tmp/FiniteProfileParentCheck.py` enumerates the exact
partition polynomials for C4, C6, C8, checks their Mobius inversions vanish,
and independently checks the walk counts on the 13-cycle at D=2. The log is
`/tmp/FiniteProfileParentCheck.log`. These are exact algebra checks, not a
numerical search for a counterexample to the conjecture.

## 3. Exact tensor repair bound — formalized and independently audited

`Submission/TensorRepair.lean`, namespace `Erdos713TensorRepair`, has sole
import `FormalConjecturesUtil`. For finite G,G' and any ordinary H-free
F contained in their categorical product, it proves

    2e(F) <= sum_{u,v} ex(d_G(u)+d_G'(v), H).

At center (u,v), the disjoint sets N_G(u) x {v} and {u} x N_G'(v) form a
complete bipartite rectangle. Its F-restriction is H-free and has at most
the indicated extremal number of edges. Each product edge lies in exactly
two rectangles. The Lean proof implements this via an explicit equivalence
between darts of F and the disjoint union of left-to-right rectangle edges.
It also proves e(G tensor G')=2e(G)e(G') and the uniform-bound corollary.

For a D-regular n-vertex G this gives

    e(F) <= (n^2/2) ex(2D,H),
    e(F)/e(G tensor G) <= ex(2D,H)/D^2.

Under ex(t,H)~c t^alpha, 1<alpha<2, this retention fraction is O(D^(alpha-2)).
For the previously verified regular cores with e(G)~c n^alpha and
Delta(G)=n^(alpha-1+o(1)), the same local estimate gives

    e(F) <= n^(2+alpha(alpha-1)+o(1)),
    e(F)/e(G tensor G) <= n^(-(alpha-1)(2-alpha)+o(1)).

Thus deletion-based tensor-square repair loses even the original polynomial
extremal exponent at the squared vertex scale. These asymptotic consequences
are written deductions, not additional theorems in the Lean module.

Parent read all 199 non-audit source lines, rebuilt a fresh olean under strict
settings, and reran the full axiom audit (38 theorem declarations, including
generated proof lemmas). Logs: `/tmp/TensorRepair.parent-strict.log`,
`/tmp/TensorRepair.parent-build.log`, `/tmp/TensorRepair.parent-audit.log`.
Only propext, Classical.choice and Quot.sound occur. Spec's original hash
was independently checked after the build.

## 4. Irrational clone density is possible, but does not fix the exponent

Let J be the disjoint union K4^(3) plus one triple. Its extension F adds a
new vertex and triple for each of the twelve uncovered original pairs.
Then v(F)=19, e(F)=17, F has no isolates, and its triples have empty total
intersection. Yan--Peng and the extension identity give

    pi_3(F) = p = sqrt(3)/3.

The statements were checked in `/corpus/src/2112.14935/2112.14935.tex`,
Proposition `relationlt` and Theorem `main`. The assertion concerns the
extension F, not the original J's Turan density.

Define one ordinary bipartite H: its left side is V(F) plus two apices x,y.
For each triple e of F, give it 25 distinct right vertices, each adjacent
exactly to e union {x,y}. Thus v(H)=446, e(H)=2125, and minimum degree is 5.

For m points, let G_m have one apex v and 25 vertices z_(T,j) for every
triple T of points, with N(z_(T,j))=T union {v}. It is H-free: right-side
vertices have degree 4, and H's high-degree apices rule out the opposite
bipartite orientation.

Add a vertex v' adjacent to S subset N(v). Write

    A(S) = {T: all 25 vertices z_(T,j) belong to S}.

There is the exact ORDINARY-copy equivalence

    G_m + v'S is H-free iff A(S) is F-free.

In any H-copy its high-degree apices must lie on the point/apex side.
Each degree-5 right vertex must map to a selected z and use its entire
five-element neighborhood. Hence v and v' lie in every image right
neighborhood. Their preimages are exactly x,y, because the intersection
of all right neighborhoods of H is {x,y}. The remaining left vertices
then embed F in A(S). Conversely such an F-copy supplies H immediately.
Therefore, with M=binom(m,3), the maximum safe |S| is exactly

    24M + ex_3(m,F),

and its fraction of d(v)=25M tends to the irrational number (24+p)/25.
No color or induced-embedding restriction is involved.

Nevertheless unrestricted ordinary ex(n,H)=Theta(n^(9/5)): H's right
side has maximum degree 5, giving the upper bound by dependent random
choice; H contains K_(5,25), giving the matching lower bound from norm
graphs (25>4!). Sources checked: `/corpus/src/0909.3271/0909.3271.tex`,
one-sided bounded-degree theorem, and
`/corpus/src/1306.5167/FureSimSurvE_arXiv_v2_.tex`, norm-graph theorem.
Thus any pure-power exponent for this H is 9/5. No claim of an all-n
leading constant is made. Moreover e(G_m)~4v(G_m), so these witnesses are
far from globally extremal and do not satisfy the regular-core bounds.

With k apices and L repeated right vertices per r-edge, the analogous
clone fraction is 1-(1-pi_r(F))/L. If L>(r+k-1)!, the global exponent is
2-1/(r+k). For the same F and L=121, k=2 and k=3 have the same irrational
clone fraction but global exponents 9/5 and 11/6. Scalar clone capacity
alone therefore does not determine the exponent.

Reusing a fixed pool is also limited: if H is contained in K_(a,b), t
vertices each adjacent to at least beta d members of one d-element pool
satisfy

    t binom(ceil(beta d),b) <= (a-1) binom(d,b).

Thus t is bounded for a fixed positive beta as d grows. Higher-order
uncolored copies cannot be ignored when iterating cloning.

## 5. A finite-scale algebraicity criterion

If f(n)~c n^alpha, c>0, and the limiting ratios at scales 2,3,5 are all
algebraic, then alpha is rational. The ratios are 2^alpha,3^alpha,5^alpha.
For irrational alpha, the six exponentials theorem applied to (1,alpha)
and (log 2,log 3,log 5) makes at least one of these transcendental. The
special case is explicitly stated in
`/corpus/src/2105.05809/_36_the_six_exponentials_theorem.tex`.

This does NOT prove those ratios algebraic for extremal numbers. Limits
of finite algebraic optimizations can be transcendental. In particular,
unbounded products of (1+kappa/j) from j=n to qn-1 tend to q^kappa; their
finite factors can be algebraic while their limit is transcendental.
A one-step asymptotic with an o(1) coefficient error also need not yield
a positive power-law constant: the weighted accumulated error may diverge.

The unresolved step remains a globally sharp ordinary-H construction or
comparison, not the availability of an irrational local density or a
finite collection of polynomial counting identities.

## 6. Selective duplication: a forward cyclic-witness strengthening

For 2<=t<k and S subset V(G), define T_(S,t)(G) by deleting all old edges
inside S, replacing each member of S by t independent twins, and leaving
other vertices single. Its exact counts are

    v(T)=n+(t-1)|S|,
    e(T)=e(G)+(t-1) sum_{v in S} d_G(v) -(2t-1)e(G[S]).

If G has girth greater than 2k, T is ordinary C_(2k)-free. To see this,
project a purported cycle to G minus E(G[S]). A cyclic image contradicts
girth. If the image is a tree, every image edge is traversed at least twice.
A vertex outside S occurs at most once, so has image degree at most one.
As S is independent, the tree image is then a star with at most one
nonsingleton fiber. Its center must occur k times, contradicting t<k.
The restriction is sharp: t copies of the center of K_(1,k) produce
K_(t,k), which contains C_(2k) if t>=k.

For a uniform s-element S (n>=2), the exact expected edge multiplier is

    a(n,s,t)=1+2(t-1)s/n -(2t-1)s(s-1)/(n(n-1)).

Hence a high-girth G satisfies

    a(n,s,t)e(G) <= ex(n+(t-1)s,C_(2k)).

For s=floor(epsilon n), set lambda=1+(t-1)epsilon and
A=1+2(t-1)epsilon-(2t-1)epsilon^2. If f(n)~c n^alpha, alpha<2, then a
sufficiently small fixed positive epsilon gives A>lambda^alpha. This is
a genuine finite-scale coefficient gain, without differentiating f.

Define Q_t^ind(C_(2k)) using proper independent-set partitions of the cycle
with block sizes at most t, and with NO quotient edge between two
nonsingleton blocks. Every such quotient is cyclic by the tree argument.
For an arbitrary C_(2k)-free G, take a maximal edge-disjoint packing of
these quotients, with union D and p members. Then |D|<=2k p. After deleting
D, every T_(S,t) is C_(2k)-free: a projected copy is either injective (already
forbidden) or belongs to this quotient family. Thus

    a(n,s,t)(e(G)-|D|) <= f(n+(t-1)s).

For near-global extremizers e(G)=f(n)-o(f(n)), this forces

    |D| >= (delta-o(1))e(G),
    p >= (delta/(2k)-o(1))e(G),
    delta=1-lambda^alpha/A > 0.

This is stronger than the existing arbitrary-proper-quotient packing,
because the new witnesses are cyclic. In particular these extremizers
cannot be made girth>2k by deleting o(e(G)) edges. It is NOT a statement
that a quotient's extremal exponent equals alpha.

For C8 with t=2 the five unmarked quotient graphs are exactly:

* C6 with one pendant edge;
* C3 and C5 sharing one vertex;
* two C4s sharing one vertex;
* C4 with pendant edges at two opposite vertices;
* K_(2,4).

With t=3 there are two more: C4 with two leaves at the same vertex, and
two triangles sharing a vertex with a leaf at that vertex. Parent exact
partition enumeration confirms 26 admissible partitions/five isomorphism
classes for t=2, and 42/seven for t=3.

For bipartite hosts, forbidding C8 and the four bipartite members of the
t=2 list gives an extremal function within 3n of the bipartite girth>8
extremal function. Peel degree-at-most-three vertices. In the remaining
minimum-degree-four graph, a C4 has two distinct external leaves at opposite
vertices, giving the listed pendant quotient; a C6 has an external leaf.
Thus the remainder has no C4, C6 or C8. The other inequality is immediate.
This reduces a finite family to the still-undetermined high-girth problem,
not to a known rational exponent.

The same packing idea applies to any H containing C_(2 ell) with ell>=3:
choose t<ell and use the analogous quotient family. A tree image would
restrict to the impossible tree image of that cycle. The denominator 2k
in the packing bound becomes e(H).

### 6.1 Why a high-girth reset loses the gain

In any C4-free subgraph of K_(t,d), the edge count is at most d+binom(t,2):
each pair of left vertices has at most one common neighbor and
j-1<=binom(j,2) for every positive right degree j. Consequently any
C4-free J subset T_(S,t)(G) satisfies

    e(J) <= e(G)-e(G[S])+binom(t,2)|S|.

For t=2, e(J)<=e(G)+|S|, whereas the vertex count increased by |S|.
Repeated full-vertex resets therefore have a nonincreasing e-v invariant,
and cannot retain any superlinear leading gain at an expanding scale.
Allowing further vertex deletions is handled by the cycle-space dimension
beta=e-v+number_of_components: folding a twin pair with at most one common
neighbor cannot decrease beta. Other twin fibers have no edges to it,
so later folds preserve this condition. The folded graph is a subgraph
of G, giving beta(J)<=beta(G).

For comparison, the source-audited Kuhn--Osthus theorem in
`/corpus/src/1708.05454/making_bipartite-3.tex` says a bipartite C_(2k)-free
graph has a C4-free subgraph with at least 1/(k-1) of its edges; this
constant is sharp, not an asymptotically lossless reset. The general
constant-fraction extraction of girth>2k remains posed as a problem in
`/corpus/src/1306.5167/FureSimSurvE_arXiv_v2_.tex`.

### 6.2 Legal next batches can themselves saturate

Let F=(A,B) be bipartite of girth>2k with d_F(a)>=k-1 for every a in A.
Put r=k-1, and let U be the r-fold independent blowup of A only. It is
C_(2k)-free and is reachable by legal successive two-twin steps.
For EVERY S for which T_(S,2)(U) remains C_(2k)-free,

    e(T_(S,2)(U)) <= e(U)+r|S|.

Here is the exact argument. In each a-fiber let s_a be the number selected,
u_a=r-s_a, and let T=S intersect B. Split d_F(a)=d_0(a)+d_1(a) according
to neighbors outside/inside T. The edge gain is

    sum_a s_a d_0(a) + sum_a (r-2s_a)d_1(a).

If s_a>0 and d_0(a)>=k, at least k resulting a-clones have k common
unchanged neighbors, yielding K_(k,k). Therefore the first sum is at most
r sum s_a. At a selected b in T, two positive terms r-2s_a would give
two neighboring groups with u_a+u_c>=k unselected clones. Choose positive
p<=u_a and q<=u_c with p+q=k. Using p-1 and q-1 additional neighbors,
form paths of lengths 2p and 2q between b's two new twins. The two
neighbor sets are disjoint because F is C4-free. The resulting injective
C_(2k) is forbidden. Thus at most one positive term contributes at b,
and it is at most r. This bounds the second sum by r|T|.

For a next t-twin step, 2<=t<k, the same counting gives

    gain <= r(t-1)|S intersect (A x [r])| + r(t-1)^2 |S intersect B|.

If t positive groups surrounded a selected b, their unselected capacities
would total at least k; paths around its t new twins would form C_(2k).
Again the gain is only linear in the number of added vertices.

For C8, a D-regular seed with equal parts of size M gives a legal one-sided
triple blowup U with v=4M, e=3MD and degrees D or 3D. Its min degree is
(4/3)e/v, compatible numerically with the core minimum-degree requirement
for alpha<4/3. Every legal next two-twin batch gains at most 3|S|, which
is o(e(U)) for a fixed positive vertex fraction when D grows. This is
not a claim that U is globally extremal or that suitable seeds exist at
every exponent in the C8 gap. It blocks automatic iterability from the
stated numerical regularity conditions alone.

A smallest failure of cyclic-only descent is

    K_(1,4) -> K_(2,4) -> K_(4,4).

The final C8 projects to a cyclic quotient at the middle step but to a
tree at the original step: composed fiber sizes have increased. A finite
sequence of strict coefficient comparisons therefore supplies neither a
strict exponent gap nor a rationality-producing equality.

All arguments in this section were checked independently by the parent.
`/tmp/SelectiveDuplicationParentCheck.py` and its `.log` verify the exact
C8 quotient classifications, 1572 tree-duplication/averaging cases,
the sharp star and two-round failures, all 109 legal next-batch cases
on K_(3,4), and the exact C4-free reset maxima in K_(2,4) and K_(3,4).
This section has not been formalized in Lean and does not settle Spec.
