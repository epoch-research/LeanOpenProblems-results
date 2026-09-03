# Independent density, counting, and injectivity investigation

## Scope and outcome

This investigation does **not** prove or disprove the existence of an absolute constant C with R(Q_n) <= C 2^n. Nor does it establish a counterexample to the corresponding half-density embedding statement for every constant C.

It does establish several precise positive lemmas and obstructions to proposed proofs. In particular, complete multipartite graphs **do not** disprove the uniform half-density statement: their asymptotically sharp density constant is 1 + 1/sqrt(2). The red-blue problem is easier in this class, with exact threshold 3*2^(n-1)-1. A robust version tolerates a bounded number of color errors per vertex.

A further collision obstruction is proved below: identifying only O_k(log n) far-apart pairs of vertices of Q_n can destroy **every** copy of Q_(n-k), for any fixed k. Only three identifications suffice to destroy Q_(n-1), for n >= 15. These are sparse host graphs, not counterexamples to the density or Ramsey conjectures.

No Lean theorem or axiom from Spec.lean was used. Spec.lean was not modified; its SHA-256 is `9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b`. The results here have paper proofs, not new Lean formalizations.

Throughout, n >= 1, h = 2^n, and m = h/2. Containment always means an ordinary injective graph homomorphism, not induced containment. For a graph G on N vertices, distinguish the usual density rho = e(G)/binom(N,2) from the homomorphism-normalized density p = 2e(G)/N^2 = rho(1-1/N).

## 1. Complete multipartite graphs: exact criterion

**Partition lemma.** Suppose positive integers a_1,...,a_t sum to N, where N >= 3m-2. There is a union of parts of size between m and N-m if and only if max a_i <= N-m.

Proof. Necessity is immediate if a part exceeds N-m: a union either includes that part or lies in its complement, whose size is less than m. Conversely, if some part has size at least m, take it. Otherwise every part has size at most m-1. Add parts until their sum first reaches m. The sum is at most 2m-2 <= N-m.

**Multipartite cube criterion.** If G is complete multipartite, with part sizes a_i and N >= 3m-2, then

    Q_n is contained in G  iff  max a_i <= N-m.

For sufficiency, the partition lemma produces two disjoint unions of parts, each of size at least m. All cross edges are present, giving K_(m,m), which contains Q_n. For necessity, if a part has size at least N-m+1, its complement is a vertex cover of G of size at most m-1. But Q_n has a perfect matching of size m, so any vertex cover of a copy needs at least m vertices.

Consequently, the exact maximum number of edges of a Q_n-free complete multipartite graph in this range is

    binom(N,2) - binom(N-m+1,2).

Equality is attained by one independent part of size N-m+1 and m-1 singleton parts. Equivalently, take a clique of size m-1 joined to an independent set of size N-m+1. The small clique is a vertex cover, so this construction is cube-free for every N, not just in the range of the criterion.

For N/h -> C >= 1, the density of this example tends to

    1 - (1 - 1/(2C))^2 = 1/C - 1/(4C^2).

This exceeds 1/2 precisely when C < 1 + 1/sqrt(2), in the relevant C >= 1 range. Thus all constants below approximately 1.707 are excluded for the density formulation, but this gives no obstruction to larger constants.

Conversely, if N >= (2+sqrt(2))*m = (1+1/sqrt(2))*h, every complete multipartite graph of density at least 1/2 contains Q_n. Indeed, a cube-free one would have a part of size a >= N-m+1. Writing b=N-m, we have b >= N/sqrt(2), hence

    a(a-1) >= b(b+1) > N(N-1)/2,

contradicting density at least 1/2. Integer N is handled by rounding the displayed threshold upward. In particular, C=2 more than suffices in this class.

## 2. The red-blue dichotomy helps: an exact and robust result

Consider colorings arising from a partition: edges inside each part are blue and all edges between parts are red.

**Exact restricted Ramsey threshold.** Every such coloring on 3m-1 vertices has a monochromatic Q_n, and 3m-2 vertices do not suffice.

Proof of the upper bound. If some part has at least 2m vertices, it contains a blue clique of size h, hence a blue Q_n. Otherwise max a_i <= 2m-1 = N-m. The multipartite criterion gives a red K_(m,m).

For the lower bound, take one part of size 2m-1 and m-1 singleton parts. The red graph has a vertex cover of size m-1. The blue graph consists of a clique on h-1 vertices and isolated vertices. Neither contains Q_n. For n >= 2, the red density in this example is already at least 1/2: the exact comparison reduces to (m-1)(m-2) >= 0. This also gives the general lower bound R(Q_n) >= 3m-1.

The denser multipartite obstructions with N around 1.6h do not refute Ramsey: their large independent red part has more than h vertices and is a blue clique.

**Robust partition-coloring lemma.** Suppose a coloring of K_N differs from a partition coloring in at most D incident edges at every vertex. If

    N >= 3(m+nD)-1,

then it contains a monochromatic Q_n.

Here D is an integer, and an incorrect edge means a red edge inside a part or a blue edge between different parts.

Proof. Set r=m+nD. If a part has at least h+nD vertices, embed a blue Q_n greedily in it. At each step at most h-1 vertices are used; each of at most n earlier neighbors forbids at most D additional vertices.

Otherwise every part has size at most h+nD-1 <= 2r-1 <= N-r. Since N >= 3r-1, the partition lemma gives unions A and B of parts, each of size at least r. There are at most D blue edges from any vertex to the opposite union. Embed the two parity classes of Q_n into A and B, respectively, in any order. A step excludes at most m-1 used vertices in its pool and at most nD vertices due to earlier neighbors. Since each pool has size at least m+nD, a candidate remains.

Thus a structural theorem locating a near-partition coloring with D=O(h/n) would be quantitatively useful. Such a structural theorem for arbitrary cube-free two-colorings has **not** been proved here. Random colorings are not themselves close to partition colorings at this error scale.

## 3. Sidorenko: scalar homomorphism counts cannot enforce injectivity

The verified Sidorenko property of hypercubes states

    hom(Q_n,G) >= N^h p^(nm),    p=2e(G)/N^2.

Under usual density rho >= 1/2, p >= (1-1/N)/2; it is important not to drop this finite-N correction silently.

The elementary collision subtraction is

    inj(Q_n,G) >= N^h p^(nm) - binom(h,2) N^(h-1).

This requires N p^(nm) > binom(h,2), nowhere near N=Ch.

There is a stronger logical obstruction to relying only on the numerical homomorphism lower bound. **For every fixed C >= 1 and all sufficiently large n**, let N=ceil(Ch) and

    G = K_(m-1, N-m+1).

This graph contains no Q_n, since it has a vertex cover of size m-1. Nevertheless,

    hom(Q_n,G) = 2 [(m-1)(N-m+1)]^m.

The formula follows because Q_n is connected and bipartite: either parity class may be sent into either host part, independently within each class. For fixed C, the normalized count is exp(-O_C(h)), whereas 2^(-nm) is exp(-Theta(nh)). Therefore

    hom(Q_n,G) >= N^h 2^(-nm)

for all sufficiently large n. This is even stronger than the scalar lower bound supplied by rho >= 1/2. These graphs need not themselves be half-dense when C is large. The point is exact: **the numerical conclusion of Sidorenko alone does not imply an embedding, at any fixed multiplier C**. A successful proof must retain additional information about the host's density or structure.

Even for a host where injective cubes certainly exist, their fraction among homomorphisms need not be bounded below. For G=K_(s,s), where s=Cm >= m,

    Prob[a uniform homomorphism Q_n -> G is injective]
       = ((s)_m/s^m)^2
       <= exp(-m(m-1)/s)
       = exp(-(h-2)/(2C)).

Thus a positive constant fraction of injective homomorphisms is an inappropriate target at linear host size.

Hatami's stronger weakly norming inequality controls subgraph densities, but quotient graphs produced by collisions are not generally subgraphs. For example, identifying opposite-parity nonadjacent vertices can produce triangles. A direct use of subgraph monotonicity gives only

    hom(Q_n-u,G) <= N^(h-1) t(Q_n,G)^(1-2/h),

so the corresponding union bound guarantees injectivity when N p^n > binom(h,2), of order h^3 at p=1/2. This is a bound for this direct argument, not a claimed limitation on every use of graph norms.

## 4. Tensor powers do not make injectivity descend

For the categorical graph product, homomorphisms tensorize:

    hom(H,G tensor G) = hom(H,G)^2.

But injective embeddings into a tensor power do not imply an injective embedding into a factor. Let P_3 have vertices 0-1-2. It does not contain Q_2, but P_3 tensor P_3 has the square

    (0,1), (1,0), (2,1), (1,2), (0,1).

For n >= 2, P_3 raised to tensor power 2(n-1) has a component containing K_(2^(n-1),2^(n-1)), and hence Q_n: use tuples with leaves in the first n-1 coordinates and centers in the rest, or the opposite pattern.

Blowups have the same problem. If G[M] replaces every vertex by M independent twins, then

    inj(H,G[M]) = sum_(f:H->G hom) product_v (M)_(|f^(-1)(v)|).

The leading coefficient records hom(H,G), but the value at M=1 records inj(H,G). Positivity at large M says nothing about positivity at M=1. In fact, any graph with an edge has Q_n in its m-fold blowup.

## 5. A rigorous almost-injective obstruction via far-apart identifications

**Lifting lemma.** Select pairwise Hamming-distance-at-least-5 vertices in Q_n, pair them, and identify the two vertices of each pair. Let G be the resulting simple quotient graph. For every d >= 2, every ordinary copy of Q_d in G lifts to a coordinate d-dimensional subcube of Q_n. In particular,

    Q_d is contained in G
      iff some coordinate d-subcube contains at most one endpoint of each identified pair.

Proof. Quotient edges have unique original preimages. There are no loops, and two different source edges cannot become the same edge: either they would give two selected endpoints a common neighbor, or they would join selected endpoints, contrary to their separation.

Every 4-cycle in G lifts to an original square. Otherwise, while lifting it, at some identified vertex one must jump between the two endpoints of its pair. Between two such jumps, or around the remaining cycle if there is only one jump, there is a cube path of length at most four between distinct selected endpoints. Their separation rules this out.

Now consider a Q_d copy in G. Any two incident copy edges belong to a square, so their unique preimages must meet the same representative of the image vertex. As d >= 2, all incident copy edges choose one consistent representative. These choices lift the entire copy injectively into Q_n.

Finally, every injective graph homomorphism Q_d -> Q_n is coordinate: each square has opposite edges in the same coordinate direction. Propagating across domain squares makes the direction of each domain coordinate constant, and the directions are distinct at a vertex. Therefore the image is an axis-aligned subcube. The claimed equivalence follows.

**Explicit three-collision example.** For n >= 15, divide coordinates into nonempty blocks A,B,C, each of size at least five. Interpret a three-bit string as a vertex constant on these blocks. Identify the pairs

    000 ~ 100,
    001 ~ 011,
    110 ~ 111.

The six selected vertices are pairwise at distance at least five. Every (n-1)-subcube fixes a coordinate. If that coordinate is in A, the second pair lies entirely in the 0-half and the third entirely in the 1-half. If it is in B, use the first and third pairs. If it is in C, use the first and second pairs. Thus every (n-1)-subcube contains a collision pair. By the lifting lemma, the quotient has no Q_(n-1).

So there is a homomorphism from Q_n that is injective except at three pairs, into a graph on h-3 vertices, yet its image contains no Q_(n-1).

**Arbitrary fixed dimension loss.** Fix k >= 1. Choose

    r = ceil(4^k (k+2) log(2n))

independent random pairs of vertices of Q_n. The probability that any two among the 2r endpoints have distance at most four is at most

    binom(2r,2) * [sum_(j=0)^4 binom(n,j)] / 2^n = o(1).

A given codimension-k subcube contains both endpoints of a random pair with probability 4^(-k). Hence the probability that some such subcube contains no full pair is at most

    2^k binom(n,k) exp(-r/4^k) = o(1).

For sufficiently large n both desired events hold simultaneously. Applying the lifting lemma gives a graph on h-O_k(log n) vertices and a homomorphism Q_n -> G with only O_k(log n) collision pairs, but **no Q_(n-k)**.

The general construction can even be kept bipartite: draw all endpoints uniformly from the even parity class. Each codimension-k subcube (with n-k >= 1) still has relative mass 2^(-k) in that class, and the separation bound changes by at most a factor of two. Only vertices in the same parity class are then identified.

These quotients are sparse, with exactly nh/2 edges and maximum degree at most 2n. They do not refute the density or Ramsey conjectures. Indeed, after padding by isolated vertices to N >= h+2n^2, their complements already contain Q_n by the greedy bound N >= h+n*Delta(G). They do refute extracting a cube of only constant smaller dimension from a nearly injective homomorphism by a purely source-combinatorial argument. Additional host density, color information, or a genuine repair operation is indispensable.

## 6. Dependent random choice: identify the excessive requirement

Let a bipartite host have sides A,B of sizes a,b and cross-density p. Sampling t vertices of B with replacement and taking their common neighborhood gives the standard certificate

    |U| >= a p^t - binom(a,n) (r/b)^t,

where every n-subset of U has at least r common neighbors in B. This follows by expectation and deletion of one vertex from every bad n-subset.

Setting r=m and |U|>=m would embed Q_n by placing one parity class in U and greedily placing the other. At a=b=Cm and p=1/2, however, the first term requires t <= log_2 C, while for bounded t the deletion term is enormous. Taking t of order n shrinks the guaranteed U to constant size. This particular certificate cannot yield a uniform multiplier.

More decisively, **for every fixed C and every fixed p_0 in (1/2,1)** there exist graphs on N=ceil(Ch) vertices of density at least 1/2 that have no K_(n,m). Indeed, for G(N,p_0),

    Prob[K_(n,m) is present]
      <= binom(N,n) binom(N,m) p_0^(nm)
      <= N^n (eN/m)^m p_0^(nm)
      -> 0.

The logarithm is O(n^2)+m[O_C(1)+n log p_0], which tends to minus infinity. Meanwhile the edge density exceeds 1/2 with probability tending to one. Consequently, a linear-size half-dense graph need not have even **one** n-set with m common neighbors. An all-large-common-neighborhood DRC lemma is therefore a genuinely false intermediate assertion at this scale, not merely a poorly optimized bound.

This does not say those random graphs are cube-free; it says the proposed large-list sufficient condition is unnecessarily strong.

For comparison, the corpus's Fox-Sudakov density theorem uses the scale N >= 32 Delta rho^(-Delta) v(H), giving 32 n 4^n for the cube at density 1/2. Its improvement from all good tuples to almost all good tuples is important, but its constants are not uniform in dimension at the desired scale.

## 7. Hall's theorem pinpoints the remaining embedding problem

Let E_n and O_n be the parity classes. Given disjoint host sets A,B and an injection f:E_n->A, define

    L_y = B intersect (intersection_(x adjacent to y) N_G(f(x))),  y in O_n.

Then f extends to a Q_n copy with O_n mapped into B **if and only if**

    |union_(y in S) L_y| >= |S|  for every S subset O_n.

This is exactly Hall's theorem. Lists need not have m elements; they can be small but collectively expanding. Distinct cube neighborhoods in the same parity class intersect in zero or two vertices, a useful fact that generic maximum-degree DRC bounds discard.

A failed Hall test for a single f does **not** force a blue cube. If S violates Hall, every b outside the union of its lists has a blue neighbor in f(N(y)) for each y in S. Such blue witnesses may be highly concentrated.

An exact example uses an extended Hamming code. For n=2^k with k >= 1, index coordinates by F_2^k and put

    D = {x of even parity : sum_i x_i i = 0 in F_2^k}.

Then |D|=m/n, and every odd vertex y has exactly one neighbor in D: flip the coordinate indexed by sum_i y_i i.

Take A to contain a labeled copy of E_n plus m/n extra vertices, and take |B|=m. Color only D x B blue and all other edges red. For the canonical injection f:E_n->A, **every L_y is empty**. Yet the entire blue graph has a vertex cover D of size m/n<m, so contains no Q_n. Meanwhile (A minus D) union B is a red clique of size h.

Thus even total failure of this particular one-sided embedding, in a nearly complete red graph, can mean only that the chosen f must be rearranged. It does not supply a blue alternative. A valid dichotomy must analyze a suitably optimized family of injections, or prove a robust reassignment/absorption lemma, rather than treating one failed common-neighborhood test as a blue obstruction.

## 8. Density below one quarter really does fail uniformly

There cannot be an extension claiming linear-size cube embedding for **every** fixed positive density. Fix rho < 1/4 and choose p_0 with rho < p_0 < 1/4. For N=ceil(C2^n),

    E[inj(Q_n,G(N,p_0))]
      <= N^h p_0^(nh/2)
      = [ (C+o(1)) (2 sqrt(p_0))^n ]^h
      -> 0.

With probability tending to one there is no Q_n, while the edge density is at least rho. This works for every fixed C. It does not disprove the statement at density 1/2. Any putative general density or entropy theorem must respect this threshold obstruction.

## 9. What has, and has not, been reduced

A successful route needs to use actual half-density or both colors, not just:

- the Sidorenko scalar lower bound;
- bounded multiplicity, or even o(h) collisions, in a homomorphism;
- injectivity obtained only in a tensor power or a blowup;
- m common neighbors for all relevant n-sets;
- a blue witness supplied by one failed one-sided embedding.

Two quantitatively meaningful directions remain:

1. A structural theorem producing a coloring close enough to a partition coloring for the robust lemma (error budget O(h/n)), together with a genuinely different treatment of the non-structured case.
2. A cube-specific reassignment method obtaining Hall expansion for small candidate lists. It must preserve injectivity and cope with concentrated witnesses such as the Hamming-code example; simply replacing large lists by nonempty lists is not enough.

These are unproved requirements, not claimed solutions or restatements of a known available Ramsey theorem. No family with R(Q_n)/2^n unbounded has been constructed here.

## Corpus evidence

- `/corpus/src/0806.0047/normFinal.tex`, Hatami, *Graph norms and Sidorenko's conjecture*: weakly Holder/weakly norming property of hypercubes, lines 458-466; subgraph norm monotonicity and its proof, lines 575-597. It concerns homomorphisms, not injective embeddings.
- `/corpus/src/0707.4159/0707.4159.tex`, Fox-Sudakov, *Density theorems for bipartite graphs and related Ramsey-type results*: density theorem at lines 140-146, cube bound at lines 170-185, and the DRC mechanism beginning at line 600.
- `/corpus/src/1306.0461/1306.0461.tex`, Fiz Pontiveros et al., *The Ramsey number of the clique and the hypercube*: the introduction explicitly distinguishes the diagonal conjecture from fixed-clique versus cube results. No dimension-uniform theorem solving the diagonal problem is inferred from it.

This is a local-corpus audit, not a claim to certify the latest literature status.

## Verification

Run `python3 Submission/check_cube_density_investigation.py` from the project root. The complete run passed:

- 258,016 integer-partition/bin-packing instances, including the exact multipartite extremal edge counts;
- 208 independent NetworkX **noninduced** graph-copy checks in dimensions 1, 2, 3;
- 1,200 greedy embeddings under randomly generated robust-partition hypotheses;
- extended-Hamming-code incidence checks in dimensions 2, 4, 8, 16;
- the tensor-product square;
- the explicit Q_15 quotient: 32,765 vertices, exactly 245,760 edges, every coordinate half blocked by a pair, and no square mixing the two original stars at any identified vertex;
- far-apart-pair and every-subcube-blocking certificates for codimensions 1, 2, 3 in dimensions 48, 48, 64, respectively;
- numerical homomorphism comparisons and the unchanged Spec.lean hash.

The quotient checks are finite **structural certificates used by the lifting proof**, not brute-force searches over all embeddings of enormous cubes. The asymptotic conclusions rely on the paper proofs above, not on finite experiments.
