# Exact distance-support compression: a rigidity theorem and actual planar obstructions

## Scope

These results do not establish the universal subset contraction, nor disprove it. They give (1) a finite endpoint-consistency lemma, (2) a classification of all planar equal-distance-preserving models of sufficiently large number-field coefficient boxes, and (3) sparse actual point sets with few distances but no ratio-controlled macroscopic rich motion. No claim of historical priority is made.

Write D(P) for the number of positive Euclidean distances. A map f on P is **distance-class preserving** if

    |a-b|=|c-d| => |f(a)-f(b)|=|f(c)-f(d)|.

This is weaker than preserving actual lengths, and even permits different source classes to merge. Equivalently, there is one function psi on the source squared-distance support such that |f(a)-f(b)|^2=psi(|a-b|^2) for every pair. The result concerns this endpoint-consistent notion, not mere global set inclusion of distance supports with arbitrary reassignment of distances to edges. A Freiman homomorphism means a+b=c+d implies f(a)+f(b)=f(c)+f(d).

## 1. Universal endpoint-consistency lemma: grid thickening forces affine layer maps

Let G_l={0,...,l}+i{0,...,l}, l>=2, A any finite subset of C, and P=A+G_l. Let f:P->C be injective and distance-class preserving. Then there is one nonzero real-linear similarity T and a Freiman homomorphism b:A->C such that

    f(a+u)=b(a)+T(u)  (a in A, u in G_l).

Representations a+u need not be unique; the displayed formula is consistent wherever they overlap.

### Proof

Each elementary square in a translate of G_l has four equal sides and two equal diagonals after applying f. Its four images are distinct. Four distinct planar points with these equalities form a square: the two opposite vertices are the two intersections of equal-radius circles about the other opposite vertices, so the diagonals bisect at right angles; equal diagonals make the rhombus a square. Adjacent squares cannot fold onto the same side of their common edge, since that would identify distinct vertices. Consequently

    f(a+u)=T_a u+b_a,

where T_a is a nonzero similarity. All T_a have the same scale because all unit edges belong to one distance class.

Fix a,b and a coordinate vector e_j. For u,v in G_l intersect (G_l-e_j), the source differences are identical before and after translating both endpoints by e_j. Set

    w=T_a u-T_b v+b_a-b_b,
    h=(T_a-T_b)e_j.

Distance-class preservation gives |w+h|^2=|w|^2. Hold v fixed and vary u by either coordinate vector; these variations are available because l>=2. Subtraction gives

    (T_a e_k) dot h=0  (k=1,2).

Thus h=0, since T_a is invertible. Both j give T_a=T_b=T.

If a-c=d-b in A, compare the equal source differences

    (a+u)-(c+v)=(d+u)-(b+v)

for u-v=0,1,i. The corresponding image norm equalities, polarized against T(1),T(i), imply b_a-b_c=b_d-b_b. Therefore a->b_a is a Freiman homomorphism. QED.

## 2. Number-field boxes have no other planar distance-class models

Let K be a real-embedded number field, with Q-basis e_1=1,e_2,...,e_m, chosen as the power basis of an integral primitive element. Define

    B_M = {sum_j a_j e_j + i sum_j b_j e_j : a_j,b_j integers, |a_j|,|b_j|<=M}.

For all sufficiently large M (depending only on the basis), every injective distance-class-preserving map f:B_M->C has the form

    f(x+iy)=b+T(sigma(x)+i sigma(y)),

where sigma:K->R is a real field embedding and T is a nonzero real-linear similarity.

In particular, the map cannot merge any two distance classes, cannot lower rational/Freiman rank, and for every S subset B_M,

    D(f(S))=D(S).

If K has exactly one real embedding, f is an ordinary similarity of the original point set.

### Reduction to a Q-linear map

Separate the coefficients of 1 and i from the other 2m-2 coefficients. B_M is a grid thickening of a full (2m-2)-dimensional integer coefficient box. The preceding lemma gives one common similarity on every 1,i grid layer and a Freiman map on the layer box. A Freiman map on a full integer box is affine: its discrete increment in a coordinate direction is independent of the basepoint, by the parallelogram relation. Hence

    f(z)=b+F(z),

with F:K+iK->R^2 Q-linear.

### A finite list of actual equal-distance comparisons suffices

Let

    T_0={e_j} union {e_j+e_k : j<k}.

It is enough that the following vectors occur as differences of points in the domain:

    (e_j,e_k), (e_j,-e_k)                 for all j,k;
    (x,0), (0,x)                          for x in T_0;
    (x^2-1,2x), (x^2+1,0)                for x in T_0.

Every displayed pair has equal original norm. The last equality is the Pythagorean identity

    (x^2-1)^2+(2x)^2=(x^2+1)^2.

This list is finite, so it lies in B_M-B_M for M sufficiently large. These are therefore comparisons between actual distances, not imposed formal equalities absent from the set.

Write U(x)=F(x,0), V(y)=F(0,y). The first comparisons give

    U(e_j) dot V(e_k)=0,

and thus the two image subspaces are orthogonal. The second comparisons, using basis vectors and their pairwise sums, identify their Gram forms:

    U(x) dot U(y)=V(x) dot V(y)=A(x,y).

Define the Q-linear functional lambda(t)=A(t,1). The Pythagorean comparisons give

    A(x,x)=A(x^2,1)=lambda(x^2)  (x in T_0).

Polarization on the basis and its pairwise sums gives, for all x,y in K,

    A(x,y)=lambda(xy).

Thus the full Gram form of F is

    H=diag(A,A),  A(x,y)=lambda(xy).                 (* )

It is PSD and has rank at most two. Nonconstancy forces rank(A)=1. Write A(x,y)=c sigma(x)sigma(y), normalized by sigma(1)=1 and c>0. This normalization is possible: if A(1,1)=0, PSD makes A(t,1)=0 for every t, and (*) then makes A=0.

Now

    c sigma(xy)=lambda(xy)=A(x,y)=c sigma(x)sigma(y).

So sigma is a unital Q-linear multiplicative map K->R, hence a real field embedding. Equality of Gram forms gives the asserted similarity T. Conversely every such real-embedding model preserves all distance classes. Injectivity of sigma also proves the reverse implication between distance equalities and the all-subset support identity. QED.

### A stronger linear-algebra statement

For maps into any Euclidean space, the same finite comparisons force (*). Every PSD form A(x,y)=lambda(xy) on a number field is a nonnegative sum of its real-embedding forms:

    lambda(t)=sum_{sigma real} c_sigma sigma(t), c_sigma>=0.

One proof extends to K tensor_Q R = R^{r_1} x C^{r_2}. On a complex factor, a functional alpha Re(z)+beta Im(z) evaluated on z^2 has matrix [[alpha,beta],[beta,-alpha]], which is indefinite unless alpha=beta=0. The real factors have nonnegative coefficients. The total Gram rank in (*) is twice the number of positive coefficients. Planarity therefore selects exactly one real embedding.

## 3. Explicit arbitrarily high-rank low-distance counterexamples

Take odd m>=3 and theta=2^(1/m), K=Q(theta). Eisenstein gives [K:Q]=m and X^m-2 has only one real root, so K has one real embedding. With the basis 1,theta,...,theta^(m-1), every vector in the finite comparison list above has coefficient absolute value at most 5. Indeed, for x=theta^j+theta^k with j!=k, the three exponents 2j,j+k,2k are distinct modulo odd m; reduction by theta^m=2 gives coefficients at most 4 in x^2, and adding or subtracting 1 gives at most 5. The single-basis cases are smaller. Thus M>=5 is sufficient in the preceding theorem.

Consequently every injective distance-class-preserving planar model of B_M is a similarity, although

    |B_M|=(2M+1)^(2m),   D(B_M)=o_m(|B_M|),
    rational/Freiman dimension(B_M)=2m.

Here is a qualitative proof of the distance estimate, included to make the counterexample independent of an unproved inverse assertion.

All squared distances lie in the coefficient box

    sum_{j=0}^{m-1} c_j theta^j,  |c_j|<=C_m M^2,

whose cardinality is O_m(M^(2m)). For any prime p congruent to -1 modulo 4m, the mth-power map on (Z/p^2 Z)^* is bijective: gcd(m,p(p-1))=1. Let t_p be the unique mth root of 2 modulo p^2. Evaluation theta->t_p defines a ring map Z[theta]->Z/p^2 Z.

If z=x^2+y^2 and its evaluated residue is divisible by p, then p=3 modulo 4 forces both evaluated x,y to vanish modulo p. Therefore the evaluated z is actually 0 modulo p^2. The p-1 residues with valuation exactly one are forbidden. The allowed fraction is

    1-1/p+1/p^2.

For any fixed finite collection of these primes, CRT and coefficient-box equidistribution give the product of these allowed fractions, up to o(1). The evaluation maps are jointly surjective because the constant coefficient alone can assume every residue modulo the product of the p^2. The reciprocal sum of primes in the reduced class -1 modulo 4m diverges (the classical prime-in-progressions theorem). The product therefore tends to zero. First taking M->infinity for a fixed collection, then enlarging the collection, proves D(B_M)=o_m(M^(2m)).

This is an actual counterexample to any proposed dichotomy saying that every low-D configuration admits a non-similarity, endpoint-consistent distance-class-preserving planar model. It is not a counterexample to taking an actual subset of B_M, or to a different notion of compression that may split old distance classes while controlling only the global support.

## 4. Thinning: exact Freiman rigidity survives, while all nonidentity motions become sparse

Fix r and let X_L={0,...,L-1}^r, N=L^r. Retain each point with probability delta. Suppose delta^3 N/log N -> infinity.

With probability tending to one, every Freiman homomorphism on the retained set, into any abelian group, is the restriction of an affine homomorphism of Z^r. Also its difference set contains an integer box of side comparable to L.

### Proof

Choose H=floor(L/10). For every h in [-H,H]^r and every coordinate e_j, demand a translate of {0,h,h+e_j} in the sample. There are O_r(N) demands. Each pattern has at least c_r N valid translations and a greedy selection of at least c_r N/9 pairwise disjoint copies. Its failure probability is at most exp(-c_r delta^3 N). A union bound proves all demands simultaneously.

For a Freiman map f, the increment d(h)=f(p+h)-f(p) is independent of the realizing pair: compare (p+h)+q=p+(q+h). A realized triple gives d(h+e_j)=d(h)+d(e_j). Hence d(h)=sum h_j d(e_j) throughout the small box. Partition X_L into a bounded number (depending on r) of cells with side less than H/2. With high probability every cell is occupied, so the graph joining sample points at l_infinity distance <=H is connected. The affine formula propagates to every sampled point. The same event supplies all small differences and makes the Freiman dimension exactly r. QED.

Apply this in coefficient coordinates to B_M for the one-real-embedding fields in Section 3. Once M is large, the finite norm comparison list is in the sampled difference set. Therefore every nonconstant distance-class-preserving Freiman map on the sample is still a similarity. The Freiman qualification in this thinned assertion is essential to the proof; no assertion is made here about arbitrary non-Freiman maps on the sample.

Let epsilon_M=D(B_M)/|B_M| ->0, N=|B_M|, and choose

    delta_M=max(sqrt(epsilon_M), (log N)^(-1/4)).

Then delta_M->0, and with high probability, for n=|P|,

    n=(1+o(1))delta_M N,
    D(P)/n <= (1+o(1))epsilon_M/delta_M ->0.

The additive doubling is unbounded, since |P-P|>=c_m N while n~delta_M N. Nevertheless its Freiman dimension remains exactly 2m and all its nonconstant norm-compatible Freiman models are similarities.

### Uniform rich-motion bound

For these same samples,

    max_{g != id, g a planar isometry} |P intersect gP|
        <= sqrt(N)+12 delta_M^2 N                 (with high probability).

In particular the maximum divided by n tends to zero.

Proof: every line meets the ambient product set B_M=A_M+iA_M in at most |A_M|=sqrt(N) points. Thus a nonidentity isometry has at most sqrt(N) fixed ambient points. If its overlap has at least two points, it belongs to a list of at most 2N^4 isometries, determined by two ordered source points, two ordered target points and the orientation choice.

For a fixed motion remove fixed points and form the undirected graph with edges {x,gx} lying in the ambient set. The graph has maximum degree two and is a union of three matchings. In each matching the retained-edge indicators are independent Bernoulli(delta_M^2). A Chernoff bound shows that each matching contributes at most 2 delta_M^2 N edges except with probability exp(-c delta_M^2 N). Each undirected edge contributes at most two directed matches. Union-bounding over the finite motion list proves the displayed estimate. Our choice of delta_M makes all error terms negligible.

### Stronger ratio-only obstruction already in Z^2

For r=2, the difference-box property and the Landau-Ramanujan count give, uniformly for the above high-probability samples,

    D(P) asymp N/sqrt(log N),
    lambda:=n/D(P) asymp delta sqrt(log N),
    max_{g != id}|P intersect gP|/n << delta

provided delta^3 N >> log N and delta^2 sqrt(N)->infinity. Hence for every prescribed nondecreasing F:[1,infinity)->[1,infinity), there is a sequence with lambda->infinity but

    F(lambda) max_{g != id}|P intersect gP|/n ->0.

Indeed take delta=t/sqrt(log N), let t->infinity, and choose N so large relative to t and F(Ct) that delta F(Ct)->0. Thus no positive macroscopic rich-motion lower bound depending only on n/D can hold. These are actual endpoint-consistent Euclidean motions, not relaxed edge-correspondence rows.

## 5. What is left open

The theorem does not rule out an adaptive density increment that passes to an actual subset first, or compressions that split old distance classes while controlling only the global support. On thinned inputs, the proved rigidity statement applies only to Freiman maps. It does not assert that the rich-motion overlap subsets all fail the potential contraction. The required universal statement

    Phi(P) <= Phi(Q)+C,   2<=|Q|<=|P|/2,   Phi(S)=(|S|/D(S))^2

is still neither proved nor disproved here.

What is proved is that endpoint-consistent distance-class model changes have no freedom beyond similarity on explicit arbitrarily high-rank low-distance boxes, and that even after sparsifying, neither norm-compatible Freiman deformation nor a ratio-only macroscopic-motion inverse principle is available.

## Verification

`verify_norm_support_compression_rigidity.py` constructs the finite comparison equations exactly for theta^m=2. For m=1,3,5,7 it checks every asserted norm identity in the quotient ring and verifies that their linear Gram constraints have nullity exactly m, with solution space diag(lambda(e_j e_k),lambda(e_j e_k)). The largest comparison coefficient is 5 for odd m>=3. These checks validate the finite gadget; the proofs above establish the statements for arbitrary degree and asymptotic sampling.
