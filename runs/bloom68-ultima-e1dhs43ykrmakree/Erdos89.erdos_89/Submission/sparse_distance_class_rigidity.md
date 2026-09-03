# Sparse distance-class rigidity without an additive hypothesis

## Status and the new point

This does **not** prove or disprove the sharp planar Erdős bound
`D(P) >= c |P| / sqrt(log |P|)`.

The result here removes the **Freiman-map hypothesis** from the previously
proved random-thinning rigidity statement. It also proves an exact
infinitesimal-rank theorem. In particular, deleting a proportion tending to
one of a field box need not create either non-similarity distance-class
models or infinitesimal distance-class flexes. The argument is a finite
certificate, valid simultaneously for all maps of the sample. No historical
priority claim is made.

## 1. Statements

Let K=Q(theta) be a number field with a specified embedding in R, theta an
algebraic integer, and m=[K:Q]. Use the power basis
`e_0=1,e_1=theta,...,e_{m-1}=theta^(m-1)`. Put

    B_M = {sum a_j e_j + i sum b_j e_j : |a_j|,|b_j| <= M, a_j,b_j integers},
    N = |B_M| = (2M+1)^(2m).

Retain each point independently with probability delta, obtaining P. A map
f:P->R^2 is **distance-class preserving** if

    |p-q|=|r-s|  implies  |f(p)-f(q)|=|f(r)-f(s)|.          (1)

Different original classes are allowed to merge in this definition.

### Theorem A: global sparse rigidity

There are positive constants c_m,C_m, and a threshold M_0(K), such that for
M>=M_0(K), with probability at least

    1 - C_m N exp(-c_m delta^27 N),

every **injective** map satisfying (1) has the form

    f(x+iy) = b + T(sigma(x)+i sigma(y)),                   (2)

where sigma:K->R is a real field embedding and T is a nonzero real-linear
similarity. In particular, it merges no distance classes and preserves
D(S) for every S subset P.

Thus delta^27 N/log N -> infinity is sufficient for the conclusion with
probability tending to one. If K has only one real embedding, all these
maps are ordinary similarities of the original sample. No additive or
Freiman assumption is made on f.

### Theorem B: exact infinitesimal sparse rigidity

Call a velocity field v:P->R^2 class-preserving to first order if

    (p-q) dot (v(p)-v(q)) = (r-s) dot (v(r)-v(s))           (3)

whenever |p-q|=|r-s|. With probability at least

    1 - C_m N exp(-c_m delta^12 N),

all such fields are

    v(p)=b+alpha p+omega Jp,   J(x,y)=(-y,x).              (4)

Equivalently, if one representative edge is chosen per distance class and
(3) is imposed between it and every other edge in that class, the resulting
matrix in 2|P| velocity variables has rank exactly

    2|P|-4.

There is no integrability assumption on v. Theorem B is a genuine tangent
space assertion, not a deduction of infinitesimal rigidity from global
rigidity. Multiple real embeddings in Theorem A give discrete models, not
additional infinitesimal motions.

## 2. A random finite certificate

We first work in coefficient space Z^r, r>=2, with an injective additive map
Phi:Z^r->R^2 satisfying Phi(e_1)=(1,0), Phi(e_2)=(0,1). For the field box,
r=2m; order the coefficient directions to put 1,i first. Let

    X=[-M,M]^r intersect Z^r,   H=floor(M/10),
    C=[-H,H]^r intersect Z^r,
    G_l={u e_1+v e_2 : 0<=u,v<=l},    l in {1,2}.

For a retained coefficient set S subset X define the anchor set

    A={a : a+G_l subset S}.

Consider the following deterministic certificate:

* (T) For every h in C and j=1,...,r, some a has
  `{a,a+h,a+h+e_j} subset A`.
* (C) The graph on A joining anchors whose difference lies in C is connected.
* (N) For every p in X, some a in A has
  `p-a, p-a-e_1, p-a-e_2 in C`.

### Certificate probability

The certificate holds with probability at least

    1-C_r N exp(-c_r delta^(3(l+1)^2) N).                  (5)

**Proof.** For a fixed demand (h,j), require the translated pattern

    G_l union (h+G_l) union (h+e_j+G_l)

inside S. Its size is at most s=3(l+1)^2 and its coordinate widths are at
most H+3. Consequently at least c_r N translations fit inside X. For any
fixed translate, at most s^2 translation parameters give an overlapping
translate: their difference must belong to the difference set of the
pattern. A greedy choice therefore gives at least c_r N/s^2 disjoint
translates. Their retention events are independent, each with probability
at least delta^s. The failure probability is at most
`exp(-c_r delta^s N)`. There are r|C|=O_r(N) demands.

For (C) and (N), the possible anchor starts form the box

    X^-=[-M,M-l]^2 x [-M,M]^(r-2),

with integer coordinates. Partition each coordinate interval into a bounded
number of balanced intervals of length at most floor(H/3) and at least a
fixed positive multiple of H. For large M this is possible, and there are
O_r(1) product cells, each containing at least c_r N possible starts.
Disjoint-translate selection for G_l shows that a specified cell contains
no anchor with probability at most
`exp(-c_r delta^((l+1)^2) N)`, which is no larger than the bound needed in
(5).

If all cells are occupied, anchors in one cell and in face-adjacent cells
have coefficient differences in C; their graph is connected. For any p in
X, clamp its first two coordinates into X^- and use an anchor in that cell.
The clamping changes coordinates by at most l. Thus the three differences
in (N) have sup norm at most floor(H/3)+l+1<=H, for large M. A union bound
proves (5). QED.

Notice that this uses many small witnesses, not a macroscopic overlap under
any one motion. The constants may depend on the fixed rank r.

## 3. Global maps: patches force affinity

Use l=2 and assume the certificate.

### Patch lemma

For an injective distance-class-preserving f on Phi(A+G_2), there is a single
nonzero similarity T and a Freiman homomorphism b:A->R^2 such that

    f(Phi(a+u))=b(a)+T(u),       a in A, u in G_2.         (6)

Here physical and coefficient coordinates agree on the first two axes.

**Proof.** An elementary source square has four equal sides and equal
diagonals. Its four distinct images have the same relations and hence form
a square: the two vertices on one diagonal are the two equal-radius circle
intersections about the other diagonal, and equal diagonals make the
resulting rhombus a square. Adjacent elementary squares cannot fold onto
the same side of their common edge, since that would identify distinct
vertices. Hence the image of each 3x3 patch is
`b(a)+T_a u`, with T_a a nonzero similarity. All T_a have the same scale,
since every unit edge is in the same class.

Fix anchors a,b and j in {1,2}. Simultaneously translate both endpoints of
a cross-patch edge by e_j, taking u,v in G_2 with u+e_j,v+e_j in G_2.
The source displacement is unchanged. Write

    w=b(a)-b(b)+T_a u-T_b v,
    h=(T_a-T_b)e_j.

Condition (1) gives `|w+h|^2=|w|^2`. Hold v fixed and vary u by either
coordinate vector; both variations are available in the 3x3 patch. It
follows that `(T_a e_k) dot h=0` for k=1,2. Since T_a is invertible, h=0.
Doing this for j=1,2 gives T_a=T_b=T.

If a-c=d-b among anchors, compare the two source displacements with common
additional offset u-v=0,e_1,e_2. They are equal, so their image squared norms
are equal. Subtracting the equation for offset zero from the other two
shows that b(a)-b(c) and b(d)-b(b) have the same dot products with T(e_1)
and T(e_2). They are equal. This is precisely the Freiman condition. QED.

### Propagating a Freiman map on the anchors

For h in A-A the increment

    d(h)=b(a+h)-b(a)

is independent of the realizing anchor pair: this follows from the Freiman
identity `(a+h)+a'=a+(a'+h)`. Condition (T) gives C subset A-A and

    d(h+e_j)=d(h)+d(e_j)    (h in C).                     (7)

The values outside C occurring on the left are also defined by (T).
Lattice paths inside C, using (7) forward or backward, yield

    d(h)=L(h):=sum h_j d(e_j)     (h in C).

Connectivity (C) implies `b(a)=b_0+L(a)` for every anchor. Condition (T)
with h=0 gives anchor pairs a,a+e_j. For j=1,2, consistency with (6) gives
`L(e_j)=T(e_j)`. Therefore

    f(Phi(s))=b_0+L(s)       (s in A+G_2).                (8)

### Extending from the patches to every sampled point

For p in S use (N) to choose a. For u=0,e_1,e_2 the difference
`h=p-a-u` is in C subset A-A. Its norm is realized by an anchor pair, so
(1) and (8) give

    |f(Phi(p))-(b_0+L(a+u))|^2 = |L(p-a-u)|^2.           (9)

If h=0, the equality is automatic; equivalently p is already on the patch.
The proposed point b_0+L(p) satisfies the same three equations. Their
centers are noncollinear, since L(e_1),L(e_2) are nonzero perpendicular
vectors. Subtracting squared-distance equations proves uniqueness. Thus

    f(Phi(p))=b_0+L(p)       (p in S).                    (10)

This is the missing automatic-affinity step. It did not assume f was
Freiman. Furthermore, all equal norms among coefficient vectors in C are
preserved by L, because C subset A-A.

## 4. The finite norm certificate classifies L

Identify L with a Q-linear map K+iK->R^2. Let

    T_0={e_j} union {e_j+e_k : j<k}.

Use the following finite equal-norm comparisons, where (x,y) denotes x+iy:

    (e_j,e_k)        and (e_j,-e_k),                 all j,k;
    (x,0)            and (0,x),                      x in T_0;
    (x^2-1,2x)       and (x^2+1,0),                  x in T_0.       (11)

They are valid by the sign, axis-swap, and Pythagorean identities. Since
theta is integral, every displayed coordinate belongs to Z[theta]. The
list is finite, so for M>=M_0(K) all its coefficient vectors lie in C and
occur as actual differences of sampled anchor pairs.

Write U(x)=L(x,0), V(y)=L(0,y). The first comparisons give U(K) perpendicular
to V(K). The second, applied to a basis and its pairwise sums, give identical
Gram forms

    U(x) dot U(y)=V(x) dot V(y)=A(x,y).

U(1),V(1) are the nonzero orthogonal columns of T, so each of U(K),V(K) is
one-dimensional and A has rank one. Set lambda(t)=A(t,1). The last
comparisons give

    A(x,x)=A(x^2,1)=lambda(x^2)       (x in T_0).

Polarizing on the basis and its pairwise sums proves

    A(x,y)=lambda(xy)                 (x,y in K).         (12)

Let c=A(1,1)>0 and sigma(x)=A(x,1)/c. Rank one gives
`A(x,y)=c sigma(x)sigma(y)`. Equation (12) now implies

    sigma(xy)=sigma(x)sigma(y),   sigma(1)=1.

Thus sigma is a real field embedding. It follows that
`L(x,y)=T(sigma(x),sigma(y))`, proving (2). Conversely every such map
satisfies (1) and is injective. Its squared distances are c sigma of the
original squared distances; injectivity of sigma prevents class mergers.
Combining this deterministic proof with (5), l=2, proves Theorem A.

## 5. Infinitesimal rigidity: a finite derivation calculation

Use l=1. The smaller patch is sufficient because first-order gluing has no
reflection/folding branch.

### Infinitesimal patch lemma and propagation

On an elementary unit square, (3) for the four sides and the two diagonals
forces

    v(Phi(a+u))=b(a)+(alpha I+omega_a J)u.                (13)

For completeness, after subtracting v(a), let the velocity increments at
e_1 and e_2 be `(alpha,beta)` and `(gamma,alpha)`; equality of the four side
derivatives makes the increment at e_1+e_2 equal to
`(alpha+gamma,alpha+beta)`. Equality of the diagonal derivatives gives
`beta+gamma=0`. This is (13). All patches have the same alpha because all
unit edges belong to the same distance class.

For two patches a,b, simultaneously shift both endpoints of a cross edge
by e_1. The displacement is unchanged; (3) therefore gives

    Phi(a-b+u-v) dot ((omega_a-omega_b)J e_1)=0.

Take v=0 and u=0,e_2; these choices and their e_1-shifts lie in G_1.
Subtracting shows omega_a=omega_b. Thus (13) has one common matrix.
For an additive relation among anchors, compare equal displacements with
offsets 0,e_1,e_2, just as above but in (3). Subtraction again proves that
b is Freiman. The increment and connectivity argument of Section 3 gives

    v(Phi(s))=b_0+L(s)       (s in A+G_1).

For p in S and a supplied by (N), compare the derivative for p,a+u with an
anchor pair having the same coefficient difference, u=0,e_1,e_2. This gives

    Phi(p-a-u) dot (v(Phi(p))-b_0-L(p))=0.

Subtracting the equation for u=0 from those for u=e_1,e_2 makes both
coordinates of the parenthesized vector zero. Hence v=b_0+L on the entire
sample. This argument uses noncollinearity of the original anchors, not
invertibility of L.

### The norm comparisons force a derivation

Write

    L(x,0)=(a(x),b(x)),      L(0,y)=(c(y),d(y)),

with Q-linear real-valued functions a,b,c,d on K. Applying (3) to the first
comparisons in (11) gives

    x c(y)+y b(x)=0    (x,y in K).

Consequently `b(x)=omega x` and `c(y)=-omega y`. The axis comparisons on the
basis give a=d. Write alpha=a(1). The Pythagorean comparisons give, for
x in T_0,

    (x^2-1)(a(x^2)-alpha)+4x a(x)
       = (x^2+1)(a(x^2)+alpha),

or equivalently

    a(x^2)=2x a(x)-alpha x^2.

Set partial(x)=a(x)-alpha x. Then

    partial(x^2)=2x partial(x)       (x in T_0).

Polarizing on the basis and its pairwise sums, then extending Q-bilinearly,
yields the full Leibniz rule

    partial(xy)=x partial(y)+y partial(x)    (x,y in K).

So partial:K->R is a derivation with respect to the specified embedding.
It is zero: for the separable minimal polynomial F of any x in K,
`0=partial(F(x))=F'(x)partial(x)`, and F'(x)!=0. Therefore

    L(x,y)=(alpha x-omega y,omega x+alpha y),

as required in (4). Translations, dilation, and rotation plainly satisfy
(3), and they are four linearly independent fields on a set containing a
square. The rank assertion follows. Formula (5) with l=1 proves Theorem B.

This proves infinitesimal rigidity directly and rules out spurious
first-order flexes; global rigidity alone would not have justified it.

## 6. Actual low-distance, vanishing-density examples with both rigidities

Take odd m and theta=2^(1/m). Eisenstein gives degree m, and X^m-2 has one
real root, so K has exactly one real embedding. The coefficient bound in
(11) is at most 5 for odd m>=3: for x=theta^j+theta^k the exponents
2j,j+k,2k are distinct modulo m, reduction by theta^m=2 gives coefficients
at most 4 in x^2, and adding or subtracting 1 increases this to at most 5.

For these boxes the qualitative bound

    epsilon_M:=D(B_M)/N -> 0                              (14)

uses only a norm-sieve **upper** bound, not norm saturation. Here is a
proof to specify the analytic input. Squared norms lie in a coefficient
box `|c_j|<=C_m M^2`, of cardinality O_m(N). For a prime
`p=-1 mod 4m`, excluding the finitely many p dividing 2m, the mth-power map
on `(Z/p^2 Z)^*` is bijective, since gcd(m,p(p-1))=1. Let t_p^m=2 mod p^2.
Evaluation theta->t_p is a ring homomorphism. Since p=3 mod 4, if an
evaluated sum of two squares is divisible by p, it is actually divisible
by p^2. Thus the p-1 residues of valuation exactly one are forbidden; the
allowed fraction is `1-1/p+1/p^2`.

For any fixed finite collection of these primes, CRT and equidistribution
of a growing integer coefficient box give the product of these allowed
fractions, up to o(1). Surjectivity is already supplied by the constant
coefficient. The classical divergence of the reciprocal sum of primes in
a reduced residue class makes this product tend to zero. First take
M->infinity for fixed primes, then enlarge the collection. This proves
(14). No lower count of represented norms, no bounded-field uniform
asymptotic, and no joint field/height limit are being asserted.

Choose

    delta_M=max(sqrt(epsilon_M), (log N)^(-1/4)).

Then delta_M->0 and both probabilistic rigidity thresholds hold. With
probability tending to one, writing n=|P|,

    n=(1+o(1))delta_M N,
    D(P)/n <= (1+o(1))epsilon_M/delta_M ->0,
    |P-P|/n >= c_m/delta_M ->infinity.                    (15)

The last inequality follows because the certificate gives a full
coefficient difference cube of size at least c_m N. Nevertheless every
injective distance-class-preserving planar map of P is a similarity and
the colored infinitesimal rank is exactly 2n-4. This is the extension beyond
the earlier thinned statement, which required the map to be Freiman.

These samples can simultaneously have no macroscopic nonidentity motion.
Indeed every line meets B_M in at most sqrt(N) points. A nonidentity
isometry fixes at most a line, hence at most sqrt(N) ambient points. An
isometry with at least two overlapping ambient points belongs to a list of
at most 2N^4 motions, determined by two ordered source points, two ordered
target points, and an orientation choice. After removing its fixed points,
the unordered edges {x,gx} form a maximum-degree-two graph, the union of
three matchings. Within each matching the retained-edge indicators are
independent Bernoulli(delta_M^2). Chernoff and a union bound give

    max_(g != id) |P intersect gP|
       <= sqrt(N)+12 delta_M^2 N = o(n).                 (16)

Motions with less than two ambient matches already satisfy the bound. This
proves that the rigidity certificate is not secretly imposing the excluded
macroscopic-motion condition. Each odd m is fixed in its asymptotic; m can
then be made arbitrarily large, or allowed to increase along a diagonal
with M chosen sufficiently large at each stage. No rank-uniform constants
are claimed.

## 7. What this does and does not settle

* The new finite theorem removes the additive-map assumption for sparse
  field boxes, and separately identifies the entire infinitesimal kernel.
* Thus arbitrary class-preserving model changes do not become available
  merely by thinning a rigid low-distance box. The point set may have
  unbounded doubling and vanishing overlap under every nonidentity motion.
* There is still no extraction of this certificate, or of any quantitatively
  controlled arithmetic model, from **arbitrary** D=o(n) point sets.
* Full infinitesimal rank does not supply bounded field degree, bounded
  height, or a uniform norm-sieve saturation theorem. The joint field/height
  issue remains untouched.

Accordingly the sharp Erdős inequality remains unresolved here. This is a
proved robustness and derivation-rank result, not a claimed proof of the
arithmetic/generic dichotomy or of the target bound.

## 8. Verification

`verify_sparse_distance_class_rigidity.py` performs the following checks:

1. Exact arithmetic in Q(2^(1/m)), m=1,3,5,7, verifies all finite identities
   (11). The infinitesimal matrices have ranks 2,10,18,26 in 4,12,20,28
   variables, respectively, leaving exactly dilation and rotation. The
   fictitious derivative treating theta as transcendental fails the
   constraints for m>1.
2. For a square, a 3x3 patch, and an actual random 78-point subset of an
   11x11 integer grid, the full class-equation matrices have exact ranks
   4,14,152. A nonzero minor modulo a prime proves the characteristic-zero
   lower rank, and the four explicit exact kernel vectors prove equality.
3. Literal subset tests on two random samples of a 201x201 grid verify all
   882 triple demands, short-step connectivity of the anchors, and an
   anchor net for every ambient point. The l=1 test retains 26,148 points
   and has 6,929 anchors; the l=2 test retains 31,504 points and has 4,237
   anchors. These are finite checks, not substitutes for the probability
   proof.

The verification output is in `sparse_distance_class_rigidity_verification.txt`.
`Spec.lean` was not modified; its SHA-256 before and after is
`c2fbaabe5ad8088f856ca97625747c7a01754f3c149dd6a493454e776de290db`.
No Lean formalization was attempted.
