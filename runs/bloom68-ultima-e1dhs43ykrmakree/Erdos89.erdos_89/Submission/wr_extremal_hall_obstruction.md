# Extremal-palette Hall gate: a quantitative obstruction, not a WR proof

## Outcome

**WR is not proved or disproved here.** The sharp planar distinct-distances
bound remains open in this investigation. No Lean files were edited.

The new obstruction is stronger than the earlier skinny-rectangle example:
there are explicit sets that are **globally cardinality-maximal for their
actual palettes**, have `D=o(n)`, and have a fixed positive fraction of their
normalized witness mass on axes with both `m -> infinity` and
`w/m^2 -> infinity`. Nevertheless every witness-reflection Hall graph has an
explicit perfect matching obtained by pairing equal residues modulo a prime.
This is not an appeal to maximality to assert that a matching exists.

Moreover, the modular matching certificate survives **every choice of a
maximum-cardinality, maximum-R configuration for the same allowed palette**,
using that configuration's actual palette. For these configurations **every
translation and every reflection** has an explicit Hall certificate.
Irrational translations have forbidden minimum degree at least `n-sqrt(n)`;
non-rational reflections have minimum degree at least `t-sqrt(n)` on parts
of size t in {n-1,n}. Neither case has proper nonempty tight Hall sets.

The secondary R condition does not give a local remedy: under a reflected
exchange, the contribution of the generating axis is exactly unchanged as
soon as it is capped. Any useful R improvement must come from other axes.
The explicit sheared configurations are not proved to be R-maximizers or
F(s)-maximizers. That remaining distinction is stated precisely in section 7.

## 1. Setup and the exact effect of a reflected exchange

Use the actual positive squared-distance palette S, with D=|S|. Write

    Bnorm = [n(n-1)-sum_p d_p]/D,
    R(P)  = sum_l m_l min(w_l,m_l(m_l-1)).

Here w_l is ordered: it counts the points a in P with r_l(a) in P and
r_l(a)!=a. The normalized mass h_l is the sum of 1/(D k_{p,s}) over
ordered isosceles witnesses on l, with full pinned fibers. Thus

    sum_l h_l=Bnorm,       0 <= h_l <= m_l.

The two-center bound makes F(s) finite and attained (for positive integer s).
For fixed n, `0<=R<=n^2(n-1)`, because `sum_l w_l=n(n-1)` and m_l<=n.
Consequently the integer R maximum is also attained; no compactness of the
configuration space is needed. An F(s)-maximizer is globally maximal for its
actual palette, and its tight palette-preserving exchanges remain
F(s)-maximizers.

For an isometry g put

    C=P intersect gP,   A=P\gP,   Bset=gP\P.

A subset Y of Bset can replace its forbidden neighborhood N(Y) in A:

    P_Y=(P\N(Y)) union Y.

Indeed C and Y both lie in gP, Y is internally compatible, and by definition
there are no forbidden pairs between Y and A\N(Y). Thus maximum cardinality
implies Hall's inequalities. This argument does not require the palette to
remain fully realized after the exchange, only that no new distance is added.

For a reflection r=r_l there is more exact information:

    |C|=m_l+w_l,      |A|=|Bset|=n-m_l-w_l,      Bset=r(A).       (1.1)

All the witnesses on l lie in C; the forbidden graph is on the complementary
points. No point of A or Bset lies on l. For every Y, not just tight Y,

    m_l(P_Y)=m_l(P),
    w_l(P_Y)=w_l(P)+2 |r(Y)\N(Y)|.                            (1.2)

To verify the second identity, the old reflected pairs lie in C and none is
removed. Every new reflected pair consists of y in Y and its retained
counterpart r(y) in A\N(Y); these are all the new pairs, counted twice.

In particular, if w_l>=m_l(m_l-1), then

    R_l(P_Y)=m_l^2(m_l-1)=R_l(P)                              (1.3)

for every exchange. Even increasing reflection overlap cannot improve R on
an already capped axis. This is a limitation of this particular potential,
not a statement that the total R is unchanged.

## 2. A modular global-cardinality bound and its equality case

Let p be an odd prime and suppose the allowed squared-distance palette
satisfies

    S subset Z_{>0},       S intersect p Z = empty.           (2.1)

### Lemma 2.1: every S-compatible planar set has at most p^2 points

Take one point as origin and form the Gram matrix

    G_ij = (|x_i|^2+|x_j|^2-|x_i-x_j|^2)/2.

Its entries belong to Z_(p), the rationals whose denominators are prime to p.
Its real rank is at most two, so its reduction over F_p also has rank at most
two: every 3-by-3 minor is identically zero before reduction.

The reduced rows are distinct. If rows i and j were equal, symmetry would
give G_ii=G_ij=G_jj modulo p, and hence

    |x_i-x_j|^2 = G_ii+G_jj-2G_ij = 0 modulo p,

contrary to (2.1). A vector space of dimension at most two over F_p has at
most p^2 elements. This proves the bound for arbitrary real configurations,
not merely for lattice configurations. QED.

### Lemma 2.2: the equality configurations have a full residue coloring

Suppose |P|=p^2. The reduced Gram rank is exactly two. Choose two point
vectors u,v whose 2-by-2 Gram matrix Gamma has determinant a p-unit. Such a
principal nonsingular minor exists: pivot on a nonzero diagonal entry; the
nonzero rank-one symmetric Schur complement has a nonzero diagonal entry.
All points of P then lie in

    L = Z_(p) u + Z_(p) v.

Indeed their two inner products with u,v lie in Z_(p); solve using
Gamma^{-1}. Reduction of their coordinates gives a bijection

    phi:P -> F_p^2.                                         (2.2)

Injectivity follows again from (2.1), and cardinality gives surjectivity.
The reduced norm form Gamma_bar is anisotropic: every nonzero vector of
F_p^2 occurs as the difference of two colors, whose squared distance is
nonzero modulo p.

Two consequences used below are:

* Every line contains at most p points of P. Take two points on the line;
  their direction has p-unit norm, hence a p-unit coordinate. Every other
  collinear point has a p-integral scalar parameter along that direction.
  Their colors lie on an affine F_p-line, which has p colors.
* For z in Q u+Q v, if z is not in L, write z=p^{-k} z_0 with k>=1 and
  z_0 in L\pL. Anisotropy implies

      |z|^2 has p-adic valuation -2k.                       (2.3)

  This is just a denominator calculation: the norm of z_0 is nonzero
  modulo p. No p-adic analytic theorem is being used.

These conclusions hold for **every** equality configuration, including
one selected to maximize R. They do not assume it is congruent to a grid.

## 3. Explicit Hall certificates for reflections and translations

### 3.1 Reflections: all witness axes are covered

Let P be an equality configuration in section 2. Any affine isometry g
whose coordinate formula preserves L and is invertible modulo p maps the
p^2 colors bijectively onto themselves. Thus P and gP each have one point
of every color. After removing C, A and Bset have exactly the same color set.
Pair their points of equal color. Each such pair is forbidden: its squared
distance is zero modulo p if integral, and therefore cannot belong to S.
This is an explicit perfect matching.

Every endpoint-bisector reflection has the required coordinate formula.
For endpoints a,b in P, put d=b-a and c=(a+b)/2. Then

    r(z)=z-2 <z-c,d>/|d|^2 d.                               (3.1)

All coefficients lie in Z_(p), since |d|^2 is in S and is a p-unit.
Its inverse is itself. Consequently the color matching works for **every
axis with w_l>0**, even if it has zero or one actual center. Similarly a
reflection in a line through two actual points has p-integral coefficients.
In particular all axes remaining after the one-center absorption are covered.

This certificate uses no estimate involving h_l, k_{p,s}, m_l, w_l, or R.
It still works if the actual palette of the equality configuration is a
proper subset of the original allowed S.

The relevant graphs are not merely vacuous symmetry graphs. A reduced
reflection has exactly p fixed colors. If a point of P has a fixed color
but is not on the real axis, its reflected point has the same color and
cannot be the different representative in P. Thus

    w_l <= n-p,       |A|=|Bset| >= p-m_l.                  (3.1a)

On an axis with w_l>=T m_l^2 this gives

    |A|=|Bset| >= p(1-1/sqrt(T)).                           (3.1b)

In the positive tail constructed below, these graphs therefore have at least
`(1-o(1))sqrt(n)` vertices in each part. Their matchings are not explained by
A and Bset being empty.

There is also a precise description of tight sets. Label the residual
points a_c,b_c by their common colors c in T. For Y={b_c:c in K},

    N(Y) contains {a_c:c in K}.

Equality holds exactly when

    |a_d-b_c|^2 is allowed for every c in K and d in T\K.    (3.2)

Thus a tight set is a legal switch between two systems of color
representatives. It requires a whole allowed rectangle of
`|K|(|T|-|K|)` cross pairs. Hall itself is automatic; only this additional
mixed-configuration geometry could activate an R comparison.

### 3.2 Translations: all translation vectors are covered

Fix the rational plane V=Q u+Q v from Lemma 2.2, with n=p^2.

* If the translation vector t belongs to L, use the same color matching.
  This includes every supported translation t in P-P.
* If t belongs to V\L, P and P+t are disjoint, and (2.3) applies to every
  cross difference. Every cross squared distance is nonintegral at p.
  The forbidden graph is exactly K_{n,n}.
* If t is not in V, the copies are again disjoint. A point b outside V can
  be at integer squared distances from at most p points of P. Otherwise
  its allowed neighbors would include three noncollinear points: subtracting
  their three squared-distance equations would give two independent rational
  linear equations for b and force b into V. If the neighbors are collinear,
  Lemma 2.2 bounds their number by p. Apply the same argument on both sides.

In the third case the forbidden graph therefore satisfies

    minimum degree >= n-p,      edge density >= 1-1/p.      (3.3)

Since p>=3, n-p>n/2. Every proper nonempty Hall set is strictly expanding.
For completeness, if |Y| is smaller than the minimum degree, its neighborhood
is larger than Y. Otherwise any vertex outside N(Y) would need more than
n-|Y| available neighbors, contradicting the minimum degree. Then N(Y)=A,
again strictly larger unless Y is all of Bset.

Thus irrational translations have only the empty and whole-copy tight
exchanges, both R-neutral. The complete-graph case has the same property.
This is a quantitative density statement at genuine low-D R-selected palette
maximizers, not merely the observation that a generic motion usually avoids
finitely many distance equations.

### 3.3 All other real reflections: either a color certificate or strict Hall

In fact the reflection gate can be completed for **every real reflection**, not
only witness axes. Call an affine reflection V-rational if its linear part
and its offset have rational coordinates in the basis u,v.

First, any V-rational orthogonal linear map M preserves L. Its columns have
p-integral norms (the corresponding diagonal entries of Gamma). By (2.3),
a rational vector with p-integral norm must lie in L. Thus M(L) is contained
in L; apply the same argument to its inverse. Consequently a V-rational
reflection r(z)=Mz+b has the color certificate if b is in L. If b is in
V minus L, every cross difference has nonintegral norm at p, just as for
translations: the forbidden graph is complete.

Now suppose r is not V-rational. Then V intersect r(V) is either empty or a
single fixed point. To prove this, if two distinct rational points and their
images were rational, the linear reflection would map a rational nonzero
vector v to a rational vector w of the same norm. When w!=-v its axis has
direction v+w; when w=-v its normal has direction v. Either formula makes
the reflection matrix rational, and either point-image equation then makes
the offset rational. This is a contradiction. If there is just one rational
point-image pair, involutivity forces the point to be fixed.

It follows that C=P intersect rP has size at most one. All points of Bset
lie outside V, and all reflected points r(a), a in A, lie outside V.
The three-circle subtraction argument of section 3.2 bounds each allowed
degree by p. With t=|A|=|Bset| in {n-1,n},

    forbidden minimum degree >= t-p > t/2.                 (3.4)

Thus every non-V-rational reflection has strict Hall on every proper
nonempty subset. The only tight exchanges are the empty exchange and the
whole reflected copy, both R-neutral.

Together, sections 3.1--3.3 give explicit Hall certificates for **all
translations and all reflections** of every modular equality configuration.
The only cases where a nontrivial tight exchange can exist are the
p-integral rational motions, where it is exactly a switch of color
representatives as in (3.2).

## 4. Globally palette-maximal sheared grids with a positive cap tail

The modular examples need not be balanced squares. A slowly growing
unimodular shear makes them skinny while preserving exact global maximality.

### Theorem 4.1

Let p tend to infinity through primes p=3 modulo 4, put

    r=(p-1)/2,       K=floor((log p)^(1/16)),       Q=K^2+1,
    P_{p,K}={(i,Ki+j): i,j in Z, |i|,|j|<=r},
    n=p^2,          S=the actual squared-distance palette of P_{p,K}.

For all sufficiently large p:

1. P_{p,K} is globally cardinality-maximal among all real planar
   S-compatible sets, with maximum cardinality exactly p^2.
2. `D/n=O((log p)^(-3/8))`, so `Bnorm/n -> infinity`.
3. With the original palette and full pinned fibers,

       sum_{l: m_l>=Q, w_l>=(Q/4608)m_l^2} h_l
           >= 2^(-41) n^2/D >= 2^(-41) Bnorm.              (4.1)

   In particular this tail is omega(n), Q tends to infinity, and its
   overfullness threshold Q/4608 tends to infinity.
4. Every witness-reflection graph has the explicit color perfect matching
   of section 3. The same holds for every supported translation.

### 4.1 Cardinality and distance count

The shear (i,j)->(i,Ki+j) is unimodular, so P has exactly one point of each
color in F_p^2. For p=3 modulo 4,

    x^2+y^2=0 modulo p  implies  x=y=0 modulo p.

Thus no nonzero squared distance of P is divisible by p. Lemma 2.1 gives
the global upper bound p^2, which P attains.

Every squared distance is a sum of two integer squares at most

    [(K+1)^2+1](p-1)^2 <= 4K^2 p^2  (K>=2).

The classical sum-of-two-squares upper bound
`U(X)=O(X/sqrt(log X))`, also used in the earlier rectangle note, gives

    D/n = O(K^2/sqrt(log p)) = O((log p)^(-3/8)),
    Q D/n = O((log p)^(-1/4)) -> 0.                         (4.2)

No statistical approximation to the finite palette is used.

### 4.2 Geometry of the sheared region

Use the orthonormal coordinates

    X=(x+Ky)/sqrt(Q),      Y=(-Kx+y)/sqrt(Q),
    L=r sqrt(Q),          H=r/sqrt(Q).

The point set is exactly the original integer lattice intersected with

    |Y|<=H,       |X-KY|<=L.                               (4.3)

Since K/Q<=2/5 for K>=2, this region contains the rectangle

    |X|<=L/2,       |Y|<=H,                                (4.4)

and is contained in the slab |Y|<=H. The lattice is rotated in these
coordinates; it has not been replaced by a new rectangular lattice.

Choose actual bulk pins (i,Ki+j) with

    |i|<=r/64,       |j|<=r/16.

They satisfy |X|<=L/16, |Y|<=H/16 and there are at least

    r^2/1024 >= n/9216                                    (4.5)

of them.

### 4.3 A full-fiber lower bound without assuming reflection invariance

Use the symmetric set E of displacement vectors

    +(a,Ka+b), -(a,Ka+b),
    ceil(r/6)<=a<=floor(r/5),       |b|<=r/16.

For r>=60 it has at least `r^2/480 >= n/4320` elements. At every selected
bulk pin c, all c+E belong to P. The positive vectors have

    L/8 < X < L/4,       |Y|<=H/16,                         (4.6)

and their negatives have the opposite X sign. The finite constants follow
from `1/6-(2/5)/16=17/120>1/8` and
`1/5+(2/5)/16=9/40<1/4`.

For each full pinned label s, let e_s count the vectors of E with norm s,
and let k_{c,s} be the **full** fiber size in P. Central symmetry of E makes
e_s even, equally split between the two sides. Its ordered opposite-side
witnesses have mass

    e_s^2/(2D k_{c,s}).

Cauchy--Schwarz, keeping those full denominators, gives

    sum_s e_s^2/(2D k_{c,s})
       >= |E|^2/[2D sum_{e_s>0} k_{c,s}]
       >= |E|^2/[2D(n-1)].                                (4.7)

This argument does not assert that the entire fiber is reflection-symmetric.
It avoids that false assertion for a sheared lattice.

Sum (4.7) over the bulk pins. The selected witness mass E_total satisfies

    E_total >= c0 n^2/D,       c0=2^(-40),                 (4.8)

because `2*9216*4320^2=343985356800 < 2^40`.
Every selected witness has a near-short-direction bisector: its endpoints
have X separation greater than L/4 and Y separation at most H/8. If an axis
direction has components (alpha,beta), beta>0, then

    |alpha|/beta <= H/(2L).                                (4.9)

The axis passes through the actual selected bulk pin.

### 4.4 Integer reflected pairs on every sufficiently occupied selected axis

Take a primitive integer direction v for such an axis, and let
(alpha,beta) be its rotated components. Put L'=L/2 and t=H/beta.
Since the entire set lies in |Y|<=H, its actual line occupancy satisfies

    m<=2t+1.

If m>=65, then t>=32. The weaker cone condition
`L' |alpha|<=8H beta` follows from (4.9). Let

    R0=floor(H/(16 beta)),
    S0=floor(L'/(16 beta)).

All the integer points

    c+a v+b v_perp,       |a|<=R0, |b|<=S0,

lie in (4.4). Indeed their coordinate displacements are at most

    R0|alpha|+S0 beta <= 9L'/16,
    R0 beta+S0|alpha| <= 9H/16,

and the bulk pin uses at most L'/8,H/8. Reflection in the axis sends
(a,b) to (a,-b). The fact that v_perp is also an integer vector is why the
construction remains valid in the rotated coordinates.

Every point with b!=0 is a nonfixed reflected endpoint. Distinct parameter
pairs give distinct points. Therefore the ordered count obeys

    w >= (2R0+1) 2S0
      >= (L'/H)t^2/256
      >= (L'/H)m^2/2304
       = Q m^2/4608.                                     (4.10)

This counts genuine reflected endpoints in the full point set, not merely
potential circle intersections.

### 4.5 Low-occupancy removal and the positive tail

Let L_M be the full normalized mass on axes with m<=M. The checked
low-center estimate from `wr_investigation.md` is

    L_M^2 <= M n^2(n-1)/D <= M n^3/D.                      (4.11)

Briefly, there are at most M n(n-1) ordered witnesses on these axes,
while the sum of inverse squared full-fiber sizes is at most nD;
Cauchy--Schwarz gives (4.11).

Use M=Q. From (4.8),

    (L_Q/E_total)^2 <= Q D/(c0^2 n) -> 0.

Eventually at least E_total/2 remains on selected axes with m>Q>=65.
Apply (4.10). This proves (4.1) with the stated constant. Also
`Bnorm=n(n-1)/D-O(n)`, so both Bnorm and the selected tail are omega(n).
QED.

### Corollary: maximality does not restore cap-tail absorption

Even restricted to globally cardinality-maximal sets for their actual
palettes, there is no uniform estimate

    sum_{l:m_l>=2, w_l>=T m_l^2} h_l
       <= epsilon(T) Bnorm + C_T n,
    epsilon(T)->0,       C_T finite.                       (4.12)

Choose a fixed T with epsilon(T)<2^(-42), then take the family above far
enough that Q/4608>=T and n=o(Bnorm). Equation (4.1) contradicts (4.12).

This is a counterexample to the specified tail absorption on actual
palette maxima. **It is not a counterexample to WR:** no upper bound making
R small has been asserted.

## 5. What the R tie-break does and does not change

For each palette S of Theorem 4.1, select a global S-compatible
cardinality maximum that also maximizes R. Its cardinality is still p^2.
Its actual palette is contained in S, hence D=o(n) and Bnorm/n tends to
infinity. Lemmas 2.1--2.2 and all of section 3 apply to it.

Thus R-selection cannot invalidate the color perfect matchings. On a
reflected capped axis, (1.3) also applies to every tight exchange at this
R-maximizer. Consequently a useful contradiction must compare the R
contributions on **other axes**. Neither the matching nor the fact that
reflection overlap has increased supplies the sign of that comparison.

What is not established is that the particular sheared grid maximizes R
among the p^2-point S-compatible sets. Accordingly the positive-tail
corollary is proved for cardinality maxima, but is **not** claimed for the
R-selected subclass. The automatic-Hall and capped-axis-neutrality results,
on the other hand, do hold for that subclass.

## 6. Small exact finite audit

Reproduce with

    python3 Submission/verify_wr_extremal_hall.py

Output: `Submission/wr_extremal_hall_verification.txt`.
There are eight fixed allowed-palette audits: five small maximum-clique
searches, two additional modular matching checks, and one full-fiber check
at three pins. The subset exchange-identity test reuses the 3-by-3-square
allowed palette; it is not a sweep of additional palette-maximization problems.
There are no numerical WR-ratio tables and no floating-point equality tests.

For a rational palette, put anchors at squared distance t in S. Every other
point is one of the circle intersections for r,s in S. In anchor-normalized
coordinates its horizontal coordinate is `(r+t-s)/(2t)` and its height
squared is rational. Two nonzero heights from distinct square classes
cannot have rational squared mutual distance. Thus candidates split into
rational Gram-matrix blocks, with collinear candidates included in each.
All anchor lengths and all blocks are searched. This is a global finite
reduction, not a search in a chosen coordinate box. The bitset clique
search is independently checked against NetworkX's Bron--Kerbosch routine.
Exact anchor-frame invariants identify isometry classes.

| Allowed palette | Global maximum | Maximum isometry classes | R values |
|---|---:|---:|---|
| {1} | 3 | 1 | 0 |
| {1,2} | 4 | 1 | 8 |
| {1,3,4} | 7 | 1 | 60 |
| {1,2,4,5,8} | 9 | 1 | 88 |
| {1,2,3,4,5} | 7 | 2 | 34, 60 |

For every maximum representative the script checks every two-center witness
reflection and every nonzero supported translation. It enumerates every
Hall subset and computes R on every tight exchanged configuration. For the
first four palettes, no nonvacuous two-center reflection has a proper tight
set. All proper tight translated exchanges are congruent to the starting
configuration. Thus the R tie-break yields no improvement in those tests.
Exact generic motions give complete forbidden graphs. The three-corner
square is a control: reflection across its missing side produces a singleton
Hall deficiency, so the implementation is not declaring Hall automatic for
arbitrary sets.

Further checks include:

* Full residue matching, doubled-Gram rank, and fixed-color bounds (3.1a)
  for the 3-by-3 square,
  7-by-7 square, and its shear K=2: respectively 20,536,536 lines through
  two actual points; 20,548,786 endpoint bisectors; and 24,168,168 supported
  nonzero translations.
* All 12,201 mixed-set reflection identities in the specified small-subset
  audit with one fixed allowed palette, including nonmaximal sets; the exact
  formula (1.2) and capped equality (1.3) are checked directly.
* Exact quadratic-field checks for translation by (sqrt(2),0) and reflection
  in y=sqrt(3)x of the 3-by-3 square. Their residual forbidden graphs have
  minimum degrees 8 on 9 vertices per side and 7 on 8 vertices per side;
  every proper nonempty Hall set is strictly expanding.
* Twelve exact rational overlap-construction/occupancy checks, and three
  pinned checks of (4.7) using full fibers of the 31-by-31 shear K=2.

### An ancillary exchange-connectivity check (allowed-palette caveat)

For the last allowed palette the two maximum types are the 3-by-3 integer
square with two adjacent corners removed (R=34), and a unit regular hexagon
with its center (R=60). They have different actual palettes, respectively
{1,2,4,5} and {1,3,4}; do not treat this as a same-actual-palette comparison.

No isometry exchange connects the two types, even if all isometries, rather
than just the audited motions, are admitted. Any nondegenerate triangle in
the first type has rational area; in the second its area is a nonzero
rational multiple of sqrt(3). Hence an isometric cross-intersection is
collinear and has at most three points. Two copies of one type cannot cover
seven points of the other type. By the exact maximum classification, every
cardinality-neutral compatible exchange stays in its original isometry
class and preserves its R.

This ancillary example shows why local stability under all one-copy Hall
exchanges must not be confused with global R maximization for an allowed
palette. It is not used to claim the positive tail at R-maximizers.

## 7. Precise remaining gap

The analysis rules out two concrete hoped-for shortcuts:

1. **Cardinality extremality removes the overfull tail or makes it force a
   Hall deficiency.** Theorem 4.1 and its explicit matchings refute this,
   quantitatively, for genuine actual-palette global maxima.
2. **A tight exchange that improves reflection overlap raises the capped
   potential on its generating axis.** Formula (1.3) refutes this exactly.
   Some translated graphs are moreover so dense that no nontrivial tight
   exchange exists at all.

What remains unproved is a comparison coordinating different axes at a
selected F(s)- and R-maximizer. In particular:

* The theorem does not assert `F(|S_{p,K}|)=p^2`. A maximum for a fixed
  arithmetic palette need not maximize cardinality among all palettes of
  that size.
* The positive cap tail is not proved to survive selection of maximum R
  even within the fixed palette.
* No implication from actual **WR failure**, namely
  `Bnorm^2/(n^2+R)` becoming unbounded, to an R-improving mixed configuration
  is proved. The examples have large Bnorm/n and a positive overfull tail,
  not a demonstrated divergent WR ratio.

These are limits of the result, not new surrogate conjectures. The concrete
new information is the exact modular extremal family, the positive-tail
lower bound on that family, the universal matching certificates for its
palette maxima, and the capped-axis exchange identity. A proof using the
remaining global R-selection information would have to go beyond the Hall
and local-cap mechanisms tested here.

## File integrity

No Lean files were edited. The SHA-256 of `Submission/Spec.lean` remains

    c2fbaabe5ad8088f856ca97625747c7a01754f3c149dd6a493454e776de290db
