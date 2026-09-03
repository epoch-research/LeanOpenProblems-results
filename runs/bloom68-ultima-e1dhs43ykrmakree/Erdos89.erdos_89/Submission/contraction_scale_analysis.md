# Contraction criterion: separated unequal fibers and the overlap obstruction

## Status

This investigation does **not** prove or disprove the unrestricted contraction criterion, and does not prove the sharp planar Erdős distinct-distance conjecture. It establishes two complete restricted lemmas:

1. With full recovery of the coefficients of the squared-distance polynomial, arbitrary unequal two-scale fibers have linearly many distinct distances, unless the lift is contained in one complex affine line. No common anchor or balance assumption is needed.
2. With coefficient recovery and an affine transversal, an elementary layer-cake inequality gives zero-loss extraction in the balanced case, and contraction with the explicit constant 12 in all nontrivial cases.

A grid example shows that uniformly bounded coefficient-evaluation multiplicity fails at overlapping scales. It is not a counterexample to unrestricted selection.

The existing Lean file was inspected and not changed. Its geometric assertion remains an explicit unproved hypothesis.

## 1. Exact formulation of the obstruction to contraction

Write K(P)=|P|/D(P), where D counts distinct positive distances (equivalently, squared distances). For |P|>=4 put

    defect(P) = K(P)^2 - max{K(Q)^2 : Q subset P, 2 <= |Q| <= |P|/2}.

The proposed criterion is exactly boundedness above of this defect for sufficiently large P. Every pair has K=2, so an unbounded-defect counterexample sequence must also have unbounded K. Failure of a restricted selector class does not imply an unbounded unrestricted defect.

## 2. Complex-direction lemma for distance polynomials

Identify R^2 with C. Let S be a finite set of n distinct pairs (a,b) in C^2. Associate the moving planar point

    p_(a,b)(t) = a + t b,  t real.

For distinct x=(a,b), y=(a',b') in S, define the nonzero real polynomial

    F_xy(T) = |a-a'|^2 + 2 Re((a-a') conjugate(b-b')) T + |b-b'|^2 T^2.

Let T(S) denote the set of distinct such polynomials. For a real M, assume:

- the evaluated planar points a+Mb are distinct; and
- evaluation F -> F(M) is injective on T(S).

### Theorem 1

There is an absolute c>0 such that, if S is not contained in a complex affine line, some point of P_M={a+Mb:(a,b) in S} determines at least c n distinct distances to P_M. In particular,

    D(P_M) >= c n.

More generally, if evaluation has fibers of size at most L, then

    D(P_M) >= c n/L.

### Proof

Use the following standard consequence of complex Beck's theorem: a noncollinear n-point set in C^2 has a point incident to at least beta n distinct spanned complex lines, for an absolute beta>0.

For completeness, complex Beck gives either at least c1 n^2 spanned lines or a line with at least n/100 points. In the first case, averaging point-line incidences supplies a point incident to at least 2 c1 n lines. In the second case, take a point outside the rich line; its joins to the points on that line are distinct. Thus beta=min(2c1,1/100) works. This is valid over C, not an application of real-plane Beck to a four-dimensional real set.

Fix this point x. Write a difference to another point as (u,v), and write its polynomial as c0+c1 T+c2 T^2. If v is nonzero, the complex direction is w=u/v, and

    Re(w) = c1/(2 c2),       |w|^2 = c0/c2.

Consequently one polynomial can give at most two directions, w and conjugate(w). If v=0 it gives only the vertical direction. The beta n pinned directions therefore require at least beta n/2 pinned distance polynomials. Evaluation injectivity transfers this to actual distances. If each evaluation fiber has size at most L, divide the count by L. Set c=beta/2.

### The exceptional complex-line case is explicit

If S is contained in a complex affine line, write

    (a,b) = (a0,b0) + z(u0,v0),   z in Z subset C.

Then

    P_t = a0+t b0 + (u0+t v0) Z.

Whenever the last scalar is nonzero, P_t is a direct planar similarity of Z. Thus this exceptional case really contains arbitrary planar point configurations; it cannot simply be discarded in a universal argument.

### Arbitrary unequal fibers

Suppose S={(a,b): b in B, a in A_b}, every A_b is nonempty, there are at least two coarse sites b, and at least one fiber has two points. Then S cannot be contained in a complex affine line: two points in one fiber force such a line to have b constant, contradicting the other coarse site.

Therefore Theorem 1 applies to **all** such unequal fibers whenever coefficient recovery holds. The fibers need not intersect, be translates, have equal size, or admit a common anchor.

For n>=4, taking any pair Q gives contraction with a universal constant C=c^(-2), since K(P)^2<=c^(-2) and K(Q)^2=4. This is a restricted-family result, not the universal geometric lemma.

## 3. An explicit sufficient separation condition

Suppose S is contained in Z[i]^2. Put

    A = diameter of the fine-coordinate projection,
    B = diameter of the coarse-coordinate projection.

If M is a positive integer and

    M > max(A^2, 4 A B),

then all points a+Mb are distinct and coefficient recovery holds.

Indeed, the coefficients of every distance polynomial are integers with

    0 <= c0 <= A^2,       |c1| <= 2AB,       c2 >= 0.

If two evaluations agree, reducing modulo M shows c0=c0'. Dividing the remaining equality by M gives

    c1-c1' + M(c2-c2') = 0.

Since |c1-c1'|<=4AB<M, this gives c1=c1' and c2=c2'. The same argument comparing a distance polynomial with the zero polynomial excludes point collisions.

This is full three-coefficient separation. It must not be silently replaced by the weaker condition M>A^2 alone when B is large.

More generally, M>A^2 already gives evaluation multiplicity at most

    L <= 1 + floor(4AB/M),

because c0 is fixed by the value modulo M, and the possible c1 values lie in an interval of length 4AB and one residue class modulo M. Distinctness of the evaluated points also follows from M>A^2 for Gaussian-integer coordinates. Hence Theorem 1 gives the corresponding lower bound c n/L.

## 4. Rigidity of linear deformations

For any fixed finite S, two different polynomials in T(S) have equal values at at most two real parameters. Point collisions also occur at only finitely many parameters. Therefore, if S is not complex-collinear,

    D(P_t) >= c n

for all but finitely many real t, with a pinned linear bound as well.

Equivalently: if a family of linear trajectories a_i+t b_i has n distinct points and fewer than c n distances at infinitely many parameter values, then all trajectories collectively form a family of direct similarities of a fixed planar set, as described above.

For Gaussian-rational a,b, any real transcendental parameter, or real algebraic parameter of degree greater than two, automatically distinguishes all distinct distance polynomials. This follows because their coefficients are rational and their degree is at most two.

## 5. Elementary layer-cake extraction with an affine transversal

Retain coefficient recovery. Let the nonempty fine fibers A_b have sizes m_b, with at least two coarse sites and max m_b>=2. Suppose there are lambda,mu in C such that

    lambda b + mu belongs to A_b for every b in B.

A common anchor is the special case lambda=0. Put

    B_j = {b : m_b >= j},

let m1>=m2 be the largest and second-largest fiber sizes, and choose a largest fiber A_*.

### Lemma 2: exact layer-cake inequality

    D(P_M) >= D(A_*) + sum_(j=1)^m2 D(B_j).

### Proof

Group the cross-fiber distance polynomials by their leading coefficient t=|b-b'|^2>0. For one such coarse pair, put v=b-b'. Its lower coefficients are obtained from

    u in A_b-A_b'  ->  (2 Re(u conjugate(v)), |u|^2).

This map has fibers of size at most two, because it fixes a line projection and a norm in the real plane. For any two nonempty finite sets X,Y in R^2,

    |X-Y| >= |X|+|Y|-1.

One elementary proof orders X and -Y by a generic real linear functional and constructs an increasing chain of |X|+|Y|-1 sums. Thus the chosen coarse pair supplies at least

    ceil((m_b+m_b'-1)/2) >= min(m_b,m_b')

different distance polynomials. For each t, maximize this minimum over its coarse pairs. The resulting sum over t is exactly

    sum_(j=1)^m2 D(B_j),

by the layer-cake identity. Within the largest fiber, D(A_*) additional polynomials have leading coefficient zero, so are disjoint from all the cross-fiber polynomials. Evaluation injectivity proves the displayed inequality.

The inequality itself does not need the affine-transversal assumption. That assumption is used next to realize the coarse sets as subsets of the original P.

### Zero-loss extraction in the balanced case

For j<=m2, define the actual subset

    Q_j = {(M+lambda)b+mu : b in B_j} subset P_M.

The scalar M+lambda is nonzero, because otherwise distinct transversal points would collide. Therefore D(Q_j)=D(B_j). A translated copy of A_* is also a subset of P_M.

Let R be the largest of K(A_*) and K(B_j), 1<=j<=m2. All these sets have at least two points. The layer-cake identity for cardinalities gives

    |A_*| + sum_(j=1)^m2 |B_j| = n+m2.

Consequently

    R D(P_M) >= n+m2,

and some candidate subset has ratio strictly larger than K(P_M).

If both max m_b<=n/2 and |B|<=n/2, every candidate has size at most n/2. Thus this gives the requested extraction with C=0.

### Uniform constant 12 without balance

If m1>n/2, a coarse pair involving the largest fiber produces at least m1/2 distinct cross-fiber distance polynomials, by the same two-to-one argument. Thus K(P)<2n/m1<4.

If |B|>n/2, take a nontransversal point over b0, with offset u nonzero from lambda b0+mu. Its differences to the transversal points have the form

    u + (T+lambda)v,       v=b0-b.

The quadratic and linear coefficients determine |v|^2 and Re(u conjugate(v)), so there are at most two possible v per polynomial. The |B|-1 other coarse sites supply at least ceil((|B|-1)/2) polynomials. The transversal point over b0 supplies one more, with leading coefficient zero. Hence D(P)>(|B|/2), and again K(P)<4.

In either unbalanced case, any two-point Q has K(Q)^2=4 and

    K(P)^2 < 16 = K(Q)^2+12.

Thus all nontrivial coefficient-recovering fiber families with an affine transversal satisfy contraction with C=12 and threshold n=4. This conclusion is entirely elementary once coefficient recovery is available.

## 6. Why overlapping scales are genuinely outside these proofs

Let

    A_s = {0,...,s-1}^2,       B = {0,1}^2,       M=s,
    S_s = A_s x B.

Then P_s=A_s+sB is the ordinary 2s-by-2s integer grid, with n=4s^2 distinct points. Thus this example has full uniform fibers and a common anchor, not an unequal-fiber pathology.

The formal distance-polynomial support has at least (2s-1)s elements. To see this, fix the coarse difference v=(1,0) and vary the fine difference u=(x,y) with

    -(s-1)<=x<=s-1,       0<=y<=s-1.

The polynomials are

    T^2+2xT+x^2+y^2,

and are pairwise distinct: the linear coefficient recovers x and the constant coefficient then recovers y.

In contrast, the actual squared distances are integers at most 2(2s-1)^2 that are sums of two squares. The classical counting estimate for sums of two squares gives

    D(P_s)=O(s^2/sqrt(log s)).

It follows that

    |T(S_s)|/D(P_s) = Omega(sqrt(log s)).

Thus even the **average** number of formal distance polynomials per actual distance is unbounded. A constant-multiplicity transfer from formal coefficients to actual distance colors is false at overlapping scales.

This does not refute the contraction criterion: the actual P_s has ordinary smaller-grid subsets. It pinpoints the missing adaptive step. Neither complex Beck nor the layer-cake inequality controls how these coefficient collisions should be converted into a high-ratio proper subset.

## Verification and external input

The complex incidence input was checked against the local source of Csaba D. Tóth, *The Szemerédi–Trotter Theorem in the Complex Plane*, arXiv:math/0305283, published in Combinatorica 35 (2015), 95–126. The complex Beck dichotomy is the first corollary in its introduction. The source is `/corpus/src/math_0305283/2005Mar_cmplx.tex`.

`verify_contraction_scales.py` performs exact integer/rational checks of:

- the two-directions-per-polynomial calculation, including pinned versions;
- coefficient recovery under the explicit diameter condition;
- arbitrary unequal fibers without common anchors;
- the complex-collinear similarity exception;
- the layer-cake inequality and the balanced actual-subset extraction;
- coefficient collisions for overlapping-scale full grids.

These computations check identities and finite instances; the proofs above, not the computations, establish the lemmas. No Lean formalization or modification was made.

## What remains

There is no argument here bounding the unrestricted contraction defect for arbitrary planar P. In particular, no theorem is supplied that converts high coefficient-evaluation multiplicity at every useful scale into a subset Q preserving K(P)^2 up to an absolute additive loss. Establishing such a theorem, or finding configurations whose unrestricted defect diverges, remains the unresolved part of the task.
