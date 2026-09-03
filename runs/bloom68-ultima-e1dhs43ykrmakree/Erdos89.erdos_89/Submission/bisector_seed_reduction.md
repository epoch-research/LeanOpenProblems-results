# A uniform exact-incidence seed reduction

This is a partial reduction, not a solution of Spec.lean. A research agent
supplied the argument; the parent checked the probability estimates, rational
reconstruction formulas, rank argument, and the field-descent limitation.

Let P have n>=2 points and D positive distances. Either D>(n-1)/4 or there
is A⊂P with |A|<=7200 sqrt(D log(2n)) such that every p∈P is the unique
intersection of two distinct perpendicular bisectors with endpoints in A\{p}.

## Exact probabilistic proof

Assume n-1>=4D. Sample every point independently with probability q. For a
fixed p, its other points have at most D nonempty distance fibers of sizes r_j.
Fix a perpendicular bisector line ell through p occurring in the full set.
Reflection across ell partitions a circle's r points into orbits of size at
most two (use singletons for missing reflections). Divide whole orbits into
two groups U,V with sizes differing by at most two. Each group has at least
(r-2)/2 points. Any selected point in each group gives a bisector different
from ell. With x=q(r-2)_+, the probability of missing one group is at most

  exp(-min(x^2,x)/36).

Indeed it is at most 1-(1-exp(-x/2))^2 and at most 2exp(-x/2). For x<=4,
1-exp(-x/2)>=x/6; for x>=4, 2exp(-x/2)<=exp(-x/4).

Fibers are disjoint. Put X=Σ_j q(r_j-2)_+ >=q(n-1)/2>=qn/3. Splitting
terms at x=1 and using Cauchy gives Σmin(x_j²,x_j)>=min(X/2,X²/(4D)).
Writing k=qn, the event that every retained equal-distance pair around p
has the same bisector ell therefore has probability at most

  exp(-min(k/216,k²/(1296D))).

Let L=log(2n), k=1296(sqrt(DL)+L). If k>=n/2 use A=P; a fiber of at least
three points supplies distinct bisectors at every p. Otherwise sample with
q=k/n. There are at most n³ pairs (p,ell), so the probability that some p is
not determined is at most n³exp(-6L)<1/2. Markov gives probability at most
1/2 that |A|>2k. A successful sample exists. The elementary two-anchor bound
n<=2D²+2 implies L<=3D, and hence |A|<=7200sqrt(DL) in both cases.

## Rational reconstruction and rank

If p is determined by bisectors of (a,b),(c,d), let u=b-a, v=d-c,
h=(|b|²-|a|²)/2, j=(|d|²-|c|²)/2, and Delta=u_x v_y-u_y v_x !=0. Then

  p_x=(h v_y-u_y j)/Delta,
  p_y=(u_x j-h v_x)/Delta.

The numerators have degree at most 3 in seed coordinates and the denominator
has degree at most 2. Thus for any subfield F⊂R, F(coords P)=F(coords A).
The two equal-distance equations per p outside A have a nonsingular 2×2
Jacobian block in the columns of p; all other columns are in A. Hence the
full equal-distance-class Jacobian has rank at least 2(n-|A|). Fixing two
seed points at (0,0),(1,0) removes the four similarity dimensions.

Substitute these formulas into all edge-color equations and the strict order
of color representatives. A squared edge has numerator degree <=10 and
squared-denominator degree <=8. Clearing positive squared denominators gives
O(n²) rational equations and strict inequalities of degree <=18 in 2|A|
variables (or 2|A|-4 after similarity normalization). Keep Delta!=0 and all
positive distinct class representatives. The entire exact coloring, including
the distance counts of every subset, is preserved in any solution.

Every nonempty rational semialgebraic system has a real-algebraic solution.
One can also prove the required instance directly: choose a transcendence
basis t of the field of a real solution, and a primitive element theta of its
finite separable extension over Q(t). Express coordinates rationally in
(t,theta). The minimal polynomial has a simple root at the original point.
Its real implicit branch permits sufficiently close rational specialization
of t, retaining all nonzero denominators and strict inequalities. Polynomial
identities persist because their numerators are divisible by the minimal
polynomial. The resulting coordinates lie in one real-embedded number field.

Consequently the sharp conjecture is equivalent, with the same constant, to
the assertion for finite subsets of K² over ALL real-embedded number fields K.
This gives no degree, height, density, or lattice-rank bound. The applicable
corpus reference for exact sign-condition sampling is Basu 0708.2854,
ams_final_submission.tex, lines 1327--1389, not a distinct-distance theorem.

## Why field descent does not close the problem

The seed is a GENERATING core, not a proper-field core. All reconstructed
points already lie in its field, so the exterior-pin bound does not apply.
For odd prime m, K=Q(2^(1/m)) has no intermediate proper field between Q and
K. The saved full coefficient-box examples B_M⊂K+iK have D=o_m(|B_M|), while
all class-preserving planar models are similarities. Any similarity of Q²
meets B_M in at most (2M+1)² points, versus |B_M|=(2M+1)^(2m): its intersection
with the coefficient space has Q-affine dimension at most two, and at most
two coefficient projections are injective. Thus no positive-density proper
field core follows. Full infinitesimal rank also occurs in saved lowD rigid
examples and does not bound degree or height.

No unrestricted actual-support estimate has been obtained from this seed.
No Lean file was modified and neither requested theorem is proved.
