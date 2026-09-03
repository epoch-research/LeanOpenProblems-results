# Disk localization with actual distance support

## Status and scope

The universal disk criterion remains **unproved and undisproved** in this work. No counterexample to it, and no proof of the sharp planar Erdős distinct-distance conjecture, is claimed.

There is, however, a concrete unconditional geometric inequality here. It gives:

1. **Ambient-capacity localization for every subset of a square-lattice disk.** The selected set is an actual intersection with a closed Euclidean disk, and its denominator is its actual number of distinct distances.
2. **Bounded disk defect for arbitrary fourth-parity-class restoration.** Start with any three parity classes throughout a lattice disk and restore an arbitrary selection of the fourth class. The restoration need not be an annulus, periodic, radially symmetric, or confined to one scale.
3. **Vanishing upper disk defect for sparse random lattice disks with unbounded potential.** For example, independently retaining points with probability `(log(4R^2))^(-1/4)` gives this conclusion with probability tending to one.

These results use order-zero support counts, not Shannon or positive-order Rényi entropy. A logarithmic *spatial radius moment* appears in the disk-packing proof; it is not an entropy replacement for the distance count. No Lean files were changed.

---

## 1. Definitions and main inequalities

For a finite planar set P, let D(P) be the number of distinct positive Euclidean distances. Equivalently, count distinct positive squared distances. Put

    K(P) = |P| / D(P),       Phi(P) = K(P)^2

when |P| >= 2. For n = |P| >= 4 define

    M_disk(P) = max { |Q| / D(Q) :
                      Q = P intersect a closed Euclidean disk,
                      2 <= |Q| <= n/2 }.

This maximum exists: there are finitely many subsets, and the diameter disk of a closest pair contains exactly that pair. In particular,

    M_disk(P) >= 2.                                      (1.1)

Let

    S(x) = #{m in Z : 1 <= m <= x, m = a^2+b^2 for some integers a,b}.

### Theorem A: unconditional ambient-capacity localization

There is an absolute constant C such that, for every R > 0 and every

    P subset Z^2 intersect closedDisk(c_0,R),    |P| = n >= 4,

one has

    M_disk(P)^2 >= ( n / S(4R^2) )^2 - C.                 (1.2)

More quantitatively, there are absolute C,R_0 such that, for R >= R_0, writing

    L = log(4R^2),       delta = n/R^2,       log_+(u) = max(0,log u),

one has

    (n/S(4R^2))^2 - M_disk(P)^2
      <= C delta^2 (1 + log_+(1/delta))
         + C L^(121/40) R^(-1/20).                       (1.3)

The constant in (1.2) is uniform even when the set is sparse or highly nonuniform. The center c_0 is arbitrary. Similarities of the square lattice have the same assertion after measuring R in lattice units.

**Important limitation:** S(4R^2) is an upper bound for D(P), not a lower bound. Thus (1.2) does not on its own prove the proposed criterion for arbitrary lattice subsets. This direction of comparison must not be reversed.

### Theorem B: arbitrary restoration of a fourth parity class

Fix any three-element set A subset (Z/2Z)^2. Suppose

    {p in Z^2 : |p-c_0| <= R and p mod 2 belongs to A}
       subset P subset {p in Z^2 : |p-c_0| <= R}.

Then, for an absolute C and every such P with n >= 4,

    Phi(P) <= M_disk(P)^2 + C.                           (1.4)

This is uniform over R, c_0, the omitted parity class, and **every choice of restored points**. It includes arbitrary multiscale or nonperiodic restoration, not just the audited thin-annulus example.

### Theorem C: sparse examples with unbounded potential and vanishing defect

Let G_R = Z^2 intersect closedDisk(0,R), let L=log(4R^2), and retain each point independently with probability

    theta_R = L^(-1/4).

With probability tending to one, the resulting P_R satisfies

    |P_R| = (1+o(1)) pi R^2 L^(-1/4),
    D(P_R) = (1+o(1)) S(4R^2),
    Phi(P_R) = (1+o(1)) (pi/(4 kappa))^2 sqrt(L) -> infinity,

where kappa is the Landau-Ramanujan constant. Nevertheless,

    Phi(P_R) - M_disk(P_R)^2 <= o(1).                   (1.5)

The upper bound in (1.5) does not assert that the defect is nonnegative. A smaller disk may have strictly higher potential.

---

## 2. Unconditional input and elementary facts

The only analytic-number-theory input is the classical quantitative Landau-Ramanujan asymptotic

    S(x) = kappa x / sqrt(log x) * (1 + O(1/log x)),       (2.1)

as x tends to infinity, with absolute implied constants. This is the usual first-error-term consequence of the classical asymptotic expansion for sums of two squares. No short-interval theorem is used: both the upper and lower estimates used below follow directly from (2.1).

For every center c and r >= 0,

    # (Z^2 intersect closedDisk(c,r))
       <= pi (r + sqrt(2)/2)^2.                         (2.2)

Indeed, the disjoint unit squares centered at these lattice points are contained in the larger disk. Conversely those squares cover the disk of radius max(0,r-sqrt(2)/2), so for the full lattice disk its cardinality is pi r^2+O(r+1), uniformly in the center.

For a lattice subset Q lying in a radius-r disk,

    D(Q) <= S(4r^2).                                    (2.3)

This is an exact support bound: a squared distance is a positive integer sum of two squares and is at most 4r^2.

For (1.1), let p,q be a closest pair at distance d. A third point in their closed diameter disk would have distance less than d from at least one endpoint. Therefore that disk selects exactly p,q. This argument applies to arbitrary finite planar sets, not just lattice sets.

---

## 3. A disk packing with a bounded logarithmic radius moment

### Lemma 3.1

Put lambda = 2^(-10). For each 0 < h_0 <= lambda, the open unit disk admits a countable packing by disks with pairwise disjoint interiors, grouped into finite stages j=1,2,..., with the following properties:

- every stage-j disk has radius

      rho_j = (h_0/2) lambda^(j-1);

- after stage j the uncovered area is at most pi 2^(-j);
- if w_j is the total area of the stage-j disks divided by pi, then

      sum_j w_j = 1,
      sum_j w_j log(1/rho_j)
        <= log(2/h_0) + log(1/lambda).                   (3.1)

Boundaries have area zero. Only finitely many stages will be used to select points.

### Proof

Let h_j=h_0 lambda^(j-1). At stage j take every h_j-grid square whose closure lies in the still-uncovered open region, and insert its inscribed disk. Disks in different chosen squares have disjoint interiors; future disks lie outside previous closed disks.

Write A_j for the uncovered area after stage j and a_j=A_j/pi, with a_0=1. Let N_i be the number of stage-i disks. Their grid squares are disjoint and lie in the previous uncovered region, so

    N_i h_i^2 <= A_(i-1).                                (3.2)

Set t_j=sqrt(2) h_j. A point in the uncovered region that does not lie in a chosen square is within t_j of its boundary. That boundary is contained in the original unit circle and the circles of earlier disks. The area E_j of this bad strip therefore satisfies

    E_j <= 2 pi t_j
           + sum_(i<j) N_i (2 pi (h_i/2) t_j + pi t_j^2).

By (3.2),

    E_j/pi <= 2 sqrt(2) h_j
              + pi sqrt(2) sum_(i<j) a_(i-1) lambda^(j-i)
              + 2 pi sum_(i<j) a_(i-1) lambda^(2(j-i)).   (3.3)

Assuming inductively a_i <= 2^(-i), (3.3) is at most 2^(-(j-1)) times

    2 sqrt(2) h_0
      + pi sqrt(2) lambda/(1/2-lambda)
      + 2 pi lambda^2/(1/4-lambda^2)
      < 1/4.                                            (3.4)

The selected disks fill a fraction pi/4 of the selected squares. Hence

    a_j <= (1-pi/4) a_(j-1) + (pi/4) E_j/pi
        <= (1-3pi/16) 2^(-(j-1))
        < 2^(-j).

This proves the area assertion. Since w_j=a_(j-1)-a_j,

    sum_j (j-1) w_j = sum_(j>=1) a_j <= 1.

Substituting the formula for rho_j proves (3.1). QED.

For example, the strict numerical inequality (3.4) can be checked using only pi<4, sqrt(2)<2, h_0<=lambda, and rational arithmetic:

    4 lambda + 8 lambda/(1/2-lambda)
               + 8 lambda^2/(1/4-lambda^2) < 1/4.

---

## 4. Proof of Theorem A

Translate coordinates so that the containing disk has center zero. The lattice is then possibly a translate of Z^2; (2.2) and (2.3) are unchanged.

Let

    F(r)=S(4r^2),        T=n/F(R),        M=M_disk(P).

If T<=2, (1.1) proves both claimed lower bounds immediately. We may therefore assume T>2. By (2.1), for all sufficiently large R,

    n >= c R^2 / sqrt(L),                               (4.1)

where c>0 is absolute. Small bounded R will be handled at the end.

### 4.1 Balanced disks and a generic translation

Set

    a=R/L,       R_*=R+a,
    h_0=min(2^(-10), sqrt(n)/(100 R_*)).

Use Lemma 3.1 in a disk of radius R_*. Its physical stage-j radii are

    r_j=R_* rho_j.

The largest radius obeys r_1<=sqrt(n)/200. Thus every one of these disks, regardless of its center, contains at most n/2 lattice points, by (2.2). One completely numerical check valid for n>=4 is

    pi (1/200 + sqrt(2)/(2sqrt(n)))^2
       <= (22/7)(1/200+5/14)^2 < 1/2.                    (4.2)

Consequently every selected Q with at least two points is an admissible disk cut.

By (4.1),

    h_0 >= c_1 L^(-1/4).                                (4.3)

Let J be the largest stage with r_J>=sqrt(R). Such a stage exists for all sufficiently large R. Translate the entire finite packing through a vector z chosen uniformly from the disk of radius a. Every P remains inside the corresponding containing disk of radius R_*.

For each fixed p in P, the set of translations for which p lies in the residual uncovered part has area at most the residual area pi R_*^2 2^(-J). Therefore some translation leaves at most n epsilon points uncovered, where

    epsilon <= (L+1)^2 2^(-J).                          (4.4)

We may choose this translation away from the finitely many measure-zero conditions that put a point of P on a packing-circle boundary. For that choice the intersections with the closed disks are disjoint.

Let alpha=1/10, so lambda^alpha=1/2. Since r_(J+1)<sqrt(R),

    2^(-J)=(lambda^J)^alpha
       < (2sqrt(R)/(R_* h_0))^alpha.

Together with (4.3), this gives the uniform estimate

    epsilon <= C L^(2+1/40) R^(-1/20).                  (4.5)

### 4.2 Adding the actual support capacities

Each packing disk used has radius at least sqrt(R). If its intersection Q has at least two points, then

    |Q| <= M D(Q) <= M F(r_j).

If it has zero or one point, the same last inequality still holds because M>=2 and F(r_j)>=1. Summing over the finite packing,

    n(1-epsilon) <= M sum_(j<=J) N_j F(r_j).             (4.6)

This is where the proof keeps the actual distance count D(Q). It is not an energy estimate. In fact M in this part of the argument can be replaced by the maximum of 2 and the actual ratios of the finitely many nontrivial packing intersections. Thus a good cut can be selected from those disks and a closest-pair disk; the argument is not just a condition on an unknown global maximizer.

For sqrt(R)<=r<=r_1, (2.1), and the elementary bound for (1-u)^(-1/2) on 0<=u<=1/2, imply

    F(r) <= (4 kappa r^2 / sqrt(L))
               * [1 + C(1+log(R/r))/L].                 (4.7)

The radii are all less than R for large R; also log(4r^2)>=L/2. Let

    H=sum_(j>=1) w_j log(1/rho_j)
       <= log(2/h_0)+log(1/lambda).

The packing moment gives

    sum_(j<=J) N_j r_j^2 <= R_*^2,
    sum_(j<=J) N_j r_j^2 log(R/r_j) <= R_*^2 H.

Using these in (4.7), and then (2.1) at R, yields

    sum_(j<=J) N_j F(r_j)
       <= F(R) [1 + C(1+H)/L].                          (4.8)

The inflation R_*/R=1+1/L contributes only to the absolute constant in this estimate.

Combining (4.6) and (4.8), and putting x=C(1+H)/L,

    M >= T (1-epsilon)/(1+x).

For large R we have 0<=epsilon<=1, whence

    T^2-M^2 <= 2T^2(epsilon+x).                          (4.9)

### 4.3 Uniformity in the density

By (2.1) and (2.2),

    T^2 <= C delta^2 L,       delta <= C.

The choice of h_0 implies

    1+H <= C[1+log_+(1/delta)].                          (4.10)

The x term in (4.9) is consequently bounded by

    C delta^2[1+log_+(1/delta)].

The epsilon term, using (4.5) and delta<=C, is at most

    C L^(121/40) R^(-1/20).

This proves (1.3). The function delta^2[1+log_+(1/delta)] is bounded for delta in a bounded interval, and L^(121/40)R^(-1/20) is bounded for R bounded below and tends to zero. Hence (1.2) holds for all sufficiently large R.

Finally, for bounded R the lattice-point count is bounded uniformly in the center. Thus T^2 is bounded by an absolute constant depending only on the already fixed absolute threshold. Enlarging C covers all remaining cases. QED.

---

## 5. Proof of Theorem B: arbitrary fourth-class restoration

Let b be the missing parity class. Fix a nonzero v in Z^2. There is a parity class u such that both u and u+v are different from b: at most two of the four possible u are forbidden.

Choose p in u+2Z^2 nearest to c_0-v/2. The covering radius of this lattice coset is sqrt(2), so

    |p-(c_0-v/2)| <= sqrt(2).

Both p and p+v lie in the three-class base whenever

    |v| <= 2R-2sqrt(2).

Indeed, both have distance at most |v|/2+sqrt(2) from c_0, and both have permitted parity. Consequently, for R>=sqrt(2),

    S((2R-2sqrt(2))^2) <= D(P) <= S(4R^2).              (5.1)

In particular,

    0 <= S(4R^2)-D(P) <= C R,                           (5.2)

simply by counting the integers in the intervening interval. No angular equidistribution of representations is needed.

Since n<=C R^2, (2.1) and (5.2) imply

    0 <= Phi(P) - (n/S(4R^2))^2
       <= C (log(4R^2))^(3/2)/R                         (5.3)

for large R. Combining (5.3) with Theorem A proves (1.4). Bounded R is again absorbed into the same absolute constant.

**Why this is stronger than the annulus audit:** a restoration E can be scattered at single-point scale throughout the disk, so there need not be any large fully restored patch. The packing-and-averaging argument handles that situation directly. It also handles arbitrarily many nested or interleaved restoration scales. QED.

---

## 6. Proof of Theorem C: sparse random lattice disks

A useful elementary support fact is the following.

### Lemma 6.1

For R sufficiently large and every nonzero v in Z^2 with |v|<=2R-10, the graph on G_R with edges {p,p+v} contains at least c sqrt(R) pairwise vertex-disjoint edges, where c>0 is absolute.

### Proof

Put a=|v|/2 and use orthonormal coordinates parallel and perpendicular to v, centered at -v/2. The rectangle

    |u|<=1,       |w|<=sqrt(R)

lies in

    closedDisk(0,R-1) intersect closedDisk(-v,R-1).

Indeed a<=R-5, and for either center the squared distance is at most

    (a+1)^2+R <= (R-4)^2+R <= (R-1)^2

for large R. Its area is 4sqrt(R). Associate each point of this rectangle to the center p of its unit lattice square. Since the square's covering radius is less than 1, both p and p+v belong to G_R. The unit squares partition the rectangle, so there are at least 4sqrt(R) such lattice p.

The translation graph has maximum degree two. A greedy matching takes at least one third of its edges, giving the assertion. QED.

If points are independently retained with probability theta, the probability that a particular such v disappears from P-P is at most

    exp(-c theta^2 sqrt(R)).

There are O(R^2) possible v. Hence, provided

    theta^2 sqrt(R) / log R -> infinity,

a union bound shows, with probability tending to one, that

    {v in Z^2 : |v|<=2R-10} subset P-P.

On this event,

    S((2R-10)^2) <= D(P) <= S(4R^2),
    S(4R^2)-D(P)=O(R).                                  (6.1)

For theta=L^(-1/4), the probability condition holds. Standard Bernoulli concentration and the unit-square disk estimate give

    n=(1+o(1)) pi R^2 L^(-1/4).

Equations (2.1) and (6.1) give the asserted asymptotics for D and Phi. Applying (1.3), with delta=n/R^2 asymptotic to pi L^(-1/4), yields

    (n/S(4R^2))^2-M_disk(P)^2
       <= C (log L)/sqrt(L)
          + C L^(121/40)R^(-1/20).

The difference between Phi(P) and (n/S(4R^2))^2 is o(1), by (6.1) and the same computation as (5.3). This proves (1.5).

More generally, the same conclusion holds if theta_R->0 and theta_R sqrt(log R)->infinity. These conditions ensure both the needed difference-vector coverage and unbounded K(P_R). QED.

---

## 7. What is still missing for the requested universal criterion

The exact missing comparison is not hidden in a new hypothesis:

- For arbitrary lattice P, one may have D(P) substantially smaller than S(4R^2).
- Theorem A controls n/S(4R^2), which can then be substantially smaller than n/D(P).
- For the three-class family and the random family, actual endpoint realizations prove D(P)>=S(4R^2)-O(R), closing that gap.
- There is no corresponding lower comparison for an arbitrary planar set, nor a proof here that some alternative lattice or scale always supplies it.

Scaling rational coordinates into Z^2 does not fix this problem: the required containing radius in lattice units can become enormous, and the ambient capacity can be a very poor approximation to the actual distance support. Nor does replacing support by an energy or a positive-order distance entropy fix the direction of the inequality.

Thus this work supplies unconditional inequalities and rules out broad genuine geometric counterexample families, but it does **not** settle the universal disk criterion.

## 8. Verification artifacts

`verify_disk_capacity_localization.py` and `disk_capacity_verification.txt` accompany this note. They check the packing constants with rational arithmetic, the parity endpoint realization, the random-sampling matching gadget, and finite off-center disk cuts in several restoration patterns. These are checks of the proved statements and implementations, not a numerical claim about all planar sets or all disks in an untested family.

The full verification run passed. It includes 19,200 exact rational endpoint realizations, 44 exact whole-support containments, 6,640 displacement-graph counts, 120 disjoint matchings, and 212,592 integer-center/radius disk candidates across 24 restoration sets up to radius 128 (51,433 points). Global and selected-subset distance counts are computed exactly using carry-free integer polynomial multiplication, checked against brute force on 64 small arrays and an explicit larger-digit test. The largest certified *upper* defect for this finite restoration list was 1.422717. This is not a proposed universal constant and not an exhaustive optimization over all disks. Three reproducible sparse samples also had every required inner difference vector.

No claim of historical priority is made for these lemmas.
