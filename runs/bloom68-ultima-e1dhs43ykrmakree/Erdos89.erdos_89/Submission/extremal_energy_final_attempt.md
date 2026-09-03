# Extremal selection in separated grids: a genuine but restricted comparison

## Status and independent audit

The universal inequality `E(P) >= c |P| I(P)` on hereditary ratio-extremal
planar sets remains unresolved. The sharp distinct-distances conjecture is
also unresolved. No Lean file was changed.

A focused research investigation produced the results below. The parent
independently checked the palette disjointness, translation multiplicities,
all parameter exponents, the EXT argument, and the endpoint-consistent
rotation proof of the dense-grid lemma. These are mathematical arguments,
not Lean-certified theorems. In particular, none may be used as an
unconditional proof of either declaration in `Spec.lean`.

The new result is that a reparameterized version of the known separated-grid
counterexample cannot retain a large proportion of its points under EXT
selection. Moreover, every EXT subset of positive block-scale density obeys
the energy comparison. The unresolved case consists of much smaller EXT
subsets; their existence and energy ratios are not controlled here.

## 1. Definitions

For a finite planar set P, use positive squared-distance labels s and ordered
multiplicities:

```
n = |P|,             D = number of labels,       K = n/D,
k_ps = #{q in P : |p-q|^2=s},
r_s = sum_p k_ps,
I(P) = sum_{p,s} k_ps(k_ps-1),
E(P) = sum_s r_s^2.
```

EXT means `|Q|/D(Q) <= K` for every actual subset Q of P with at least two
points. In particular, EXT implies K>=2 by considering any pair. The exact
maximizer of K over the nontrivial subsets of a finite set exists and has EXT,
but its energy ratios need not resemble those of the original set.

## 2. A general block-palette inequality

Let an EXT set Q be partitioned into blocks Q_i, with q_i=|Q_i|, q=|Q|, and
K_Q=q/D(Q). Suppose that no cross-block distance belongs to any internal
block palette. Let S_i be the internal palette of Q_i and let

```
L >= sum_{i<j} |S_i intersect S_j|,
u = number of singleton blocks,
R = q^2 - sum_i q_i^2,
E_cross = sum_{cross labels s} r_s(Q)^2.
```

Then

```
D_cross(Q) <= L + u/K_Q,
R^2 <= (L + u/K_Q) E_cross.                         (2.1)
```

Indeed, EXT gives `D(Q_i)>=q_i/K_Q` for every nonsingleton block, so
`sum_i |S_i| >= (q-u)/K_Q`. For any finite family of sets,

```
|union_i S_i| >= sum_i |S_i| - sum_{i<j}|S_i intersect S_j|;
```

a label occurring h times has h-1 surplus occurrences, at most binom(h,2).
Subtract the union of internal palettes from `D(Q)=q/K_Q`, using the assumed
disjointness from cross colors. This proves the first inequality. The ordered
cross multiplicities sum to R, so Cauchy--Schwarz proves the second.

The cross/internal disjointness is essential. In arbitrary abstract EXT
colorings, cross edges can reuse internal colors, and this proof does not
apply. In the following construction, Euclidean separation proves the
hypothesis, while arithmetic controls E_cross and L.

## 3. Reparameterized actual planar construction

For sufficiently large integers m, set

```
T=m^8,      M=2^(m^44),      B_i=4m^2 i+i^2       (0<=i<m).
```

Choose distinct primes p_i in [T,2T], all congruent to 3 modulo 4. The prime
number theorem in this fixed progression ensures their existence for large
m. Define

```
P_i = (32 T M B_i,0) + p_i {0,...,M-1}^2,
P = union_i P_i,
n = m M^2.
```

The previously proved grid and representation estimates in
`pinned_degree_comparison_counterexample.md`, Sections 2--5, give

```
D(P) << M^2 = n/m,
I_p(P) ~ M^2 log M       uniformly for every actual pin,
I(P) ~ m M^4 log M,
E(P) ~ m M^6 log M,
E(P)/(n I(P)) ~ 1/m.                                  (3.1)
```

Here and throughout this note, implicit constants are absolute. The symbol
`~` in (3.1) denotes comparison above and below by constants, not asymptotic
ratio one. The D estimate follows because all squared distances are at most
`X=(200 T M m^3)^2`, and the Landau--Ramanujan upper bound gives

```
D(P) << X/sqrt(log X) << m^(6+16-22) M^2 = M^2.
```

The previous pin estimates depend on the ratios p_i/p_j, which remain
bounded, and the large fixed-form separations B_j-B_i. They apply to these
parameters. Likewise, the previous energy bounds give the two-sided energy
estimate in (3.1); the sharper cross-energy bound below is more than enough
for its upper bound.

## 4. Geometry separates every cross-block palette

For i<j, writing d=j-i gives

```
B_j-B_i = 4m^2 d + d(i+j),        0<d(i+j)<2m^2.
```

Different d give disjoint intervals, and for fixed d the expression strictly
increases with i. All these positive integer differences are distinct.
Every cross-block length between P_i and P_j lies within 6TM of
`32TM(B_j-B_i)`. The intervals for different unordered pairs are disjoint,
since their centers are at least 32TM apart. They are also disjoint from
all internal lengths, which are less than 3TM.

Thus a cross-block color determines its unique unordered block pair. It can
never be an internal color. These conclusions remain true for all subsets.

For a fixed difference vector and a fixed ordered pair of blocks, solve in
each coordinate

```
p_i a - p_j b = fixed integer,       0<=a,b<M.
```

Coprimality implies at most `1+M/max(p_i,p_j)<=2M/T` solutions per coordinate.
For the unique unordered pair supporting a given norm label, including both
orientations therefore gives

```
r_s_cross(P) <= (8M^2/T^2) r_2(s).
```

With the previously proved `sum_{s<=X}r_2(s)^2 << X log X`, this yields

```
E_cross(P) << (m^6/T^2) M^6 log M << m^34 M^6.          (4.1)
```

This is sharper than the bound obtained by summing multiplicities over all
block pairs before imposing the norm label.

## 5. Internal palette overlaps are small

For distinct i,j, a common internal squared distance has the form

```
s = p_i^2 p_j^2 t,
0<t<=2M^2/T^2,
t is a sum of two integer squares.
```

This uses inertness: for p congruent to 3 modulo 4, divisibility of a sum of
two squares by p forces both coordinates to be divisible by p. The
Landau--Ramanujan upper bound therefore gives, for the full internal palettes,

```
L := sum_{i<j}|S(P_i) intersect S(P_j)|
   << m^2 M^2/(T^2 sqrt(log M))
   << M^2/m^36.                                      (5.1)
```

Here log(M/T) and log M are comparable with absolute constants for large m.
Every subset has no larger overlap sum.

## 6. Every EXT subset retains at most one block's scale

Let Q be any EXT subset of P, with q>=2 and q_i=|Q intersect P_i|. Let u be
the number of its singleton blocks. Apply (2.1), (4.1), and (5.1). Since
K_Q>=2 and u<=m,

```
R^2 <= (L+m/2) E_cross(P)
    << (M^2/m^36 + m) m^34 M^6
    << M^8/m^2.
```

The singleton term is absorbed because `m^37 <= M^2` for large m. Hence

```
q^2 - sum_i q_i^2 <= C M^4/m.                         (6.1)
```

Since q_i<=M^2 and also q_i<=max_j q_j,

```
q(q-M^2) <= R,
q(q-max_i q_i) <= R.
```

It follows that

```
q <= (1+C/m)M^2,
q-max_i q_i <= C M^4/(m q).                           (6.2)
```

For the first inequality, the case q<=M^2 is immediate; otherwise divide
q(q-M^2)<=CM^4/m by q>=M^2. Thus every exact ratio-maximizing subset of P
retains at most `1/m+O(1/m^2)` of the original set. If q>=epsilon M^2, its
points outside the largest block number at most
`C M^2/(epsilon m)`.

This conclusion applies to the displayed reparameterization, not
quantitatively to the old choice `T=m^5, M=2^(2^m)`.

## 7. Endpoint-consistent dense-grid energy lemma

If `A subset {0,...,M-1}^2` has `a=alpha M^2` points and alpha M is
sufficiently large, then

```
E(A) >> alpha^4 M^6 log(alpha M).                     (7.1)
```

Proof. Identify the plane with C. For every primitive positive Gaussian
integer w=b+ic (b,c>0, gcd(b,c)=1), use the rotation
`R_w(z)=(w/conjugate(w))z`. For translations t put

```
f_w(t) = #{x in A : R_w(x)+t in A}.
```

The sum over occurring t is a^2. Every such t satisfies

```
conjugate(w)t = conjugate(w)y-wx in Z[i],
|conjugate(w)t| <= C M |w|.
```

Thus at most `C M^2 |w|^2` translations occur. Cauchy--Schwarz gives

```
sum_t f_w(t)(f_w(t)-1)
 >= a^4/(C M^2 |w|^2) - a^2
 >> a^4/(M^2 |w|^2)                                  (7.2)
```

when `|w|<=c_0 alpha M`, with c_0 an absolute sufficiently small constant.
Distinct primitive positive w determine distinct rotations. Two ordered
distinct source points and their two targets determine a unique
orientation-preserving motion. Consequently the terms (7.2), as w varies,
count disjoint subsets of the actual equal-distance quadruples. There is no
abstract motion-table assumption and no inconsistent endpoint reuse.

Finally

```
sum_{w primitive positive, |w|<=H} |w|^(-2) >> log H.
```

For an elementary justification, among positive pairs in [1,N]^2, at most
`N^2 sum_{d>=2} d^(-2) < (2/3)N^2` have a common divisor. At least N^2/3
are primitive. Removing [1,floor(N/2)]^2 leaves at least N^2/12 primitive
pairs in a dyadic square shell; each has norm squared at most 2N^2. Summing
disjoint dyadic shells proves the logarithmic bound. Sum (7.2) to obtain
(7.1).

## 8. Comparison for macroscopic EXT subsets

Fix epsilon>0. If an EXT subset Q as above has `q>=epsilon M^2`, then (6.2)
gives a block containing at least q/2 points for sufficiently large m.
Undo the block's similarity and apply (7.1); since its relative density is
at least epsilon/2, `log(alpha M)` is comparable to log M. Therefore

```
E(Q) >> (q^4/M^2) log M.
```

The uniform full-set pin bound in (3.1) gives

```
I(Q) <= sum_{p in Q} I_p(P) << q M^2 log M.
```

Combining the inequalities proves

```
E(Q) >= c epsilon^2 q I(Q).                           (8.1)
```

## 9. Exact unresolved boundary

An exact maximizing subset could have `q=o(M^2)`. Neither (6.2) nor (7.1)
controls its normalized energy by an absolute constant, and no macroscopic
density lower bound for such maximizers has been proved. Thus this report
provides neither a general EXT comparison nor an actual EXT counterexample.

Even a proof of the general comparison would leave the separately unproved
amplification `(I+n^2)D^2 >= c n^4`, and the required incidence theorem, before
reaching the sharp original statement. No such step is asserted here.

## 10. Logarithmic records give an entropy correction, not a closing bound

The new Lean theorems in `HereditaryReduction.lean` formally justify selecting
an actual subset Q maximizing `K(Q)^2-A log|Q|`. For A>=0 this subset is EXT
and, writing n=|Q| and K=K(Q), every nontrivial R subset Q satisfies

```
K(R)^2 <= K^2 - A log(n/|R|).
```

There is a quantitative refinement of (2.1). For a partition Q_i with the
same cross/internal palette disjointness as in Section 2, let u count its
singleton blocks and let L bound its internal palette-overlap sum. Then

```
D_cross(Q) <= L + u/K
              - A/(2K^3) sum_{i:q_i>=2} q_i log(n/q_i).       (10.1)
```

Here is the direct algebraic proof of the extra term. For q_i>=2 put
x=K(Q_i)>0 and t=A log(n/q_i)>=0. The record condition gives
`x^2<=K^2-t` and hence x<=K. Therefore

```
K-x = (K^2-x^2)/(K+x) >= t/(2K),
1/x-1/K = (K-x)/(Kx) >= t/(2K^3).
```

Multiplying by q_i gives
`D(Q_i)>=q_i/K + A q_i log(n/q_i)/(2K^3)`. Sum over nonsingleton blocks,
subtract the overlap bound L, and then subtract the internal palette union
from `D(Q)=n/K`, exactly as in Section 2. This proves (10.1). With no
singletons, its extra sum is n times the Shannon entropy of the block-size
proportions (using natural logarithms).

This is still a restricted block statement. It supplies no universal upper
bound on L, no general cross/internal palette separation, and no control of
color-specific pin variance for an arbitrary planar set. Consequently the
stronger record hypothesis does NOT presently close the energy comparison
or the distinct-distances conjecture. The algebra in (10.1) is not itself
Lean-formalized; only the exact record-selection and EXT consequences are.
