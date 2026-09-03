# Support-weighted actual lenses: exact identities and a chord-charging obstruction

## Status

**No proof of the sharp Erdős bound, and no proof or counterexample to universal disk contraction, is obtained here.** In particular, the invalid three-parity-class/restored-annulus counterexample is not used or reinstated. The proved results in `disk_capacity_localization.md` are unchanged.

This note supplies a precise failure analysis of a natural weighted endpoint-charging implementation, together with finite support-retaining inequalities:

1. **Inverse-square regularization retains the balanced support lower bound.** Weight each actual equal-distance triple by `(m/(d k))^2`, where `k` is its entire actual circle-fiber size and `d` bounds the pinned supports. This gives the same finite Jensen lower bound as the unweighted third moment, while its aggregate on ordinary grids is `Theta(n^2 log n)`, not `Theta(n^2 log^3 n)`.
2. **Both proposed unnormalized weights have exact disjoint-witness realizations and exact longest-chord disintegrations.** The weight `1/k^2` counts approximately incidence mass; `1/binom(k,3)` counts rich center-radius fibers, not global distance colors. The additional normalization needed to count global rich colors is stated explicitly.
3. **A uniform budget for each longest chord is false even on full unit grids with unbounded `K(P)`.** One fixed chord receives `L^(1-o(1))` weight under *each* of `1/k^2` and `1/binom(k,3)`, whereas `K_max^2=O(log^2 L)` follows already from Guth–Katz. This calculation retains every actual fiber multiplicity. It is not the old unweighted third-moment obstruction.
4. **There is an exact, nonconstant correction to the squared ratio.** The natural normalized inverse-square statistic equals `K(P)^2-Gamma`. On the same full grids, `Gamma=Theta(K(P))=Theta(sqrt(log n))`. Dropping this as a lower-order term does not prove constant-loss contraction.
5. **A finite integral-rotation-net lemma proves uniform pinned support in macroscopic shifted lattice disks.** This justifies the last grid assertion without assuming angular equidistribution of sum-of-two-squares representations.

The chord obstruction does **not** refute a global amortized budget, adaptive nonuniform choices of witnesses, or weights retaining additional global-color occurrence information. Those remain possible directions. No historical-priority claim or Lean formalization is made.

---

## 1. Setup and actual geometric witnesses

For a finite planar set `P`, let `D(P)` count distinct positive distances, equivalently positive squared distances. Put

\[
 n=|P|,\qquad K(P)=n/D(P),
\]

and, for `n>=4`,

\[
 M=M_{\rm disk}(P)
 =\max_{\substack{Q=P\cap\overline B(x,t)\\2\le |Q|\le n/2}}
       \frac{|Q|}{D(Q)}.
\]

The closest-pair diameter disk selects exactly that pair, so `M>=2`.

Let

\[
 A\subset\overline B(c,r),\qquad
 B\subset\{p:|p-c|\ge R\},\qquad R>r,
 \qquad m=|A|\ge1,\ s=|B|\ge1.
\]

When applying a local-ratio bound, `A` must really be an admissible disk intersection with `P`, not an arbitrary subset of a disk. The identities below only need containment and separation.

For a squared distance `delta`, write

\[
 A_{p,\delta}=\{a\in A:|a-p|^2=\delta\},\quad
 k_{p,\delta}=|A_{p,\delta}|,\quad
 d_p=|\{\delta:k_{p,\delta}>0\}|,\quad
 H_p=\sum_{\delta:k_{p,\delta}>0}\frac1{k_{p,\delta}}.
\]

Let `T_B(A)` denote the collection of unordered triples from `A` whose circumcenter belongs to `B`. For `T` in this collection its actual center `p(T)`, radius squared `delta(T)`, and **full** fiber size

\[
 k_T=k_{p(T),\delta(T)}
\]

are uniquely determined. In particular, `k_T` is not replaced by `3`, a mean fiber size, or a maximal-multiplicity upper bound in any identity below.

### Longest-chord geometry

All points of a fiber lie on an arc of angular length less than `pi`, as seen from the exterior center. Consequently a triple has a unique longest chord `a b`, and the third point `z` lies between its endpoints in that arc order. If `l=|a-b|`,

\[
 t=\frac{(z-a)\cdot(b-a)}{l^2},\qquad
 v=\operatorname{dist}(z,\operatorname{line}(a,b)),
\]

then

\[
 0<t<1,\qquad 2(R-r)v\le l^2t(1-t).                 \tag{1.1}
\]

Indeed, in chord coordinates the center is `(0,H)`, with `|H|>=R-r` because the chord midpoint is in the containing disk. The minor-arc point is on the opposite side of the chord from the center. Its circle equation is

\[
 x^2+v^2+2|H|v=l^2/4.
\]

This proves (1.1). Three distinct circle points are noncollinear, and a noncollinear triple has one circumcenter. Thus the triple collections of distinct `(p,delta)` are disjoint. This is the actual-center, actual-endpoint statement used throughout.

---

## 2. Exact support-sensitive weights

Define

\[
 U_2(A,B)=\sum_{T\in T_B(A)}\frac1{k_T^2},\qquad
 U_0(A,B)=\sum_{T\in T_B(A)}\frac1{\binom{k_T}{3}}.
\]

### Proposition 2.1: exact formulas

\[
 \boxed{\quad
 6U_2=sm-3\sum_{p\in B}d_p+2\sum_{p\in B}H_p.
 \quad}                                                       \tag{2.1}
\]

Also,

\[
 \boxed{\quad
 U_0=\sum_{p\in B}|\{\delta:k_{p,\delta}\ge3\}|.
 \quad}                                                       \tag{2.2}
\]

**Proof.** A fiber of size `k` supplies exactly `binom(k,3)` distinct triples. For every positive integer `k`, including `1,2`,

\[
 \frac{\binom k3}{k^2}=\frac{k-3+2/k}{6}.
\]

Sum this identity and use `sum_delta k_{p,delta}=m`. For (2.2), each rich fiber contributes exactly one. QED.

Thus `1/k^2` does **not** make every circle contribute one: it makes a large circle contribute approximately `k/6`. Conversely, `1/binom(k,3)` ignores fibers of size one or two and counts center-radius incidences, not their union of radii.

### Counting actual global colors, with all dependence retained

Put

\[
 t_\delta=|\{p\in B:k_{p,\delta}\ge3\}|,
 \qquad \Delta_{\ge3}=\{\delta:t_\delta>0\}.
\]

Then the exact global support identity is

\[
 \boxed{\quad
 \sum_{T\in T_B(A)}
    \frac1{t_{\delta(T)}\binom{k_T}{3}}
       =|\Delta_{\ge3}|.
 \quad}                                                       \tag{2.3}
\]

The cross palette is the disjoint union of `Delta_{>=3}` and the colors occurring only in fibers of size at most two. Formula (2.3) does not count the latter. In particular, deleting the factor `t_delta` does not preserve global support. It can change the answer by a factor as large as `s`.

### Theorem 2.2: finite inverse-square cross-distance inequality

Let `d` be a positive integer with `d_p<=d` for every `p`. For example one may take `d=D(A,B)`, or `d=D(P)` when `A,B` are subsets of `P`. If `m>2d`, then

\[
 \boxed{\quad
 s\frac{m(m-d)(m-2d)}{6d^2}
 \ \le\ \left(\frac md\right)^2 U_2(A,B)
 \ \le\ \frac{s m^3}{6d^2}.
 \quad}                                                       \tag{2.4}
\]

The left-hand side is exactly the finite Jensen lower bound supplied by the unweighted third moment. Its right-hand statistic now uses the actual weights

\[
 \left(\frac{m}{d\,k_T}\right)^2.
\]

**Proof.** Cauchy–Schwarz within one row gives `H_p>=d_p^2/m`. By (2.1),

\[
 \sum_\delta\frac{\binom{k_{p,\delta}}3}{k_{p,\delta}^2}
 \ge \frac{(m-d_p)(m-2d_p)}{6m}
 \ge \frac{(m-d)(m-2d)}{6m}.
\]

The second inequality holds because `(m-u)(m-2u)` decreases for `0<=u<=m/2`. Sum and multiply by `(m/d)^2`. The upper bound follows from `binom(k,3)/k^2<=k/6`. QED.

There is also an exact discrete version valid without `m>2d`. Set `f(0)=0` and `f(k)=binom(k,3)/k^2` for `k>=1`. If `m=qd+u`, `0<=u<d`, then

\[
 U_2\ge s\bigl((d-u)f(q)+u f(q+1)\bigr).             \tag{2.5}
\]

Indeed `f(1)-f(0)=0` and

\[
 f(k+1)-f(k)=\frac16-\frac1{3k(k+1)}\quad(k\ge1)
\]

are nondecreasing. Balancing the `d` bins, including empty ones, minimizes their sum.

**What (2.4) does and does not do.** It removes the lattice's third-moment excess while keeping an inverse squared support in the lower bound. It does not provide a geometric upper bound in terms of `M`, and its elementary upper bound is itself expressed in terms of `d`.

---

## 3. Disjoint witnesses and exact endpoint disintegration

### Proposition 3.1: the proposed weights come from row-disjoint witnesses

For a fixed `p`, independently choose one uniformly random triple from each fiber of size at least three. These triples are vertex-disjoint within that row. Every triple in a size-`k` fiber is selected with probability `1/binom(k,3)`. This realizes the weights of `U_0` exactly.

The weights of `U_2` also have an exact realization. In a size-`k` fiber, take a uniform random permutation, group its first `3 floor(k/3)` points into triples, and retain each triple with probability

\[
 a_k=\frac{\binom k3/k^2}{\lfloor k/3\rfloor}\quad(k\ge3).
\]

Here `1/9<=a_k<=1/2`: use `(k-2)/3<=floor(k/3)<=k/3` and `binom(k,3)/k^2=(k-1)(k-2)/(6k)`. By symmetry, any fixed triple occurs in the initial packing with probability `floor(k/3)/binom(k,3)`, so its final probability is exactly `1/k^2`. The retained triples are still vertex-disjoint within the row.

For different centers, selected triples cannot be identical. Their vertex sets, and particularly their longest chords, **can** overlap. No cross-row vertex-disjointness follows.

### Proposition 3.2: exact longest-chord loads

For `a,b` in a common fiber of center `p`, let `ell_p(a,b)` be the number of fiber points strictly between them in the short-arc order. If they have indices `i<j` in that order, this is `j-i-1`. Define

\[
 \begin{split}
 \Lambda_2(a,b)&=
  \sum_{\substack{p\in B\\|p-a|=|p-b|}}
      \frac{\ell_p(a,b)}{k_{p,|p-a|^2}^2},\\
 \Lambda_0(a,b)&=
  \sum_{\substack{p\in B\\|p-a|=|p-b|\\k_{p,|p-a|^2}\ge3}}
      \frac{\ell_p(a,b)}{\binom{k_{p,|p-a|^2}}3}.
 \end{split}
\]

Then

\[
 \boxed{\quad U_i=\sum_{\{a,b\}\subset A}\Lambda_i(a,b),
              \qquad i\in\{0,2\}.\quad}                       \tag{3.1}
\]

Every term is supported on an actual lens satisfying (1.1), and its center is on the perpendicular bisector of `a b`. Formula (3.1) is an equality: it makes no replacement of fiber sizes by lens populations.

For a single size-`k` fiber, a chord's contribution to `Lambda_0` is at most

\[
 \frac{k-2}{\binom k3}=\frac6{k(k-1)}.                \tag{3.2}
\]

The next section shows why summing these small contributions over actual centers can nevertheless give a very large load on one chord.

---

## 4. A full-unit-grid obstruction to a uniform per-chord budget

### Theorem 4.1

For positive integers `L`, put

\[
 P_L=\mathbb Z^2\cap[-4L,4L]^2,\quad
 A_L=\mathbb Z^2\cap\overline B(0,L),\quad
 B_L=\{p\in P_L:|p|\ge2L\}.
\]

Both `A_L` and `B_L` have cardinality comparable to `n=|P_L|`; `A_L` is an admissible actual disk cut. For the fixed chord

\[
 a=(-L,0),\qquad b=(L,0),
\]

and for every `epsilon>0`, there is a constant `c_epsilon>0` such that, for sufficiently large `L`,

\[
 \boxed{\quad
 \Lambda_0(a,b),\ \Lambda_2(a,b)
       \ge c_\epsilon L^{1-\epsilon}.
 \quad}                                                       \tag{4.1}
\]

On the other hand,

\[
 M_{\rm disk}(P_L)^2=O((\log L)^2).                    \tag{4.2}
\]

Consequently, for `i=0,2`,

\[
 \frac{\Lambda_i(a,b)}{M_{\rm disk}(P_L)^2+1}
       \longrightarrow\infty.                         \tag{4.3}
\]

Thus **neither canonical per-circle weighting admits an absolute `C(M^2+1)` budget for each chord.** Moreover `K(P_L)->infinity`, so this is not just an irrelevant bounded-`K` configuration.

### Proof, retaining the full multiplicities

Consider every integer

\[
 2L\le H\le3L,\qquad H\equiv7L\pmod{25}.
\]

There are at least `floor(L/25)` choices. For each one, the point `p_H=(0,H)` is an actual member of `B_L`. Set

\[
 z_H=\left(\frac{24L-7H}{25},\frac{H-7L}{25}\right).
                                                               \tag{4.4}
\]

The congruence makes both coordinates integers. They satisfy

\[
 3L/25\le (z_H)_x\le10L/25,\qquad
 -5L/25\le (z_H)_y\le-4L/25,
\]

so `z_H` and its reflection across the vertical axis are distinct interior points of `A_L`. Direct calculation gives

\[
 |z_H-p_H|^2=L^2+H^2=|a-p_H|^2=|b-p_H|^2.
\]

Let

\[
 k_H=|A_L\cap\{x:|x-p_H|^2=L^2+H^2\}|.
\]

This is the **entire actual fiber**, and `k_H>=4`. Every point `(x,y)` in this fiber satisfies

\[
 x^2+y^2=L^2+2Hy\le L^2,
\]

hence `y<=0`. The points `a,b` are its two extreme arc points, so

\[
 \ell_{p_H}(a,b)=k_H-2.
\]

In particular, these centers supply the exact contributions

\[
 \Lambda_0(a,b)\ge\sum_H\frac6{k_H(k_H-1)},\qquad
 \Lambda_2(a,b)\ge\sum_H\frac{k_H-2}{k_H^2}.             \tag{4.5}
\]

No size-`4` substitution is made. Instead use the genuine upper bound

\[
 k_H\le r_2(L^2+H^2)\le4\tau(L^2+H^2).
\]

For every `eta>0`, the elementary divisor estimate gives

\[
 k_H\le C_\eta L^\eta                                    \tag{4.6}
\]

uniformly over these `H`, since `L^2+H^2<=10L^2`. For completeness, `tau(N)<=C_epsilon N^epsilon` follows by bounding `e+1<=p^(epsilon e)` for all sufficiently large primes, and absorbing the finite maxima of `(e+1)/p^(epsilon e)` at the remaining primes into one constant.

Combining (4.5)--(4.6), and using `k_H-2>=k_H/2`, yields

\[
 \Lambda_0(a,b)\ge c_\eta L^{1-2\eta},\qquad
 \Lambda_2(a,b)\ge c_\eta L^{1-\eta}.
\]

This proves (4.1). The usual Guth–Katz bound, applied to **every** admissible subset `Q` of `P_L`, gives `|Q|/D(Q)<=C log n`, proving (4.2). Therefore (4.3) follows.

Finally every squared distance in `P_L` is a sum of two squares at most `128L^2`, while every represented positive integer at most `64L^2` is realized by a difference vector of `P_L`. Writing

\[
 S(X)=|\{1\le t\le X:t=u^2+v^2,\ u,v\in\mathbb Z\}|,
\]

we have

\[
 S(64L^2)\le D(P_L)\le S(128L^2).
\]

Landau–Ramanujan gives `D(P_L)=Theta(L^2/sqrt(log L))` and `K(P_L)=Theta(sqrt(log L))`. QED.

### Scope of the obstruction

- The centers and every third point are actual unit-grid points; the disk cut is admissible and the annular gap is `L`.
- The fiber denominators in (4.5) are never discarded. The divisor bound controls them in the direction needed for a **lower** bound on load.
- Multiplying `1/k^2` by `(m/D(P_L))^2`, or by the pinned version `(m/d_p)^2`, does not repair this per-chord claim: these factors are at least one for all sufficiently large `L`.
- A large maximum chord load does not imply an excessive *total* load. It does not refute an averaged or globally amortized inequality.
- The theorem concerns the stated uniform-per-triple weights. It does not show that every nonuniform selection of one triple from each rich circle must have the same overload. Nor does it remove the `t_delta` dependence from (2.3).

### Global-color weighting actually suppresses these particular overloaded circles

For the radii `delta_H=L^2+H^2` used above, the actual rich-center occurrence count satisfies

\[
 t_{\delta_H}\ge cL^2.                                  \tag{4.7}
\]

To prove this, use the three points `b,z_H,z_H'`, where `z_H'` is the reflection of `z_H` across the vertical axis, and translate all three by any integer vector

\[
 v_x\in[-L/4,-L/8],\qquad v_y\in[0,L/8].
\]

The translated point `b+v` has squared norm at most `50L^2/64`. Each translated `z` has coordinate bounds `|x|<=13L/20`, `|y|<=L/5`, so also belongs to `A_L`. Their common center `p_H+v` remains in `P_L`, and its vertical coordinate is at least `2L`, so it belongs to `B_L`. These are three distinct noncollinear points, with radius squared still `delta_H`. The rectangle contains at least `L^2/128` integer translations for `L>=16`, all giving distinct centers. This proves (4.7) with `c=1/128`.

Consequently the contribution of the selected positive centers to the *globally* color-normalized chord load is

\[
 \sum_H\frac6{t_{\delta_H}k_H(k_H-1)}=O(L^{-1}).        \tag{4.8}
\]

For a fixed chord `a b` and radius `delta_H`, the only possible centers are `(0,H)` and `(0,-H)`; including the negative centers changes (4.8) by at most a factor two. Thus the radii used to refute per-circle charging do **not** refute the same budget with the extra `t_delta` factors. The assertion concerns these radii, not all possible radii. Dropping the global-color dependence here would give the wrong conclusion.

---

## 5. A forced-witness example: unique triples do not make chords unique

The following smaller example has bounded `K` and is not a contraction counterexample. It isolates what disjoint witnesses alone can and cannot guarantee.

For `N>=1`, set

\[
 a=(-1,0),\quad b=(1,0),\quad
 z_j=(0,-1/j),\quad p_j=(0,(j-1/j)/2).
\]

Let

\[
 A=\{a,b\}\cup\{z_j:3\le j\le N+2\},\qquad
 B=\{p_j:3\le j\le N+4\},\qquad P=A\cup B.
\]

Then `n=2N+4`, `|A|=|B|=n/2`, and

\[
 A=P\cap\overline B(0,1),\qquad |p_j|\ge4/3.
\]

For `3<=j<=N+2`, the only rich fiber in the row of `p_j` is exactly `{a,b,z_j}`. Its radius is `(j+1/j)/2`; the other `A` points have mutually distinct distances from `p_j`. The two extra exterior centers have only the common size-two fiber `{a,b}` and singleton fibers. Thus

\[
 \Lambda_0(a,b)=N,\qquad \Lambda_2(a,b)=N/9.             \tag{5.1}
\]

Here every rich circle has just one possible triple. Any choice of one triple per rich circle is forced to use this same chord. The rich radii are distinct, so their `t_delta` in (2.3) all equal one.

Nevertheless

\[
 \boxed{M_{\rm disk}(P)=2.}                             \tag{5.2}
\]

To see this, every subset `Q` with at least two points has `D(Q)>=|Q|-1`. If `Q` is on the vertical axis, use its extreme point. Otherwise pin at an included point `a` or `b`: all axis points have different absolute heights, so their distances to this endpoint are distinct. Its distance to the other off-axis endpoint, if included, is `2`, and cannot equal an axis distance since that would require an axis height `sqrt(3)`, whereas all heights are rational. Thus `|Q|/D(Q)<=2`; a closest pair attains `2` with an admissible disk.

Scaling by `2 lcm(3,...,N+4)` turns this into an integer-coordinate configuration with all ratios and incidences unchanged. It is a subset of an integer grid, not a full grid. Theorem 4.1 supplies the separate full-grid, unbounded-`K` obstruction for the canonical weights.

---

## 6. The exact squared-ratio correction cannot be dropped

Now suppose `A,B` are subsets of `P`, and put `d=D(P)`. Define the dimensionless weighted statistic

\[
 \mathfrak W(A,B;P)
       =\frac{6n^2}{s m d^2}\,U_2(A,B).
\]

Proposition 2.1 gives the **exact identity**

\[
 \boxed{\quad K(P)^2=\mathfrak W+\Gamma,\qquad
 \Gamma=\frac{n^2}{s m d^2}
               \sum_{p\in B}(3d_p-2H_p).
 \quad}                                                       \tag{6.1}
\]

Since `H_p<=d_p<=d`, writing `bar d=(1/s) sum_p d_p`,

\[
 K(P)^2\frac{\bar d}{m}
 \le\Gamma
 \le3K(P)^2\frac{\bar d}{m}
 \le\frac{3n^2}{md}.                                    \tag{6.2}
\]

For a macroscopic cut `m>=alpha n`, the last bound is `(3/alpha) K(P)`, not an absolute constant.

### Theorem 6.1: the correction really diverges on the full grids above

For `P_L,A_L,B_L` from Theorem 4.1,

\[
 \begin{split}
 U_2(A_L,B_L)&=\frac{s m}{6}
                  \left(1-O((\log L)^{-1/2})\right),\\
 \left(\frac{m}{D(P_L)}\right)^2U_2(A_L,B_L)
             &=\Theta(n^2\log n).
 \end{split}                                                   \tag{6.3}
\]

Moreover,

\[
 \Gamma=\Theta(\sqrt{\log L})=\Theta(K(P_L)).             \tag{6.4}
\]

Thus the aggregate inverse-square normalization passes the grid's scale test. But replacing `K(P)^2` by `mathfrak W` incurs a genuinely unbounded error even there.

The first two assertions follow immediately from (2.1), `d_p<=D(P_L)=Theta(L^2/sqrt(log L))`, and `m,s=Theta(L^2)`. To prove the lower bound in (6.4), it suffices to establish uniformly for `p in B_L` that

\[
 d_p\ge c L^2/\sqrt{\log L}.                            \tag{6.5}
\]

Here is a finite endpoint-realization proof of this fact.

### Lemma 6.2: an integral rotation net for shifted-disk support

Whenever `p in Z^2`, `r>0`, and

\[
 2r\le |p|\le6r,
\]

one has the explicit finite inequality

\[
 D_p(\mathbb Z^2\cap\overline B(0,r))
 \ge
 S\left(\frac{(|p|+r/16)^2}{65^2}\right)
 -S\left(\frac{(|p|-r/16)^2}{65^2}\right).                \tag{6.6}
\]

Every value on the right has an actual lattice endpoint. The estimate makes no equidistribution assumption.

**Proof.** Identify the plane with the complex numbers. Consider the 36 Gaussian integers of modulus 65. In the first quadrant they are, in circular order,

\[
 (65,0),(63,16),(60,25),(56,33),(52,39),
 (39,52),(33,56),(25,60),(16,63),(0,65),
\]

and reflections give the others. The dot product of consecutive points is at least `4056=(24/25)65^2`. Thus, after dividing by 65, these directions form a `1/7` net of the unit circle in Euclidean distance: the nearest endpoint of each angular gap has squared distance at most

\[
 2-2\sqrt{(1+24/25)/2}
   =2-7\sqrt2/5<1/49.
\]

The final strict inequality follows, for example, from `2*343^2-485^2=73>0`.

If `t` is represented in the interval counted on the right of (6.6), choose a Gaussian integer `v` with `|v|^2=t`. Multiplying `v` by a suitable member `u` of this 36-element set gives a vector `w=uv` whose unit direction is within `1/7` of `-p/|p|`, while

\[
 \bigl||w|-|p|\bigr|\le r/16.
\]

Consequently

\[
 |p+w|\le r/16+(|p|+r/16)/7
          \le 13r/14<r.
\]

The point `a=p+w` is an actual lattice point in the disk, and its squared distance from `p` is `65^2 t`. Distinct `t` give distinct distances. QED.

The standard quantitative Landau–Ramanujan formula

\[
 S(X)=\kappa X(\log X)^{-1/2}(1+O(1/\log X))
\]

applied to the two fixed-proportion endpoints in (6.6) implies a lower bound `c r^2/sqrt(log r)`, uniformly over `2<=|p|/r<=6`, for all sufficiently large `r`. The fixed factor `65^2` only affects the absolute constant and threshold. Since every `p in B_L` has `2L<=|p|<=4 sqrt(2)L<6L`, (6.5) follows. Then (6.2) gives (6.4). This completes the proof of Theorem 6.1.

### Why an `O(K)` loss is not enough

Even if one proved

\[
 \mathfrak W\le M^2+C,
\]

(6.1)--(6.2) would only give, for a fixed macroscopic cut,

\[
 K(P)^2\le M^2+C+C'K(P).
\]

Completing the square yields at best `K(P)<=M+O(1)`. Iterating over half-size cuts gives `K(P)=O(log n)`, not `O(sqrt(log n))`. One must control or exactly compensate `Gamma`; it cannot be erased because it is smaller than the main term.

---

## 7. Exact compensation and the still-missing estimate

There is no algebraic difficulty in compensating for the light fibers. Let

\[
 L_p=\sum_{\delta:1\le k_{p,\delta}\le2}k_{p,\delta},
 \qquad M_p=m-L_p.
\]

If `m>2d`, then `M_p>=m-2d>0`. For an actual triple from a size-`k` fiber of row `p`, assign

\[
 w^*(T)=\frac{m}{M_p}\frac{k}{\binom k3}.
\]

Summing over the triples of that row gives exactly `m`, and hence

\[
 \boxed{\quad
 \frac{n^2}{s m d^2}\sum_{T\in T_B(A)}w^*(T)=K(P)^2.
 \quad}                                                       \tag{7.1}
\]

All factors are explicit and retain the actual multiplicities. But (7.1) is an identity, not an upper bound: proving that its left-hand side is at most `M^2+C` is still the desired geometric theorem.

For the uncorrected weights, a sufficient estimate would be

\[
 \frac{6n^2}{s m d^2}
       \sum_{\{a,b\}\subset A}\Lambda_2(a,b)
  +\frac{n^2}{s m d^2}\sum_p(3d_p-2H_p)
       \le M^2+C.                                      \tag{7.2}
\]

By the exact identities, (7.2) is equivalent to the requested contraction for that set. It is displayed to identify every term that must be paid for, **not** as a new proved hypothesis or an easier theorem in disguise.

There is also a coefficient issue. Since an admissible `A` has `m/d<=m/D(A)<=M`, the elementary bound alone gives

\[
 (m/d)^2U_2\le (sm/6)M^2.
\]

Normalizing it to `K(P)^2` introduces the factor `(n/m)^2`. This does not recover a coefficient-one constant-loss recurrence. A fixed multiplicative comparison `K(P)^2<=C_0 M^2+C`, with `C_0>1`, likewise does not give the requested logarithmic squared-ratio induction.

**Precise remaining task.** A successful continuation needs a genuinely global geometric allocation, possibly also retaining the factors `t_delta` from (2.3), that controls the whole support-normalized sum, includes the light-fiber correction, and pays it against admissible disk ratios with coefficient one and an absolute additive loss. Unique circumcenters and row-disjoint witnesses prove the identities above; they do not provide that allocation. Uniform per-chord charging is ruled out by Theorem 4.1. More adaptive allocation is not ruled out.

This work therefore saves a proved weighted certificate and a precise failed charging step, not a proof of `n<=D(P) sqrt(M^2+C)`.

---

## 8. Verification artifacts and limits

Files:

- `verify_weighted_cross_distance_lenses.py`
- `weighted_cross_distance_verification.txt`

The full run passed. It checks:

- 75 exact balanced-bin minima and the finite inverse-square lower bound;
- exact disjoint-witness probabilities by all permutations through fiber size seven;
- independent actual-triple and endpoint enumerations, including a support change at displacement `10^(-40)`;
- the distinction between rich row colors and rich global colors, with the full `t_delta` factor;
- the forced-chord construction, including integer rescaling and 4,387 exhaustive small-subset support checks;
- 520 **complete** actual circle fibers in full unit grids, through `L=6400`, retaining each full `k_H` in both weights, plus 2,080 rectangle-corner checks certifying the rich-center translation lower bounds in (4.7);
- aggregate weighted identities and the exact correction for 108,868 exterior grid rows, using the exact `D4` symmetry of the centered disk;
- a 36-element integral rotation net of common modulus 65, 1,000 exact rational net checks, and 548 explicit integer endpoint realizations for the shifted-disk support lemma.

For example, at `L=6400` the 257 selected exterior centers alone give lower chord loads `27.263485...` for `Lambda_0` and `21.667553...` for `Lambda_2`; the largest actual cap fiber in that test has size 26. The associated grid has 2,621,542,401 points, but the program does **not** enumerate that entire grid: it enumerates each relevant circle cap completely using its exact integer equation. Small-grid aggregate tests separately enumerate all pinned row multiplicities up to symmetry.

The asymptotic divergence in Theorem 4.1 is proved using the divisor bound, not extrapolated from these small loads. Similarly, the asymptotic correction in Theorem 6.1 uses the proved endpoint realization and Landau–Ramanujan, not a fit to the finite table. No finite disk search or purported optimization of `M_disk` is used. Guth–Katz is used only to upper-bound `M_disk` when refuting the proposed edgewise budget, not as a replacement for the requested support-sensitive upper bound.
