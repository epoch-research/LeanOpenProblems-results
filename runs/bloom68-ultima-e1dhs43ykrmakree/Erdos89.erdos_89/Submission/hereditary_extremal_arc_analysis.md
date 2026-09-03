# Hereditary ratio extremality and energy-adaptive circle-arc pruning

## Status: the requested extremal yes/no question remains unresolved

**This investigation does not prove AP for hereditary ratio-extremal planar sets, and does not construct an asymptotic AP counterexample certified to satisfy that restriction.** In particular, none of the lattice subsets below is silently asserted to be a ratio maximizer. The sharp distinct-distances conjecture and the proposed record-maximizer repair are not resolved here.

There is a substantive obstruction more directly relevant to the proposed repair than the thin-rectangle example:

> **Uniform actual-arc theorem.** Let `G_L = {0,...,L-1}^2` and let `P_L` be **any** subset of `G_L`, of size `n_L`, such that
> \[
> \frac{n_L\log\log L}{L^2}\longrightarrow\infty.
> \]
> Then `D(P_L)/n_L -> 0`, the actual arc mass is `(1-o(1)) n_L^2`, and, for every fixed `C>0`,
> \[
> \frac{M_{\lceil C E(P_L)/n_L^3\rceil}(P_L)}{n_L^2}\longrightarrow0.
> \]
> This includes square grids and all fixed-positive-density subsets of them. It uses the entire actual circle fibers of `P_L`, not the fibers or circular order of a containing grid.

Thus replacing a thin rectangle by a square or by an arbitrary dense lattice subset does **not** repair AP. The theorem does not require angular equidistribution of representations of integers as sums of two squares; its proof is in Sections 4–5.

Here is its precise consequence for **genuine** extremal selections. Choose an exact maximizer

\[
Q_L\in\operatorname*{argmax}_{Q\subseteq G_L,\ |Q|\ge2}\frac{|Q|}{D(Q)}.
\]

These sets really are hereditary ratio-extremal and have `D(Q_L)/|Q_L| -> 0`. **If AP on the hereditary-extremal class is true with fixed constants, then every such choice must satisfy**

\[
\boxed{|Q_L|=O\!\left(\frac{L^2}{\log\log L}\right).} \tag{0.1}
\]

The implied constant can depend on the AP constants. Conversely, an extremal family with `|Q_L| log log L / L^2 -> infinity` would be a genuine counterexample. **Existence of such an extremal family is not proved.** No lower bound of that strength for the sizes of the maximizers is supplied by ratio maximality, Guth–Katz, or the results in the two requested input files.

The distinction between this conditional sparsity consequence and an actual extremal counterexample is essential. Sections 2–3 and 6–7 identify the remaining gap precisely. No dense-core or bounded-rank assertion is used.

---

## 1. Definitions and the precise AP target

For a finite planar set `P`, write

\[
n=|P|,\quad S(P)=\{|a-b|^2:a,b\in P,\ a\ne b\},\quad D=|S(P)|,
\]
\[
r_s=|\{(a,b)\in P^2:|a-b|^2=s\}|,\qquad
E=\sum_{s>0}r_s^2,\qquad K(P)=n/D.
\]

All distance multiplicities are ordered. Arc endpoints are unordered.

For each `p in P` and `s>0`, use the **whole** fiber

\[
F_{p,s}=\{a\in P:|a-p|^2=s\}.
\]

For at least three points retain consecutive circular gaps of angle at most `pi`; for two points retain one minor arc, with either choice allowed when the points are antipodal; for a singleton retain none. Let `mu_ab(P)` count the resulting arcs with endpoint pair `{a,b}`, including their actual centers. Set

\[
M_T(P)=\sum_{\{a,b\}\subset P}\min(\mu_{ab}(P),T).
\]

As in the supplied counterexample, if `A(P)` denotes the full arc multiset, then

\[
n(n-1)-nD\le |A(P)|\le n(n-1). \tag{1.1}
\]

Indeed a size-`k` fiber contributes at least `k-1` arcs, and there are at most `nD` nonempty fibers.

The restriction at issue is

\[
\boxed{K(Q)\le K(P)\quad\text{for every }Q\subseteq P,\ |Q|\ge2.} \tag{EXT}
\]

The proposed `AP_EXT` asks for absolute `C,c>0` such that, along every such family with `K(P) -> infinity`,

\[
M_{\lceil CE/n^3\rceil}(P)\ge c n^2
\]

eventually. A finite formulation with an additional absolute lower threshold on `K(P)` would also suffice for the intended application.

---

## 2. What extremal selection legitimately gives

### 2.1 Reduction of the sharp conjecture

For each fixed finite `P_0`, an exact ratio-maximizing nontrivial subset exists, since there are finitely many subsets. Call it `P`. Then `P` satisfies EXT, `K(P)>=K(P_0)`, and `|P|<=|P_0|`.

Consequently, for any fixed `B>0`,

\[
K(P_0)^2>B\log|P_0|
\quad\Longrightarrow\quad
K(P)^2>B\log|P|. \tag{2.1}
\]

Thus proving the sharp bound on EXT sets suffices. This is a reduction for the **distance bound**; it does not assert preservation of either `E/n^3` or the capped arc statistic under the selection.

The low-distance extremal class is nonempty asymptotically. Square grids give

\[
K(G_L)\gg\sqrt{\log L},
\]

by the sums-of-two-squares upper bound. Hence every exact maximizer `Q_L` appearing in the status section satisfies

\[
K(Q_L)\ge K(G_L)\longrightarrow\infty.
\tag{2.2}
\]

In particular `|Q_L| -> infinity` and `D(Q_L)/|Q_L| -> 0`. What is not automatic is a useful density lower bound inside `G_L`.

### 2.2 Why AP_EXT would suffice

For completeness, the constants and the crossing-lemma threshold matter here. A multiplicity-`T` subgraph with `e=M_T` edges has the actual arc drawing. Interiors contain no points of `P`, by full-fiber consecutiveness. Arcs on one circle have disjoint interiors, and two distinct circles meet in at most two points. There are at most `nD` circles, so the known drawing bound is

\[
\operatorname{cr}\ll n^2D^2.
\]

The multigraph crossing lemma, when `e >= A_0 T n`, gives

\[
\operatorname{cr}\gg \frac{e^3}{Tn^2}.
\]

GK supplies `E/n^3 = O(log n)`, so for a fixed AP cap and `e >= c n^2` the threshold holds for large `n`. Also Cauchy gives

\[
\frac E{n^3}\ge K(P)(1-1/n)^2,
\]

which tends to infinity in the regime under discussion. The ceiling therefore costs only a constant. Combining the bounds yields

\[
ED^2\gg_{C,c} n^5,\qquad
K(P)^2\le B(C,c)\log n. \tag{2.3}
\]

Together with (2.1), this would prove the sharp conjecture. No converse, from the sharp conjecture to AP_EXT, is established.

### 2.3 Record maximizers: a valid strengthening with an exact transfer

Fix `A>0` and set

\[
\Phi_A(P)=K(P)^2-A\log|P|.
\]

Maximize this functional over the nontrivial subsets of an initial finite set. The selected set satisfies, for every nontrivial `Q subset P`, with `q=|Q|`,

\[
\boxed{K(Q)^2\le K(P)^2-A\log(n/q).} \tag{2.4}
\]

In particular it satisfies EXT. If the initial set has positive `Phi_A`, the selected record does too. Under the negation of the sharp conjecture, one can obtain such records with `K -> infinity` for each fixed `A`.

There is no need to assume uniform AP constants as `A` varies. In fact, suppose the initial set has size `N`, the selected record has size `n`, and `Phi_A(P_0)>0`. Then

\[
\boxed{
\frac{K(P)^2}{\log n}
 = A+\frac{\Phi_A(P)}{\log n}
 \ge A+\frac{\Phi_A(P_0)}{\log N}
 =\frac{K(P_0)^2}{\log N}.
} \tag{2.5}
\]

Both the positivity of the potential and `n<=N` were used. Thus arbitrarily large violations of the sharp bound pass to positive records for **any fixed** `A`.

Equivalently, if an AP theorem on these records gives `K(P)^2<=B log n`, maximizing the potential yields

\[
K(P_0)^2\le A\log N+(B-A)\log n
\le\max(A,B)\log N.
\]

Bounded-`K` exceptions can be absorbed in the constant. Hence AP on positive `A`-records with `K -> infinity`, for one fixed `A` and fixed AP constants, would already suffice for the original conjecture. Only a claim to prove the **preassigned** coefficient `A` itself would require an additional comparison with `B`.

Also, (2.4), applied to a pair, requires

\[
K(P)^2\ge 4+A\log(n/2).
\]

Thus it is not legitimate to assert that a familiar lattice family is a positive record for an arbitrarily large `A`.

---

## 3. Actual support consequences of EXT, and the subset-transfer issue

### 3.1 Exact distance-loss formulation

For `R subset P` with `r=|R|<=n-2`, let

\[
\lambda_P(R)=|S(P)\setminus S(P\setminus R)|.
\]

Then EXT is exactly equivalent to

\[
\boxed{\lambda_P(R)\le \frac r{K(P)}\quad(r\le n-2).} \tag{3.1}
\]

**Proof.** Substitute `|P\setminus R|=n-r` and `D(P\setminus R)=D-lambda` in EXT, and cross-multiply the positive denominators:

\[
\frac{n-r}{D-\lambda}\le\frac nD
\quad\Longleftrightarrow\quad n\lambda\le Dr.
\]

This is a statement about the actual supports of the distance graphs. In particular, deleting fewer than `K(P)` points cannot eliminate a distance, as long as at least two points remain. For `D>=2`, every individual distance graph has vertex-cover number at least `K(P)`, and hence matching number at least `K(P)/2`. The vertex-cover assertion follows from (3.1) if a minimum cover leaves two points; otherwise its size is at least `n-1>=K(P)`. The matching assertion uses the endpoints of a maximal matching as a vertex cover.

For an `A`-record, the exact strengthened version is

\[
\frac{(n-r)^2}{(D-\lambda)^2}
\le K(P)^2-A\log\frac n{n-r}. \tag{3.2}
\]

Neither (3.1) nor (3.2) identifies which equal-radius pairs are consecutive around a pin. In particular, the matching conclusion is not a bound on overloaded adjacency arcs.

### 3.2 A finite comparison for the actual arc systems

For any `Q subset P`, put `q=|Q|>=2` and `m=n-q`. For every integer `T>=1`,

\[
\boxed{M_T(Q)\le M_T(P)+qm.} \tag{3.3}
\]

There is also the elementary reverse comparison

\[
M_T(Q)\ge M_T(P)-m(n-1)-2qm. \tag{3.4}
\]

**Proof of (3.3).** Identify an arc for counting purposes by its actual center and unordered endpoints; its radius is then determined. At a retained center `p`, every new adjacency in `Q` that was not an adjacency in `P` has a deleted point in the interior of its selected circular gap. Different selected gaps on one fiber have disjoint interiors, and a deleted point belongs to only one radius fiber at `p`. Charge each new adjacency to one such deleted point. There are at most `m` new adjacencies at this center and at most `qm` altogether. All other arc incidences form a submultiset of those of `P`. Adding an arc can increase the capped sum by at most one. The antipodal size-two convention causes no problem: if the center–endpoint triple already occurred, it is not new; otherwise the selected semicircle contains a deleted point.

For (3.4), original arcs with center and both endpoints retained remain adjacencies, as endpoint incidences. Deleted centers account for at most `m(n-1)` arcs. At any surviving center, a deleted endpoint belongs to at most two retained gaps, so deleted endpoints account for at most `2qm` more. Removing an arc decreases a capped sum by at most one.

Energy behaves differently after normalization:

\[
E(Q)\le E(P),\qquad
\left\lceil\frac{CE(Q)}{q^3}\right\rceil
\le \left\lceil\frac{CE(P)}{q^3}\right\rceil,
\tag{3.5}
\]

but the right side need not be comparable to the old cap with an absolute factor if `q/n -> 0`.

Equations (3.3)–(3.5) do prove a useful **near-full transfer**: if `q/n -> 1` and a family `P` fails AP in the sense that its normalized capped mass tends to zero for every fixed cap constant, then `Q` fails it in the same sense. Eventually the new cap is at most the old cap with constant `2C`, and `qm=o(n^2)`. There is no such near-full conclusion from EXT selection in the inputs to this problem.

### 3.3 An exact maximizer can create a previously absent endpoint pair

This small example only verifies the selection issue; it is **not** a low-distance asymptotic counterexample.

Take

\[
p=(0,0),\quad a=(1,0),\quad
b=(1/2,\sqrt3/2),\quad x=(4/5,3/5),
\]

and let `P={p,a,b,x}`, `Q={p,a,b}`. The set `Q` is equilateral, so `K(Q)=3`, and is the unique ratio-maximizing nontrivial subset of `P`. Indeed `D(P)=3`, every other triple has at least two distances, and every pair has ratio two.

At center `p`, the circular order on the unit circle is `a,x,b`, followed by a gap greater than `pi`. Thus `a,b` are not adjacent in `P`. The other potential center `x` has unequal squared distances

\[
|x-a|^2=2/5,\qquad |x-b|^2=(6-3\sqrt3)/5,
\]

so `mu_ab(P)=0`. After extremal selection, `mu_ab(Q)=1`, with actual center `p`.

There is also a normalized-energy increase:

\[
E(P)=72,\quad E(P)/4^3=9/8;
\qquad E(Q)=36,\quad E(Q)/3^3=4/3.
\]

The example rules out identifying the arc system of an exact maximizing subset with an induced subgraph of the original arc system. It makes no claim that total capped mass increases in this particular four-point example.

---

## 4. A general angular-support capacity bound

This bound is valid for arbitrary planar sets, before imposing EXT or any lattice hypothesis.

Let `R=diam(P)`, let `0<theta<=pi`, and let

\[
N_P(\rho)=|\{\{a,b\}\subset P:0<|a-b|\le\rho\}|.
\]

Partition the actual source palette as `S(P)=B union G`. Write

\[
b(P)=\sum_{s\in B}r_s(P),\qquad g=|G|.
\]

Then for every `T>=1`,

\[
\boxed{M_T(P)\le b(P)+\frac{2\pi ng}{\theta}+T N_P(R\theta).} \tag{4.1}
\]

**Proof.** Arcs with source in `B` number at most `b(P)`. At any pin and any other source color, the sum of the selected gap angles is at most `2pi`, so there are at most `2pi/theta` gaps of angle greater than `theta`. Each remaining arc has endpoint distance

\[
2\sqrt{s}\sin(\alpha/2)\le\sqrt{s}\,\alpha\le R\theta.
\]

The capped contribution of all these remaining arcs is at most `T` times the number of actual close endpoint pairs. Formally, use

\[
\min(\mu^{B}_{ab}+\mu^{\rm large}_{ab}+\mu^{\rm small}_{ab},T)
\le\mu^B_{ab}+\mu^{\rm large}_{ab}
   +T\,1_{\{\mu^{\rm small}_{ab}>0\}}.
\]

This proves (4.1). It uses full-fiber angular adjacency, not arbitrary equal-radius pairs.

One exact consequence of EXT is worth noting, including its direction. Define `D_{<=2rho}=|{s in S(P): sqrt(s)<=2rho}|`, counting Euclidean lengths at most `2rho` (equivalently, squared distances at most `4rho^2`). Then

\[
N_P(\rho)\le \frac{nK(P)}2 D_{\le2\rho}. \tag{4.2}
\]

Indeed each set `P intersect closedDisk(a,rho)` has at most `K(P) D_{<=2rho}` points when it has at least two. Sum its number of points other than `a`, and divide by two. This gives an **upper** capacity for short endpoint pairs. It is not the lower capped-mass estimate AP requires.

---

## 5. Proof of the uniform lattice-square obstruction

Let `P subset G_L` have at least two points, and put

\[
n=|P|,\qquad \delta=n/L^2,\qquad
 t=\log L,\quad u=\log\log L,
\]

and take `L` sufficiently large. Let

\[
R_2(s)=|\{z\in\mathbb Z^2:|z|^2=s\}|\quad(s>0).
\]

The capital `R_2` is an ambient representation count, not the ordered distance multiplicity `r_s(P)`.

### 5.1 Two moment estimates for ambient representations

We need

\[
\sum_{1\le s\le2L^2}R_2(s)\ll L^2,
\qquad
\sum_{1\le s\le2L^2}R_2(s)^2\ll L^2\log L. \tag{5.1}
\]

The first just counts lattice vectors in a disk. For the second, all such representations lie in `[-2L,2L]^2`. For equal-norm vectors `z,z'`, set `v=z+z'`, `w=z-z'`; then `v dot w=0`. Zero cases contribute `O(L^2)`. For nonzero perpendicular vectors write

\[
v=k(a,b),\qquad w=\ell(-b,a),
\]

with `(a,b)` primitive, accounting for signs by a constant. If `j=max(|a|,|b|)`, there are `O(j)` possible primitive directions and `O((L/j)^2)` multiplier pairs. Summing over `1<=j<=4L` gives `O(L^2 log L)`. Dropping the parity restrictions on `v,w` only enlarges the bound. This is also the square case of the orthogonal-vector count in Section 3 of `circular_order_rectangular_grid_counterexample.md`.

### 5.2 A size-weighted lower normal order, proved without angle estimates

We claim

\[
\boxed{
\sum_{\substack{1\le s\le2L^2\\R_2(s)<t^{2/3}}}R_2(s)
\ll \frac{L^2}{u}.} \tag{5.2}
\]

Here the exponent `2/3` is admissible because `2/3 < log 2`.

The number-theoretic inputs for this claim are Gaussian-integer unique factorization and the classical Mertens estimate in the progression `1 mod 4`:

\[
\sum_{\substack{p\le y\\p\equiv1\ (4)}}\frac1p
=\frac12\log\log y+O(1). \tag{5.3}
\]

A proof of the required probabilistic estimate follows, so no unquoted angular or normal-order theorem is needed.

Choose a uniformly random Gaussian integer `z` in `[-2L,2L]^2`, and put `y=L^(1/2)`. Let

\[
X(z)=\sum_{\substack{p\le y\\p\equiv1\ (4)}}1_{\{p\mid |z|^2\}}.
\]

For a Gaussian ideal of index `h`, the lattice is a rotated square lattice of spacing `sqrt(h)`, and elementary boundary counting gives

\[
|I\cap[-2L,2L]^2|=\frac{16L^2}{h}
 +O\!\left(\frac L{\sqrt h}+1\right). \tag{5.4}
\]

For `p=1 mod 4`, factor `p=pi conjugate(pi)`. The event `p divides |z|^2` is the union of divisibility by `pi` and by `conjugate(pi)`; their intersection has index `p^2`. Its density is therefore

\[
a_p=2/p-1/p^2,
\]

up to error `O(1/(L sqrt(p))+1/L^2)`. For two distinct such primes `p,q`, inclusion-exclusion and coprimality give density `a_p a_q`, up to

\[
O\!\left(\frac1{L\sqrt{pq}}+\frac1{L^2}\right).
\]

The sums of the pair errors are

\[
O(y/L+y^2/L^2)=o(1),
\]

using `sum_{j<=y} j^(-1/2)=O(sqrt(y))`; single-prime errors are smaller. The harmless difference between `16L^2` and the number of sampled lattice points is absorbed in these estimates. Equation (5.3) consequently yields

\[
\mathbb E X=u+O(1),\qquad \operatorname{Var}X=O(u). \tag{5.5}
\]

For a nonzero `z`, the usual Gaussian factorization formula for representations gives

\[
R_2(|z|^2)
=4\prod_{p\equiv1\ (4)}(v_p(|z|^2)+1)
\ge 4\,2^{X(z)}.
\]

Since `2/(3 log 2)<1`, Chebyshev applied to (5.5) shows that

\[
|\{z\in[-2L,2L]^2\setminus\{0\}:
      R_2(|z|^2)<t^{2/3}\}|\ll L^2/u.
\]

Every representation of a positive `s<=2L^2` belongs to that square. Summing the bad representations proves (5.2). The point `z=0` is excluded from the representation formula; including it in the moment calculation changes the error by at most the already controlled `O(y^2/L^2)`.

### 5.3 Apply (4.1) to the actual fibers of an arbitrary subset

Call a source color **bad** if `R_2(s)<t^(2/3)`, and good otherwise. For every actual pin,

\[
|F_{p,s}|\le R_2(s),\qquad r_s(P)\le nR_2(s).
\]

It follows from (5.2) that the bad-source arc mass is at most

\[
b(P)\ll nL^2/u. \tag{5.6}
\]

By the first estimate in (5.1), there are at most

\[
g\ll L^2t^{-2/3} \tag{5.7}
\]

good source colors, whether or not every one is realized by `P`.

By the second estimate in (5.1),

\[
E(P)\le n^2\sum_{1\le s\le2L^2}R_2(s)^2
\ll n^2L^2t,
\]

so the actual proposed cap satisfies

\[
T_C=\left\lceil\frac{CE(P)}{n^3}\right\rceil
\ll_C \delta^{-1}t. \tag{5.8}
\]

Set `theta=t^(-3/5)`. The diameter is at most `sqrt(2)L`. For each endpoint `a`, at most `O(L^2 theta^2+1)` lattice points are within distance `sqrt(2)L theta`. Thus the number of eligible unordered endpoint pairs is

\[
N_P(\sqrt2 L\theta)\ll n(L^2\theta^2+1). \tag{5.9}
\]

No density lower bound or inherited circular-order assertion is used in (5.6)–(5.9).

Substitute these estimates into (4.1), then divide by `n^2`. The explicit result is

\[
\boxed{
\frac{M_{T_C}(P)}{n^2}
\ll_C
 \frac1{\delta u}
 +\frac{t^{-1/15}}{\delta}
 +\frac{t^{-1/5}}{\delta^2}
 +\frac{t}{\delta^2L^2}.
} \tag{5.10}
\]

Here `3/5-2/3=-1/15` and `1-2(3/5)=-1/5`. The ceiling is included in (5.8).

If `delta u -> infinity`, every term in (5.10) tends to zero. Finally, the classical sums-of-two-squares upper bound gives

\[
\frac{D(P)}n\ll\frac1{\delta\sqrt t}\longrightarrow0, \tag{5.11}
\]

because `u/sqrt(t) -> 0`. Equation (1.1) proves `|A(P)|=(1-o(1))n^2`. This completes the uniform actual-arc theorem.

In particular the failure concerns almost all the arc mass:

\[
\sum_{\mu_{ab}>T_C}\mu_{ab}=(1-o(1))n^2.
\]

It is not an exceptional-second-moment phenomenon. In fact the argument applies to every cap `T=O(delta^(-1) log L)`, not just the energy cap. Since `log n<=2 log L`, it also disproves the unrestricted cap-`C log n` claim on squares and on the subset families covered by the theorem. This still does not certify an EXT counterexample.

---

## 6. Exactly what this proves about hereditary maximizers

Let `Q_L` be any exact ratio maximizer inside `G_L`. Its heredity and low-distance property were proved in (2.2), without a structural assumption.

Suppose AP_EXT holds with constants `C,c`. Write `delta_L=|Q_L|/L^2`. For all sufficiently large `L`, AP gives a lower bound `c` for the left side of (5.10). If `delta_L >= B/u`, its right side is at most

\[
O_C(1/B)
 +O_C\!\left(u t^{-1/15}/B
             +u^2t^{-1/5}/B^2
             +t u^2/(B^2L^2)\right).
\]

Choose `B` sufficiently large relative to `C,c`, and then let `L` grow. This contradicts AP. Thus (0.1) follows.

This is a conditional theorem about the actual maximizers, not a constructed example in the extremal class. To turn it into a counterexample, one still needs an actual extremal family violating (0.1), or another endpoint-capacity argument that also handles the possible sparse maximizers.

There is no demonstrated contradiction between (0.1) and current inputs. For example, the unconditional GK bound `K(Q)<=C log |Q|`, combined with (2.2), only forces `|Q_L|>=exp(c sqrt(log L))`, far below the density threshold in the uniform theorem. In particular, even the hypothetical sharp bound would only compare `K(Q_L)` to `sqrt(log |Q_L|)`. Sizes such as `L^2/(log log L)^A` have nearly the same logarithm as `L^2`; logarithmic bounds alone do not exclude them. More generally, the maximizers need not occupy any prescribed positive-density lattice region at all.

The stronger result on squares therefore does **not** entitle one to write “choose a hereditary maximizing subset; the counterexample persists.” The exact transfer bounds in Section 3 explain why that inference fails. Nor does the theorem refute the positive-record version in Section 2.3: a record for the contradiction parameter must first be certified.

---

## 7. The missing theorem, stated without a core assumption

For fixed proposed AP constants, the following is an exact density-increment formulation of AP_EXT:

> Whenever `K(P)` is in the low-distance regime and
> \[
> M_{\lceil CE(P)/|P|^3\rceil}(P)<c|P|^2,
> \]
> there exists a nontrivial proper subset `Q subset P` with
> \[
> K(Q)>K(P).
> \tag{DI}
> \]

With matching quantifiers, `(DI)` and AP_EXT are equivalent: AP_EXT excludes an extremal failing set, while a nonextremal set has the asserted subset by definition. This is a reformulation of the needed geometric theorem, **not its proof**.

For the record version, in the positive-potential, low-distance regime, the required alternative is instead

\[
\boxed{K(Q)^2>K(P)^2-A\log(|P|/|Q|),} \tag{DI-record}
\]

with the positive-record reduction justified by (2.5). It may permit a small loss in `K^2`; it must still produce an actual subset with its actual distance support.

No implication from overloaded actual endpoint pairs to (DI) or (DI-record) has been proved here. The color-loss identity (3.1), the angular-support inequality (4.1), and the support bounds in `support_sensitive_motion_research.md` do not supply that implication. In particular:

* a count of rich centers on a bisector is not an induced low-distance subset;
* having many matching edges of every color does not say they occur as circular adjacencies;
* using a containing lattice palette gives an upper bound for a subset's distance count, not a density or support-saturation theorem;
* maximization of a ratio does not preserve the normalized energy or the adjacency system;
* no low-dimensional, dense-lattice, or macroscopic-motion core has been assumed.

**Accordingly, the requested full outcome remains open in this investigation:** AP_EXT is neither proved nor refuted, and no record-only proof has been obtained. The uniform obstruction and its conditional sparsity consequence narrow what a successful extremal repair would have to establish, but do not replace that missing step.

---

## 8. Verification boundary and dependencies

The asymptotic assertions above are supported by the proofs, not by numerical experiments. The number-theoretic inputs are explicitly limited to:

1. Gaussian-integer unique factorization and the representation formula;
2. the classical reciprocal-prime estimate (5.3);
3. the classical upper bound for the count of sums of two squares, used in (2.2) and (5.11).

The equal-norm second moment and the needed size-weighted lower normal order are proved in Section 5. No shrinking-sector or angular-equidistribution estimate is invoked.

An exact symbolic check of the four-point certificate gave the squared-distance list

\[
1,1,1,1,2/5,(6-3\sqrt3)/5,
\]

and energies `72` and `36`. The order certificates are

\[
\det(a,x)=3/5>0,\qquad
\det(x,b)=(4\sqrt3-3)/10>0.
\]

Thus this check concerns the explicitly specified actual endpoints and center; it is not a search for an asymptotic counterexample or evidence of an unproved density assertion.

The requested input files were read. No Lean or Spec files were edited. The pre/post SHA-256 of `Submission/Spec.lean` is

`c2fbaabe5ad8088f856ca97625747c7a01754f3c149dd6a493454e776de290db`.
