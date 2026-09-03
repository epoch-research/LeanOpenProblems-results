# Rich motions: an exact weighted inequality and a joint-data insufficiency theorem

## Status and scope

This does **not** prove the sharp planar distinct-distance conjecture. The concrete negative result is stronger than a scalar-tail counterexample: there are finite, integer-valued, balanced edge-colored models with actual row-domain subsets that satisfy

* the complete motion–distance table identities;
* the Guth–Katz-shaped rich-row tail;
* the proposed no-contraction hypothesis for **every** subset of size at most half;
* a linear distance-support bound on every nonidentity row;
* all orders of simultaneous **domain**-intersection identities, including their point-cardinality row sums;
* the usual numerical unit-distance upper bound on every subset; and
* unique source-edge/target-edge correspondence labels, sufficient for the stated support-only entropy inequality under **any** reweighting.

Nevertheless their distance support is `D = n / log_2 n`.

These are abstract colored models; no planar realization is constructed or asserted. Their edge correspondences need not give a consistent image of a point when its other endpoint changes. Thus the theorem proves insufficiency of the listed joint-data relaxation, not insufficiency of the full Euclidean geometry. An exact composition inequality below isolates additional information that the relaxation does not contain. A separate actual planar example rules out treating arbitrary rich-motion sets as bounded-doubling approximate groups.

No claim of priority is made for the elementary correlation inequalities. No conjectural weighted incidence estimate is asserted as a result.

All logarithms below are natural unless a base is displayed.

---

## 1. Exact geometric identities, including translations and identity

Let `P` be an `n`-point planar set with `n>=2`, and let `E_d` be its set of ordered distinct-point edges of length `d`. Put

\[
r_d=|E_d|,\qquad M=\sum_d r_d=n(n-1),\qquad D=|\{d:r_d>0\}|.
\]

Every pair of ordered edges of the same positive length determines exactly one direct Euclidean isometry, including a translation or the identity when appropriate. Let `G` contain all such isometries, and set

\[
Q_g=P\cap g^{-1}P,\quad k_g=|Q_g|,\quad
 a_{g,d}=|E_d\cap (Q_g\times Q_g)|.
\]

Then

\[
\boxed{\sum_g a_{g,d}=r_d^2},\qquad
\boxed{\sum_d a_{g,d}=k_g(k_g-1)}. \tag{1}
\]

Also `a_{g,d}=a_{g^{-1},d}`, all entries are even, `a_{id,d}=r_d`, and `a_{g,d} <= r_d`.

For a tuple of motions define

\[
Q_{g_1,\ldots,g_s}=P\cap\bigcap_{i=1}^s g_i^{-1}P,
\qquad b_{g_1,\ldots,g_s,d}=r_d(Q_{g_1,\ldots,g_s}).
\]

The empty tuple has `b_{empty,d}=r_d`. For every fixed preceding tuple,

\[
\boxed{\sum_h b_{g_1,\ldots,g_s,h,d}=r_d b_{g_1,\ldots,g_s,d}}. \tag{2}
\]

Indeed, each ordered source edge of color `d` has exactly `r_d` possible ordered target edges. Consequently

\[
\boxed{\sum_{g_1,\ldots,g_s}b_{g_1,\ldots,g_s,d}=r_d^{s+1}},
\quad
\sum_d b_{g_1,\ldots,g_s,d}
=|Q_{g_1,\ldots,g_s}|(|Q_{g_1,\ldots,g_s}|-1). \tag{3}
\]

The indices in these identities range independently and may repeat. Thus higher simultaneous-domain moments are not, by themselves, new upper bounds.

### Support-uniform reweighting

Define

\[
W_g=\sum_d\frac{a_{g,d}}{r_d^2}.
\]

Then exactly

\[
\sum_g W_g=D,\qquad W_{id}=\sum_d\frac1{r_d}. \tag{4}
\]

Choosing `d` uniformly, then choosing the source and target ordered `d`-edges independently and uniformly, gives

\[
\Pr(d,g)=\frac{a_{g,d}}{D r_d^2}.
\]

In particular, if all `r_d` coincide, support-uniform reweighting is a single global rescaling of the ordinary quadruple measure. It cannot manufacture multiplicity nonuniformity.

---

## 2. An actual weighted composition inequality

For a finite list of motions, form matrices indexed by that list:

\[
C^d_{g,h}=a_{h g^{-1},d},\qquad B^d_{g,h}=b_{g,h,d},
\qquad v^d_g=a_{g,d}.
\]

Here `a_{u,d}=0` if a product `u` has fewer than two incidences with `P`.

### Proposition: Gram domination

\[
\boxed{C^d\succeq B^d\succeq \frac{v^d(v^d)^T}{r_d}.} \tag{5}
\]

In particular, for **arbitrary real** coefficients `z_g`, not just nonnegative ones,

\[
\boxed{
\sum_{g,h}z_gz_h W_{h g^{-1}}
\ge \sum_d\frac{(\sum_g z_g a_{g,d})^2}{r_d^3}
\ge \frac{(\sum_g z_g W_g)^2}{W_{id}}.
} \tag{6}
\]

#### Proof

Let `U_d` be the orbit of all ordered planar segments of length `d`, with counting measure. Only a finite part of it is involved in any of the following sums. Direct isometries permute `U_d`. One has

\[
C^d_{g,h}=\sum_{e\in U_d}1_{E_d}(g e)1_{E_d}(h e),
\quad
B^d_{g,h}=\sum_{e\in E_d}1_{E_d}(g e)1_{E_d}(h e).
\]

The first equality follows by changing variables `f=g e`. Thus `C^d-B^d` is the Gram matrix contributed by `e outside E_d` and is positive semidefinite. Cauchy–Schwarz on the `r_d` elements of `E_d` gives the second domination in (5). Multiply by `r_d^{-2}` and sum over `d`. A final Cauchy–Schwarz inequality, with coefficient vector `(r_d^{-1/2})_d`, gives (6).

This also proves the familiar positive definiteness of `g -> a_{g,d}` and `g -> W_g`.

### Exactly what composition adds

There is a pointwise inclusion

\[
g(Q_g\cap Q_h)\subset Q_{h g^{-1}},
\quad b_{g,h,d}\le a_{h g^{-1},d}. \tag{7}
\]

More precisely, `g` maps `g^{-1}P intersect h^{-1}P` bijectively onto `Q_{h g^{-1}}`. The difference

\[
a_{h g^{-1},d}-b_{g,h,d}
\]

counts ordered `d`-edges of `g^{-1}P intersect h^{-1}P` with at least one endpoint outside `P`. The whole difference kernel is PSD, as proved above.

Thus knowing every intersection of the subsets `Q_g` inside `P` still does not determine the product-motion kernel. Composition introduces coherent coordinate frames and edges outside `P`, not another instance of the scalar row tail.

The proposition is an established inequality here, not a placeholder for a weighted GK estimate. It does not itself produce the conjectured logarithmic improvement.

---

## 3. A balanced coloring with no good half-size subset

Here and below a color is an abstract distance label, not a prescribed Euclidean length.

Take

\[
t=2^s\ge64,\qquad n=2^t,\qquad D=n/t,\qquad r=t(n-1).
\tag{8}
\]

Thus `D` and `r/2` are integers and `D r=n(n-1)`. There exists a coloring of the unordered edges of `K_n` by `D` colors, each used exactly `r/2` times, with the following three properties. Write `D(Q)` for the number of colors induced by a vertex subset `Q`.

\[
D(Q)\ge\min\left(\frac{|Q|}{16},\frac{3D}{4}\right)
\quad(2\le |Q|\le n/2); \tag{9}
\]

\[
r_d(Q)<16|Q|
\quad(2\le |Q|\le\sqrt n,\text{ every }d); \tag{10}
\]

\[
\deg_d(v)<8t\quad(\text{every }v,d). \tag{11}
\]

In particular, on **every** subset, not just the small ones,

\[
r_d(Q)\le16|Q|^{4/3}. \tag{12}
\]

### Proof of existence, with balanced rather than independent colors

Let `N=binom(n,2)` and `m=N/D=r/2`. Randomly permute all edges and put consecutive blocks of `m` edges into the `D` color classes. For any `h` distinct edges and any `u` specified colors,

\[
\Pr(\text{all }h\text{ edges use those colors})
=\frac{(u m)_h}{(N)_h}\le(u/D)^h. \tag{13}
\]

Here the probability is zero if there are too few available edges. Falling factorials make the inequality exact for the balanced model.

**Property (9).** For fixed `k`, put

\[
u=\left\lceil\min(k/16,3D/4)\right\rceil-1.
\]

A violating `k`-set uses at most `u` colors. The union bound is

\[
\binom nk\binom{D}{u}(u/D)^{\binom k2}. \tag{14}
\]

For `k<=16`, violation is impossible. For `17<=k<=sqrt(D)`, use `n<=D^2`, `u<=k/16`, and `u/D<=D^{-1/2}`. The bound in (14) is at most

\[
D^{33k/16-k(k-1)/4}\le D^{-k}.
\]

For `k>sqrt(D)`, use `u/D<=3/4`. Put `alpha=log(4/3)>1/4`. Since `D>=2^58` and

\[
\sqrt D-1\ge \frac{33}{4\alpha}\log D,
\]

(14) is at most `exp(-alpha k(k-1)/4)`. Summing these probabilities over all relevant `k` gives at most

\[
\frac{D^{-17}}{1-D^{-1}}+n e^{-D/32}<1/10.
\]

**Property (10).** If `k<=16`, an unordered `k`-vertex graph has fewer than `8k` edges. For `17<=k<=sqrt(n)`, the probability that some color has at least `8k` edges on some `k`-set is at most

\[
n^k D\binom{\binom k2}{8k}D^{-8k}
\le n^{1-3k}(e t/16)^{8k}
\le n^{1-2k},
\]

where `t^8<=n` for the parameters (8). The sum is less than `1/10`. Doubling the unordered count proves (10).

**Property (11).** A union bound over vertices, colors, and `8t` neighbors gives failure probability at most

\[
nD\left(\frac e8\right)^{8t}
\le\left[4(e/8)^8\right]^t<1/10.
\]

Thus all three properties hold simultaneously with positive probability. One completely specified finite construction is to take the lexicographically first balanced coloring satisfying (9)–(11); the preceding proof guarantees that this finite search terminates. This is an existence construction, not an efficient algorithm for its enormous parameters.

Finally `t^3<=sqrt(n)`. If `|Q|<=sqrt(n)`, use (10). Otherwise (11) gives `r_d(Q)<=8t|Q|<=8|Q|^{4/3}`. This proves (12).

### Consequence for contraction

The whole set has `K(P)=n/D=t`. By (9), every `2<=|Q|<=n/2` satisfies

\[
K(Q)\le\max(16,2t/3)=2t/3.
\]

Therefore its unrestricted colored-subset contraction defect is at least

\[
\boxed{K(P)^2-\max_{2\le |Q|\le n/2}K(Q)^2\ge5t^2/9.} \tag{15}
\]

For any fixed proposed loss `C`, choosing `t` with `5t^2/9>C` gives exactly the proposed contradiction hypothesis `K(Q)^2<K(P)^2-C` for every half-size subset.

---

## 4. Rich domains realizing the entire joint table

Identify the `n` vertices with the field `F_n`. Set

\[
L=t/2,\quad k_j=2^j\ (1\le j\le L),\quad
m_j=2\left\lfloor\frac{n-2}{k_j(k_j-1)}\right\rfloor.
\]

For each `j`, choose any `k_j`-element set `S_j subset F_n`. For example, use the span of the first `j` elements of a fixed `F_2` basis.

Let `A_j` be the indexed family of the `n(n-1)` subsets

\[
a S_j+b,\quad a\in F_n^*,\ b\in F_n.
\]

Equal subsets are retained with their different indices. This is legitimate for domain data: distinct actual motions can also have equal domains.

### Two-design identity

Every unordered pair of vertices belongs to exactly `k_j(k_j-1)` members of `A_j`.

For a fixed ordered pair `(x,y)`, choose an ordered pair `(u,v)` of distinct points of `S_j`. There is exactly one affine map with `a u+b=x`, `a v+b=y`. Counting these maps proves the assertion, including all multiplicities.

Define the odd positive integer

\[
s_0=r-1-\sum_{j=1}^L m_j k_j(k_j-1). \tag{16}
\]

Indeed, writing

\[
\delta_j=2(n-2)-m_j k_j(k_j-1),\quad
0\le\delta_j<2k_j(k_j-1),
\]

gives

\[
s_0=t-1+\sum_j\delta_j,
\qquad 0<s_0<3n. \tag{17}
\]

Now make the following indexed domain family:

1. one identity row with domain all `n` vertices;
2. `m_j` copies of `A_j` for each `j`;
3. `s_0` copies of the family of **all unordered two-element subsets**.

Call its indices `g`, and put `Q_g` equal to the indicated domain. For the balanced coloring from Section 3 define `a_{g,d}=r_d(Q_g)`.

### Proposition: all the claimed table and intersection axioms hold

Every unordered, and hence every ordered, edge belongs to exactly

\[
1+\sum_j m_j k_j(k_j-1)+s_0=r
\]

rows. Therefore

\[
\sum_g a_{g,d}=r\,r_d=r^2,\qquad
\sum_d a_{g,d}=k_g(k_g-1). \tag{18}
\]

There is exactly one row of size `n`; all other rows have `k_g<=sqrt(n)<=n/2`. Since `sqrt(n)<=12D`, (9) gives

\[
\boxed{D(Q_g)\ge k_g/16\quad(g\ne id).} \tag{19}
\]

This is stronger than the inductive bound `c_0 k_g/sqrt(log k_g)` for a sufficiently small absolute `c_0`, for example `c_0=sqrt(log 2)/16`. Property (10) also prevents a few high-mass colors from being responsible for this support bound.

All entries are even and at most `r`. If desired, there is a statistical inversion involution on row indices preserving `Q_g`, `k_g`, and every `a_{g,d}`: pair the copies of each `A_j`, pair all but one of the copies of the two-set family, and fix the remaining two-set rows and the identity. There are only `binom(n,2)` nonidentity fixed rows. This is a row-data involution, **not** a claim that the edge maps below compose or invert as Euclidean motions.

### Rich-row tail

For `2<k<=n`, summing the dyadic sizes `k_j>=k` gives

\[
|\{g:k_g\ge k\}|
\le1+\sum_{j:k_j\ge k}m_j n(n-1)
\le1+\frac{16n^3}{3k^2}
\le\frac{6n^3}{k^2}. \tag{20}
\]

Here `m_j<=4n/k_j^2`. At `k=2`, the two-set rows add fewer than `3n^3/2`, while all affine-family rows number less than `4n^3/3`. Including identity therefore gives

\[
\boxed{|\{g:k_g\ge k\}|\le12 n^3/k^2\quad(k\ge2).} \tag{21}
\]

The count is zero for `k>n`.

### All simultaneous intersections, with genuine point-domain row sums

For every tuple of indices use the actual set intersection `Q_{g_1} intersect ... intersect Q_{g_s}` and its induced colors. Every source edge occurs in exactly `r` domains. Hence (2) and (3) hold **at every order**, with `r_d=r`, and the sum across colors is exactly `ell(ell-1)` for the size `ell` of that intersection.

In particular, for arbitrary real `z_g`,

\[
\sum_{g,h}z_gz_h b_{g,h,d}
=\sum_{e\in E_d}\left(\sum_{g:e\subset Q_g}z_g\right)^2
\ge\frac{(\sum_g z_g a_{g,d})^2}{r}. \tag{22}
\]

Thus arbitrary support-uniform reweightings and all these weighted domain-overlap Gram inequalities also hold. Every small intersection is subject to the same all-subset contraction and support bounds, not an independently invented row statistic.

### Failure of the desired conclusion

Exactly,

\[
D=n/t,\qquad E=Dr^2=t n(n-1)^2=M^2/D.
\]

Therefore

\[
\frac{D\sqrt{\log n}}n=\frac{\sqrt{\log2}}{\sqrt t}\longrightarrow0.
\tag{23}
\]

The quadruple energy saturates ordinary Cauchy–Schwarz, while all the proper domains have linearly many colors and every half-size subset has the strict contraction deficit (15).

There is also a quantitative weighted obstruction, not just a comparison of total energies. Put `q_j=k_j(k_j-1)`. Since `1<=(n-2)/q_j`,

\[
n-2\le m_jq_j\le2(n-2).
\]

Consequently each of the `L=t/2` affine-family dyadic strata contributes support-uniform mass

\[
\frac{n(n-2)}{t^2(n-1)}
\ \le\ \sum_{g\text{ in stratum }j}W_g
\ \le\ \frac{2n(n-2)}{t^2(n-1)}.
\]

Thus a constant fraction of the total `D` remains distributed over `Theta(log n)` richness scales after reweighting. Nor are the row supports inflated by negligible entries: (10) implies the conditional color entropy bound `H(d|g)>=log((k_g-1)/16)` whenever its right side is positive.

Even the stronger hypothetical amplification `E D^2 >= c n^5` fails in this model, since

\[
\frac{E D^2}{n^5}=\frac{(1-1/n)^2}{t}\longrightarrow0.
\]

This is a counterexample to deduction from the specified joint-data axioms, not a counterexample to the planar conjecture.

---

## 5. Unique correspondence labels and the entropy inequality can also be retained

The domain model can be augmented so that each row has a color-preserving **partial bijection of ordered edges**, and every source-edge/target-edge pair of equal color occurs in exactly one row. This makes the insufficiency statement stronger than merely displaying numerical column sums.

Fix a color and put `R=r/2`. There are `R` unordered source edges. Make the bipartite incidence graph between these edges and the rows containing them. Each source edge has degree `r=2R`; each row has degree `a_{g,d}/2<=R`.

Split each source vertex into two clones, each of degree `R`. The resulting bipartite graph has maximum degree `R`, so it has a proper `R`-edge-coloring. For completeness, one obtains this by adding dummy vertices and edges to make a regular bipartite multigraph; Hall's theorem gives a perfect matching, and repeatedly deleting such matchings gives the edge-coloring.

Interpret its `R` colors as the `R` unordered **target** edges of the same distance color. The identity row sees all `R` colors, so relabel them to make its source edge `e` have target `e`. Each original source edge sees each target color exactly twice, once at each clone. Give those two occurrences the two orientation choices, making the identity occurrence orientation-preserving.

At a given row, target colors are distinct. Thus this construction defines a partial bijection `T_{g,d}` on ordered edges, commuting with reversal. Its domain is exactly the ordered color-`d` edges inside `Q_g`. Moreover

* `T_id` is the identity;
* for each ordered source edge `e` and ordered target edge `f` of that color there is exactly one `g` with `T_g(e)=f`;
* the row and column counts are exactly the previously constructed `a_{g,d}` and `r^2`.

Do this separately for all distance colors; their edge sets are disjoint.

### Consequence for the stated entropy route

Let `B=(p,q)` be an ordered source edge, `X,Y` its target endpoints, and `G` the unique row label. Conditional on `B`, the label `G` and the pair `(X,Y)` determine each other. This holds for the support, hence for **every probability reweighting** on that support. Exactly,

\[
H(G\mid B,X)+H(G\mid B,Y)
=H(G\mid B)-I(X;Y\mid B)
\le H(G\mid B). \tag{24}
\]

This includes support-uniform reweighting by `1/r_d^2`. In this model all those weights are equal.

**The missing property is explicit:** if two source edges share a point `p`, the two assigned target edges in a row need not give `p` the same image. Consequently `T_g` need not arise from any point map `Q_g -> P`, much less a direct isometry. The construction also does not assert coherent inverse or composition laws for these edge maps. Those laws cannot be replaced by the support-only entropy statement (24), the statistical inversion of row counts, or all the source-domain moments.

---

## 6. Positive definiteness alone still permits a full logarithmic loss

This is a separate, exact group-kernel example, not claimed to be the same construction as Sections 3–5.

On the translation group `Z`, let `S_j={0,...,2^j-1}`, `1<=j<=L`, and

\[
a_j(u)=|S_j\cap(S_j-u)|=(2^j-|u|)_+,
\qquad
W_L(u)=\sum_{j=1}^L\frac{a_j(u)}{2^{2j}}.
\]

These are actual set autocorrelations in a subgroup of `SE(2)`. Each column satisfies `sum_u a_j(u)=|S_j|^2`, and

\[
\sum_u W_L(u)=L,\qquad 1/2\le W_L(0)<1.
\]

For `u!=0`, summing the dyadic geometric series gives `W_L(u)<=2/|u|`. Therefore

\[
\sup_{\lambda>0}\lambda |\{u:W_L(u)\ge\lambda\}|\le5,
\quad\text{but}\quad \|W_L\|_1=L. \tag{25}
\]

All positive-definite and composition Gram inequalities hold, because these are actual group correlations. Thus positivity/composition plus a weak-`ell^1` bound cannot alone turn a support-normalized weighted tail into a logarithm-free total. This does **not** establish a single countermodel to all Euclidean constraints: its role is to rule out that particular functional-analytic shortcut.

---

## 7. Actual rich-motion sets need not be bounded-doubling approximate groups

Let `B={b_1,...,b_q}` and `A={+a_1,-a_1,...,+a_s,-a_s}` be real numbers, with the positive generators `a_i,b_j` linearly independent over `Q`. Put `m=2s>max(2q,4)` and take the collinear planar set

\[
P=\{(a+b,0):a\in A,\ b\in B\},\qquad |P|=mq.
\]

A direct isometry with at least two incidences maps the supporting line to itself. Its restriction is either a translation `x -> x+u` or a half-turn `x -> -x+c`.

Independence of the generators shows:

* a nonzero translation by `b_i-b_j` has exactly `m` incidences;
* any other nonidentity translation has at most `2q<m` incidences;
* a half-turn with `c=b_i+b_j` has `m` incidences if `i=j`, and `2m` if `i!=j`;
* any other half-turn has at most four incidences.

For example, a nonzero difference of two elements of `A` has at most two representations, while the zero difference has `m`; a nonzero `B`-difference has one representation. The analogous sum counts prove the half-turn assertions.

Thus the **entire** `m`-rich motion set consists exactly of

\[
\{x\mapsto x+u:u\in B-B\}
\ \cup\
\{x\mapsto-x+c:c\in B+B\}.
\]

It has `q(q-1)+1+binom(q+1,2)=O(q^2)` elements, including many nontranslation rotations. Products of two half-turns include all translations by

\[
b_i+b_j-b_k-b_l
\]

with the positive and negative two-element index sets disjoint. These give at least

\[
\binom q2\binom{q-2}2=\Theta(q^4)
\]

distinct products. Consequently the doubling ratio of the full rich-motion set is unbounded, of order at least `q^2`.

This disproves an automatic bounded-approximate-group step based solely on richness. It does not rule out extracting an approximate group under an additional high-composition-energy or near-saturation hypothesis. This example has many distances and is not a candidate counterexample to the sharp conjecture.

---

## 8. Conclusions and verification boundary

The task's suggested data do not force a contradiction when they mean the exact joint table, the rich-motion tail, support/induction on domains, arbitrary simultaneous **source-domain** intersections, and the stated support-only entropy inequality. Sections 3–5 give a single countermodel satisfying all of these together, even the all-subset no-contraction hypothesis, with `D=n/log_2 n`.

For genuine planar motions, Section 2 supplies the exact additional PSD composition domination. It explicitly involves coherent images outside the original point set. Sections 6 and 7 show why neither positive definiteness by itself nor automatic approximate-group structure supplies the missing gain.

What is **not** resolved is whether endpoint-coherent Euclidean motions, jointly across colors and with their actual composition law, force the required subset contraction or the sharp bound. No claim that all this geometry is insufficient is justified by the abstract models.

`verify_rich_motion_joint_table.py` checks exact finite instances of the identities, balanced-color/domain construction, all low-order intersection moments, edge-correspondence lift, weighted geometric Gram identity, dyadic kernel, and rich-motion growth example. The asymptotic countermodel is proved above; the computations do not replace its existence proof. Existing Lean files are unchanged.
