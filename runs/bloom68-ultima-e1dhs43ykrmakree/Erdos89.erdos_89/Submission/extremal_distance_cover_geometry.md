# Actual distance covers: geometric deletion certificates and a longest-distance obstruction

## Status and precise scope

**The sharp planar bound is not proved here. Neither a proof nor a counterexample to the proposed universal “some distance graph” theorem is obtained. No counterexample certified to satisfy EXT is constructed.**

There are, however, concrete geometric results and obstructions:

1. **Two actual geometric density-increment certificates.** A separated two-cap circular shell has a distance graph consisting of exactly two edges. A suitably isolated maximum cross-distance to a polygonal core is covered by the core's hull vertices. These are statements about the entire point set, not just a chosen matching.
2. **An ordered-distance/onion-depth theorem.** If an edge has the `j`-th largest distinct length, the sum of its endpoints' convex-layer depths is at most `j+1`. Consequently the first `t` convex layers cover the largest `2t` distance classes. On EXT sets this gives `H_t >= 2tK` when `2t<D`.
3. **A genuine low-distance lattice obstruction to diameter and short-prefix arguments.** Explicit integer-coordinate sets `P_k` satisfy
   \[
   D(P_k)\asymp \frac{|P_k|}{\sqrt{\log |P_k|}},\qquad
   \log |P_k|\asymp k^2.
   \]
   Their diameter graph is a matching of size `2^k`. Moreover, the first
   \[
   T_k=\frac{3^{\lfloor k/4\rfloor}+1}{2}
       =\exp(\Theta(\sqrt{\log |P_k|}))
   \]
   distance graphs all have covers much larger than `sqrt(log |P_k|)`. Every nonempty prefix of at most `T_k` longest colors also has cover much larger than its number of colors times `sqrt(log |P_k|)`.
4. **A local-to-global obstruction with actual interior endpoints.** Fill the same outer circle with all the lattice points in its disk, obtaining `Q_k`. The selected diameter matching is still a genuine diameter matching and all its endpoints are still exposed hull vertices. A distance occurring on exactly two edges of its endpoint set now has an actual matching of size at least `c|Q_k|`, with an explicit absolute `c>0`. Thus a sparse color found on the convex matching endpoint set is not automatically a small-cover color of the whole configuration.

The distinction in item 3 is essential: `P_k` also has a later distance graph of cover **two**, and an actual shell-to-core cross-distance graph of cover **four**. These give explicit ratio improvements, so `P_k` is not EXT once `k` is sufficiently large. For `Q_k`, the minimum cover over all its distance colors is not determined here. Neither family refutes the universal theorem in the question.

No arc-adjacency cap, abstract color model, bounded rational-rank hypothesis, or universal lattice-compression assertion is used. `Spec.lean` was not edited.

---

## 1. Conventions and the quantifiers of the missing theorem

For a finite set `P` of distinct planar points, let

\[
 n=|P|,\qquad
 S(P)=\{|p-q|^2:p,q\in P,\ p\ne q\},\qquad
 D=|S(P)|,\qquad K=n/D.
\]

The graph `G_s(P)` is a simple undirected graph with the **whole** vertex set `P` and all unordered edges of squared length `s`. Write `tau_s(P)` for its vertex-cover number. For a palette `C`, write `tau_P(C)` for the cover number of the union of its actual graphs. All edge and matching counts below are unordered. Squared lengths are used for exact arithmetic; their order is the same as the order of lengths.

The proposed sufficient theorem would assert that some absolute `c_0,C_0>0` satisfy, for every sufficiently large actual planar `P`,

\[
 D(P)\ge c_0|P|
 \quad\text{or}\quad
 \min_{s\in S(P)}\tau_s(P)\le C_0\sqrt{\log |P|}. \tag{1.1}
\]

On an EXT set with `D>=2`, the supplied exact reduction gives `tau_s>=K`. Thus (1.1), if proved, would give the sharp bound on EXT sets and then on all sets. The `D=1` case has at most three planar points and creates no asymptotic exception.

A genuine disproof of (1.1) would require, equivalently, a sequence with

\[
 \frac{D(P)}{|P|}\longrightarrow0,
 \qquad
 \frac{\min_s\tau_s(P)}{\sqrt{\log |P|}}\longrightarrow\infty. \tag{1.2}
\]

Large diameter cover, or large covers for a specified subfamily, is not (1.2). The constructed `P_k` explicitly fails its second condition.

We will use the following exact deletion test. If deleting `b` vertices leaves at least two points and extinguishes a color, then, for `D>1`,

\[
 K(P\setminus R)\ge\frac{n-b}{D-1}>\frac nD
 \quad\text{provided } b<K(P). \tag{1.3}
\]

More generally, extinguishing `a` colors gives a strict improvement whenever `b<aK`. This is applied below only after certifying the actual edges of those colors.

---

## 2. Two geometric density-increment certificates

### 2.1 Separated two-cap theorem

Let `R>0`. Let `A` be a finite set of at least two points on the circle of radius `R` centered at the origin. Suppose their arguments lie in an interval whose actual minimum and maximum are `alpha<beta`, with width

\[
 w=\beta-\alpha<\pi/2.
\]

Let `a_-` and `a_+` be the unique points with these extreme arguments. Let

\[
 B\subseteq\overline B(0,\rho R),\qquad 0\le\rho<1,
 \qquad 1+\rho<2\cos(w/2),
\]

and set `P=B union A union (-A)`. Then the distance graph of length

\[
 \ell_*=2R\cos(w/2)
\]

consists of exactly the two disjoint edges

\[
 \{a_+,-a_-\},\qquad \{a_-,-a_+\}. \tag{2.1}
\]

In particular its cover number is two. If `K(P)>2`, deleting `a_-` and `a_+` gives a strict ratio improvement.

**Proof.** For `a,a' in A`,

\[
 |a-(-a')|=2R\cos\bigl((\arg a-\arg a')/2\bigr).
\]

The cosine is strictly decreasing with the absolute argument difference in the interval in question. Its minimum is attained exactly at the two ordered extreme pairs. All same-cap distances are at most `2R sin(w/2)`, strictly below `ell_*`, because `w<pi/2`. Every shell-to-`B` distance is at most `(1+rho)R<ell_*`; every internal `B` distance is at most `2rho R<(1+rho)R`. Thus no omitted type of edge has this length. The four shell endpoints in (2.1) are distinct. There is a shorter positive distance, so `D>1`; deleting two of these four vertices leaves at least two. Apply (1.3). □

This theorem is not a claim about an arbitrary selected pair of caps inside a larger set: **all other points must be accounted for by the stated `B`**. Section 7 gives a quantitative counterexample to dropping that condition.

### 2.2 Isolated maximum cross-distance to a polygonal core

Let `P=A union B`, where `A,B` are disjoint, finite, and nonempty. Put

\[
 \delta=\max\{|a-b|:a\in A,b\in B\}.
\]

Assume that `delta` is not an internal distance of either `A` or `B`. Then every edge of the actual `delta` graph has both endpoints among the hull vertices of their respective parts. Consequently

\[
 \tau_{\delta^2}(P)
 \le\min\bigl(|\operatorname{vert}(\operatorname{conv} A)|,
              |\operatorname{vert}(\operatorname{conv} B)|\bigr). \tag{2.2}
\]

**Proof.** A nonvertex `b` of the convex hull of `B` is a convex combination of at least two distinct hull vertices. Strict convexity of `x -> |x-a|^2` implies that some hull vertex is strictly farther from `a` than `b` is. Hence `b` cannot occur in a maximum cross-distance pair. The same argument applies to `a`. The assumption about internal distances ensures that these are all the edges of this actual color. □

Thus, for example, an isolated maximum cross-distance to a rectangular core has cover at most four. When that cover has size less than `K` and leaves two vertices, (1.3) is a genuine geometric density increment. **The noncoincidence with the internal palettes is necessary; it is not licensed by extremality.** Section 6 verifies it exactly in the construction.

---

## 3. Ordered distance families and convex-layer depth

Peel the vertices of the convex hull repeatedly. A point removed at step `i` has depth `d(p)=i`. For a collinear layer, peel its two extreme points; a singleton is peeled at once. Equivalently, at each step remove the extreme points of the current finite set's convex hull. Let

\[
 H_t=|\{p\in P:d(p)\le t\}|.
\]

For an actual distance `s`, let `j(s)` be its decreasing rank in the distinct-distance palette: the diameter has rank one.

### Theorem: endpoint depth sum

For every edge `{p,q}` of squared length `s`,

\[
 \boxed{d(p)+d(q)\le j(s)+1.} \tag{3.1}
\]

**Proof.** If `p` has depth `a>1`, it is a nonvertex at the preceding peeling stage. Strict convexity, as in Section 2.2, supplies a vertex of that stage at strictly greater distance from the fixed point `q`. Its depth is `a-1`. Repeating this replaces `p` by a first-layer point through `a-1` strictly increasing distances. Now keep that final point fixed and similarly move `q` outward through its `d(q)-1` preceding layers. There are altogether `d(p)+d(q)-2` strictly larger, mutually distinct lengths, all realized by actual pairs of `P`. This proves (3.1). None of the successive endpoints can coincide with its fixed opposite endpoint, since the distance is positive and strictly increases. □

If `C_j` consists of the largest `j` distinct distances, (3.1) shows that the first `ceil(j/2)` convex layers form a vertex cover:

\[
 \boxed{\tau_P(C_j)\le H_{\lceil j/2\rceil}.} \tag{3.2}
\]

In particular the hull vertices cover both the largest and second-largest distance graphs. On an EXT set, the proper-palette constraint combines with (3.2) to give

\[
 \boxed{H_t\ge 2tK\qquad\text{whenever }2t<D.} \tag{3.3}
\]

Whenever `H_t<2tK` and deletion leaves two points, deleting the first `t` layers is an actual ratio improvement, since it extinguishes the largest `2t` colors.

These are genuine geometric deletion statements, but (3.3) is only a linear lower bound on cumulative layer sizes. It does not yield `log n >> K^2`. No exponential layer-growth conclusion is inferred from it.

---

## 4. Explicit integer-coordinate construction

For each integer `k>=2`, define

\[
 a_j=10^j,\qquad \theta_j=\arctan(10^{-j})\quad(1\le j\le k),
\]

\[
 N_k=\prod_{j=1}^k(10^{2j}+1),\qquad R_k=\sqrt{N_k},
\]

and the positive cap

\[
 A_k=\left\{z_\varepsilon=\prod_{j=1}^k(10^j+i\varepsilon_j):
                    \varepsilon\in\{-1,1\}^k\right\}\subset\mathbb Z[i]. \tag{4.1}
\]

Put

\[
 S_k=A_k\cup(-A_k),\qquad
 m_k=\left\lfloor R_k/20\right\rfloor,\qquad
 B_k=\{-m_k,\ldots,m_k\}^2,
\]

\[
 P_k=S_k\cup B_k. \tag{4.2}
\]

All points in (4.1) have squared norm `N_k`. Let

\[
 \sigma_k=\sum_{j=1}^k\theta_j,
 \qquad z_+=\prod_{j=1}^k(10^j+i)=u_k+i v_k.
\]

Then

\[
 u_k=R_k\cos\sigma_k,\quad v_k=R_k\sin\sigma_k,
 \quad z_-=\overline{z_+}=u_k-i v_k.
\]

Here `u_k,v_k` are positive integers; the different notation avoids confusing the cap `A_k` with a coordinate.

### 4.1 Separation of all relevant angles

For every `j>=1`,

\[
 \theta_j\ge\frac{100}{101}10^{-j},\qquad
 \sum_{\ell>j}\theta_\ell<\frac19 10^{-j},\qquad
 \sigma_k<\frac19. \tag{4.3}
\]

The first inequality follows by integrating `1/(1+x^2)` on `[0,10^{-j}]`; the others follow by comparison with a geometric series. In particular

\[
 \theta_j>2\sum_{\ell>j}\theta_\ell. \tag{4.4}
\]

Thus all sums `sum b_j theta_j`, with `b_j in {-1,0,1}`, are distinct: the first nonzero coefficient of the difference between two such sums dominates the tail, whose coefficients have absolute value at most two. Similarly, all `2^k` cap points in (4.1) are distinct. Their arguments are `sum epsilon_j theta_j` in `[-sigma_k,sigma_k]`, so their real parts are positive. The opposite cap is disjoint. Hence

\[
 |A_k|=2^k,\qquad |S_k|=2^{k+1}. \tag{4.5}
\]

### 4.2 The hull and the diameter are actual

We have

\[
 0<v_k<u_k,\qquad v_k\ge R_k/\sqrt{101}>R_k/20.
\]

The four points `z_+,z_-,-z_+,-z_-` are the corners of the rectangle

\[
 [-u_k,u_k]\times[-v_k,v_k].
\]

The grid `B_k` lies strictly inside this rectangle. Every point of `S_k` is an exposed point of the radius-`R_k` disk, and therefore of `conv(P_k)`. It follows that

\[
 \operatorname{vert}(\operatorname{conv}P_k)=S_k. \tag{4.6}
\]

Also `B_k` lies inside the disk of radius `R_k/10`. Since `P_k` is in the closed disk of radius `R_k`, equality in the diameter bound `|p-q|<=2R_k` forces `p,q` to be antipodal points of `S_k`. Consequently the **whole** diameter graph of `P_k` is exactly

\[
 \{\{z,-z\}:z\in A_k\},
\]

a matching of size `2^k`. All these hull chords cross at the origin; all their endpoints are in convex position. In particular

\[
 \boxed{\tau_{4N_k}(P_k)=2^k.} \tag{4.7}
\]

### 4.3 Cardinality and distinct-distance estimates, with uniform quantifiers

The sets in (4.2) are disjoint, so exactly

\[
 n_k=|P_k|=(2m_k+1)^2+2^{k+1}.
\]

As `k -> infinity`,

\[
 n_k\sim N_k/100,\qquad
 \log N_k=k(k+1)\log 10+O(1),\qquad
 \log n_k=k(k+1)\log 10+O(1). \tag{4.8}
\]

Indeed `0<sum_j log(1+10^{-2j})<1/99`, and `2^k=o(sqrt(N_k))`.

The arithmetic input is the classical Landau--Ramanujan estimate

\[
 \mathcal B(X):=|\{1\le s\le X:s=x^2+y^2\text{ for some }x,y\in\mathbb Z\}|
 \asymp X/\sqrt{\log X}\quad(X\longrightarrow\infty). \tag{4.9}
\]

These are ordinary rational integers; the constants in (4.9) are absolute and do not depend on `k` or on a varying number field.

Every squared distance of `P_k` is an integer sum of two squares at most `4N_k`, so

\[
 D(P_k)\le\mathcal B(4N_k).
\]

Conversely every integer sum of two squares at most `4m_k^2` is realized in `B_k`: use the absolute values of its two coordinates, each at most `2m_k`, as a difference vector in the grid. Therefore

\[
 \mathcal B(4m_k^2)\le D(P_k)\le\mathcal B(4N_k).
\]

Since `4m_k^2~N_k/100`, (4.8)--(4.9) give

\[
 \boxed{D(P_k)\asymp N_k/\sqrt{\log N_k},\qquad
       K(P_k)\asymp k\asymp\sqrt{\log n_k}.} \tag{4.10}
\]

In particular `D(P_k)/n_k -> 0`. For every fixed proposed linear-distance threshold `c_0>0`, the alternative `D(P_k)>=c_0 n_k` fails for all sufficiently large `k`. These examples themselves have the sharp order of growth, not a violation of the sharp conjecture.

---

## 5. The entire upper distance spectrum and its exact covers

All pairs between `A_k` and `-A_k` have length at least

\[
 2R_k\cos\sigma_k>3R_k/2.
\]

All other pairs have length at most `11R_k/10`: this is immediate for shell-to-core pairs; core-to-core pairs are even shorter; same-cap pairs have length at most `2R_k sin sigma_k<2R_k/9`. Thus all opposite-cap colors precede every other color in the **global** decreasing distance order of `P_k`.

For `epsilon,eta in {-1,1}^k`, put

\[
 b=(\varepsilon-\eta)/2\in\{-1,0,1\}^k,
 \qquad \delta_b=\sum_{j=1}^k b_j\theta_j.
\]

Then

\[
 |z_\varepsilon-(-z_\eta)|^2
     =4N_k\cos^2\delta_b. \tag{5.1}
\]

By (4.4), and by strict monotonicity of `cos^2 x` as a function of `|x|<=sigma_k<pi/2`, two labels in (5.1) agree exactly when their `b` vectors agree up to sign. Hence the number of opposite-cap colors is exactly

\[
 M_k=\frac{3^k+1}{2}. \tag{5.2}
\]

### 5.1 Every one of these actual graphs is a matching

For `b=0`, the graph is the diameter matching of size `2^k`. For nonzero `b`, put `h(b)=|{j:b_j!=0}|`. Fix the representative `b`, rather than `-b`. On its support, `(epsilon_j,eta_j)` is forced; off its support the common value has two choices. This produces `2^{k-h(b)}` edges. The representative `-b` produces the reverse sign assignment and another `2^{k-h(b)}` edges.

These two sets of edges have disjoint endpoints, since their positive-cap endpoints have opposite prescribed signs on the nonempty support of `b`; their negative-cap endpoints do likewise. Different choices of the remaining signs also have distinct endpoints. By the separation of pair types above, there are no further edges of that color. Thus

\[
 \boxed{\tau_{4N_k\cos^2\delta_b}(P_k)
        =2^{k-h(b)+1}\quad(b\ne0).} \tag{5.3}
\]

This is an exact matching and vertex-cover count, not just a representation count.

### 5.2 An exponentially long initial segment of large-cover colors

For `0<=r<=k`, define

\[
 T_{k,r}=\frac{3^r+1}{2}.
\]

The largest `T_{k,r}` distance colors are precisely those with

\[
 b_1=\cdots=b_{k-r}=0. \tag{5.4}
\]

To check the order, the absolute value of any sum supported on the last `r` coordinates is at most their total angle. If a sum has a first nonzero coefficient at `j<=k-r`, its absolute value is at least `theta_j-sum_{ell>j} theta_ell`, which is larger than the entire last-`r` total by (4.4). Monotonicity in (5.1) proves (5.4).

It follows that every one of these first `T_{k,r}` actual graphs has

\[
 \tau_s(P_k)\ge2^{k-r}. \tag{5.5}
\]

For `r>=1` the exact minimum is `2^{k-r+1}`; for `r=0` it is `2^k`. The weaker uniform bound (5.5) suffices.

### 5.3 Cover of each whole prefix

Let `C_t` be the largest `t` colors, for `1<=t<=M_k`. All their edges join `A_k` to `-A_k`, so `A_k` is a cover. Their union contains the diameter matching. Therefore

\[
 \boxed{\tau_{P_k}(C_t)=2^k\quad(1\le t\le M_k).} \tag{5.6}
\]

These families are proper: there are shorter colors, for example inside the nontrivial core grid.

Take `r_k=floor(k/4)` and `T_k=T_{k,r_k}`. Equations (4.8), (5.5), and (5.6) yield the two uniform limits

\[
 \min_{1\le j\le T_k}
 \frac{\tau_{s_j}(P_k)}{\sqrt{\log n_k}}
 \ge\frac{2^{k-r_k}}{\sqrt{\log n_k}}
 \longrightarrow\infty, \tag{5.7}
\]

\[
 \min_{1\le t\le T_k}
 \frac{\tau_{P_k}(C_t)}{t\sqrt{\log n_k}}
 \ge\frac{2^k}{3^{r_k}\sqrt{\log n_k}}
 \longrightarrow\infty. \tag{5.8}
\]

Here `2/3^(1/4)>1`, while `sqrt(log n_k)~sqrt(log 10) k`. Also

\[
 \frac{\log T_k}{\sqrt{\log n_k}}
 \longrightarrow\frac{\log3}{4\sqrt{\log10}}>0.
\]

Consequently, for **every fixed** `C>0` and `a>=0`, eventually none of the first `ceil((log n_k)^a)` colors has cover at most `C sqrt(log n_k)`, and no prefix of that many colors has cover at most `C` times its number of colors times `sqrt(log n_k)`. This rigorously refutes those diameter/fixed-prefix/polylogarithmic-prefix versions of a universal low-distance cover theorem.

It does **not** refute a theorem allowing an arbitrary distance or an arbitrary, possibly much longer, prefix.

---

## 6. Actual sparse colors, actual cross-distances, and non-EXT status

### 6.1 The later two-edge color

The maximum value of `|delta_b|` is `sigma_k`, attained only by `b=(1,...,1)` and its negative. Thus the shortest opposite-cap length is

\[
 \ell_*=2R_k\cos\sigma_k=2u_k.
\]

Its actual graph consists exactly of

\[
 \{(u_k,v_k),(-u_k,v_k)\},\qquad
 \{(u_k,-v_k),(-u_k,-v_k)\}. \tag{6.1}
\]

The squared color is `4u_k^2`, and its global decreasing rank is `M_k`. Its cover number is two. These are precisely the edges from the two-cap theorem, with `rho=1/10` and `w=2sigma_k`.

Since `K(P_k)->infinity`, for all sufficiently large `k`, deleting the two positive-cap points `(u_k,v_k),(u_k,-v_k)` leaves at least two points, extinguishes this actual color, and gives

\[
 K(P_k\setminus\{z_+,z_-\})
 \ge\frac{n_k-2}{D(P_k)-1}>K(P_k). \tag{6.2}
\]

The difference between the displayed lower bound and `K(P_k)` is exactly

\[
 \frac{n_k-2D(P_k)}{D(P_k)(D(P_k)-1)}>0.
\]

Thus no EXT claim is made for these sets. In fact they violate EXT by a completely specified two-vertex deletion.

### 6.2 A four-edge shell-to-core cross-distance

The largest distance between the shell `S_k` and the actual square core `B_k` has squared value

\[
 t_*=N_k+2m_k^2+2m_k(u_k+v_k). \tag{6.3}
\]

Its **entire** actual graph consists exactly of the following four disjoint edges:

\[
 \begin{array}{ll}
 (u_k,v_k)\leftrightarrow(-m_k,-m_k),&
 (u_k,-v_k)\leftrightarrow(-m_k,m_k),\\
 (-u_k,-v_k)\leftrightarrow(m_k,m_k),&
 (-u_k,v_k)\leftrightarrow(m_k,-m_k).
 \end{array} \tag{6.4}
\]

**Verification of all endpoints and other possible pair types.** At a shell point `p=(x,y)`, the farthest core point is the corner with coordinate signs opposite to those of `p`; both coordinates of `p` are nonzero. The squared maximum is `N_k+2m_k^2+2m_k(|x|+|y|)`. On these two narrow caps,

\[
 |x|+|y|=R_k(\cos|\phi|+\sin|\phi|)
\]

is strictly increasing for `0<=|phi|<=sigma_k<pi/4`. Its maximum occurs only at the four extreme shell points in (6.4). Since `m_k>=1`, the four corners are distinct. Thus these are all maximum cross-distance pairs.

This length is greater than `R_k`, while all same-cap and core-to-core lengths are less than `R_k`. It is at most `11R_k/10`, while all opposite-cap lengths exceed `3R_k/2`. Hence neither internal palette contributes any other edge of color `t_*`. This checks, rather than assumes, the isolation condition in Section 2.2. The cover number is exactly four. If `K(P_k)>4`, deleting the four actual core corners also gives a strict ratio improvement.

### 6.3 A long-prefix palette can still give an increment

The whole largest-color family `C_{M_k}` is covered by `A_k`, and

\[
 \frac{\tau_{P_k}(C_{M_k})}{M_k}
   =\frac{2^{k+1}}{3^k+1}\longrightarrow0. \tag{6.5}
\]

Deleting all `2^k` positive-cap vertices extinguishes every one of these `M_k` colors. Thus this much longer prefix also gives an explicit ratio improvement for large `k`.

Equations (5.8) and (6.5) deliberately distinguish **short prefixes**, which are obstructed, from unrestricted ordered-longest families, which remain a possible route. They must not be conflated.

---

## 7. Filling the disk: the locally rare matching color has a linear actual cover

Keep `N_k,R_k,S_k,u_k,v_k` exactly as above, but now put

\[
 Q_k=\{(x,y)\in\mathbb Z^2:x^2+y^2\le N_k\}. \tag{7.1}
\]

Then `S_k subset Q_k`. Elementary area comparison gives

\[
 n'_k=|Q_k|=\pi N_k+O(\sqrt{N_k}).
\]

Moreover every represented integer up to `N_k` is realized from the origin, and every squared distance is at most `4N_k`. Thus

\[
 \mathcal B(N_k)\le D(Q_k)\le\mathcal B(4N_k),
\]

so again

\[
 D(Q_k)\asymp n'_k/\sqrt{\log n'_k},\qquad
 \log n'_k\asymp k^2. \tag{7.2}
\]

The selected `2^k` antipodal edges from `S_k` are still actual diameter edges of `Q_k`. All their endpoints are still exposed hull vertices. There may be additional lattice points on the same outer circle; that only increases the diameter matching and its cover. In fact the full diameter graph consists of all antipodal pairs of lattice points of norm squared `N_k`.

### The actual interior matching

Set, using integers only,

\[
 U_k=\left\lfloor\frac{v_k^2}{8u_k}\right\rfloor,
 \qquad V_k=\lfloor v_k/2\rfloor.
\]

For every integer pair `|t|<=U_k`, `|y|<=V_k`, take the edge

\[
 p_{t,y}=(-u_k+t,y),\qquad
 q_{t,y}=(u_k+t,y). \tag{7.3}
\]

It has squared length `4u_k^2`, the color which had only the two edges (6.1) on `S_k`.

All endpoints in (7.3) are actual **interior** points of `Q_k`. Indeed, since `v_k<u_k`,

\[
 \begin{aligned}
 |p_{t,y}|^2,|q_{t,y}|^2
 &\le (u_k+U_k)^2+V_k^2\\
 &\le u_k^2+\frac{v_k^2}{4}
       +\frac{v_k^4}{64u_k^2}+\frac{v_k^2}{4}\\
 &\le u_k^2+\frac{33}{64}v_k^2
 <N_k.
 \end{aligned} \tag{7.4}
\]

They form a matching: within each side the coordinate pair determines `(t,y)` uniquely, and `U_k<=u_k/8` makes all left endpoints have negative first coordinate and all right endpoints positive first coordinate. There are exactly

\[
 L_k=(2U_k+1)(2V_k+1)
\]

pairwise vertex-disjoint actual edges. The elementary inequality `2 floor(x)+1>=x` for `x>=0` yields

\[
 L_k\ge\frac{v_k^3}{16u_k}
      \ge\frac{N_k}{16\,101^{3/2}}, \tag{7.5}
\]

where `v_k>=R_k/sqrt(101)` and `u_k<=R_k` were used. Since `n'_k<=(2R_k+1)^2<=9N_k`,

\[
 \boxed{\tau_{4u_k^2}(Q_k)\ge L_k
    \ge\frac{n'_k}{144\,101^{3/2}}.} \tag{7.6}
\]

Thus precisely the locally exposed two-edge color of a convex diameter-matching endpoint set can have a **linear** cover in the full, genuinely low-distance planar configuration. These are not abstract color witnesses: the integer coordinates of every edge in the matching are given in (7.3), and (7.4) verifies their membership.

The two-cap deletion theorem does not apply to (7.1), because its remaining points are not confined to the small central disk. This is an actual obstruction to extending that certificate without a global endpoint argument.

Also, any nonempty prefix of `t` longest colors of `Q_k` contains its diameter matching, so it has cover at least `2^k`. Therefore the short-prefix obstruction (5.8) holds for `Q_k` too, with `n'_k` in place of `n_k`, for `t<=T_k`. The ordering and individual matching formulas (5.3)--(5.5) are **not** asserted for `Q_k`: the newly added points can insert new colors into the global upper spectrum.

No lower bound of the form (1.2) for the minimum over **all** colors of `Q_k` is proved. No EXT assertion about `Q_k` is made.

---

## 8. What remains missing for a closing theorem

The proved certificates exclude particular geometries from the high-`K` EXT class. They do not show that every high-`K` configuration has one of those geometries.

In particular:

- A universal upper bound `tau_diameter=O(sqrt(log n))` in the low-distance regime is false, even on actual lattice disks.
- Looking only at a fixed or polylogarithmic number of the longest colors, or only at the corresponding prefix-cover ratios, cannot establish a universal small-cover theorem. The exact obstruction is (5.7)--(5.8).
- Selecting a large convex diameter matching and finding a locally sparse chord length does not produce a cover of the actual color graph. The filled-disk example makes the discrepancy as large as `2` versus `c n`.
- On the other hand, the explicit `P_k` is defeated by actual later colors and by a sufficiently long palette family. Thus it is not an obstruction to the full EXT method or to (1.1).
- Passing to an exact ratio-maximizing subset could remove the shell, alter the hull, and change the ordered spectrum. No preservation of the constructed obstruction under that selection is claimed.

What is still needed is a genuinely global geometric argument: on **every** relevant EXT set, either control all additional endpoints of some proposed sparse color/family, or find a different actual deletion with extinguished-color count greater than its vertex cost divided by `K`. Nothing here upgrades the elementary convex-layer inequality to `K^2<=C log n`.

Accordingly, the proposed universal dichotomy (1.1), its restriction to EXT sets, and the sharp distinct-distances conjecture all remain unresolved by this investigation. The results above are a rigorous obstruction to several specific diameter/local-endpoint approaches, together with concrete density-increment certificates in configurations where the global endpoint issue can be checked.

---

## 9. Verification and files

The exact-integer verification script is

`Submission/verify_extremal_distance_cover_geometry.py`.

Its saved output is

`Submission/extremal_distance_cover_geometry_verification.txt`.

The script checks:

- every opposite-cap edge and color for `k=2,...,8`, including the exact matching degrees, palette size `(3^k+1)/2`, all initial-segment identifications, and the diameter cover;
- the hull vertex set, the two rare-color endpoints, all four maximum-cross-distance endpoints, and the strict separation from all other pair types;
- for `k=2`, the full palette of `P_2` (using exact grid difference vectors), **all** shell-to-core pairs, and every endpoint of the filled-disk matching;
- the endpoint-depth rank inequality and maximum-cross-distance hull property on 204 actual finite point sets, including collinear examples;
- exact large-parameter coordinate and disk-membership inequalities through `k=128`.

All checks passed. The small case `P_2` has `n=10209`, `D=15444`, and is explicitly **not** advertised as already being in the asymptotic low-distance regime. The infinite-family conclusions follow from the proofs and the uniform arithmetic estimate (4.9), not from finite numerical extrapolation.

`Spec.lean` SHA256 before and after the investigation:

`c2fbaabe5ad8088f856ca97625747c7a01754f3c149dd6a493454e776de290db`.
