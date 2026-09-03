# Global star-dominance continuation: a sharp budget discount and a shape-general resistant-set theorem

## Outcome — no unrestricted Erdős–Sós closure

**The unrestricted Erdős–Sós theorem, and the unrestricted implication `W_k(G) => T embeds`, remain unproved by this continuation.** I did not obtain a counterexample to either. In particular, I do not turn the failure of a star certificate into the failure of the actual punctured-tree forest.

There are three proved results worth retaining:

1. **Simultaneous-root discounted dominance.** Starting with a prescribed-center star certificate, expanding several component roots at once permits a sharp reduction of the minimum-degree requirement from `e` to
   \[
   e-\sum_{i\in S}(h_i-1),
   \]
   where `h_i` is the number of nonleaf neighbors of the selected component root. The proof pays both the deleted centers and all isolated child branches before applying the reviewed dominance theorem. The bound is sharp for forests of two-edge-legged spiders.
2. **An all-roles, all-high-vertices obstruction to the star-deck proxy.** In the literal-critical hosts
   \[
   K_{r+1,r(r+1)+1},\qquad k=2r+1,
   \]
   every target with `Delta(T)<=r` has **no** punctured-forest star certificate at **any** high vertex and **any** hole, although the host contains every k-edge tree and covers every high vertex. This is a Hall-capacity obstruction, not merely the already known coarse minimum-degree shortfall. The smallest displayed instance is the 5-edge path in `K_{3,7}`.
3. **A genuine shape-general copy-or-resistance theorem.** For hosts partitioned into complete `K_{c,c+1}` chambers, arbitrary additional edges are allowed. An explicit two-color condition across a target edge gives either a full T-copy or an original-host set `X=B_i` with
   \[
   2d_G(v)-d_{G[X]}(v)\le k-1\quad(v\in X).
   \]
   Thus the conclusion already follows from `W_k`, not just full incidence criticality. This extends the chamber route beyond the old uniform rooted-star branches; the proof also handles a return to the donor chamber and the capacity-tight two-cycle case.

The third result applies to a fully critical nonbipartite family and a subdivided-double-star target for which **every proper connected core fails the coarse cost-free core budget**. Thus the positive progress is not a restatement of that budget criterion.

Only this report and a small targeted checker/log were added. No Spec or shared Lean file was edited, and no new Lean formalization is claimed.

---

## 1. Exact global premises and the distinction between two decks

All graphs below are finite, simple, and undirected. Embeddings are injective homomorphisms, not induced embeddings. Put

\[
 a=(k-1)/2,\qquad p_G(v,X)=2d_G(v)-d_{G[X]}(v).
\]

For a proper-induced critical host,

\[
 e(G)=a|G|+\eta,\quad \eta>0,\qquad
 e_G(U)\le a|U|\quad(U\subsetneq V(G)),
\]

one has, for every nonempty X,

\[
 I_G(X)=e(G)-e(G-X)\ge a|X|+\eta,
 \qquad
 \sum_{v\in X}p_G(v,X)=2I_G(X)>(k-1)|X|.                 \tag{1}
\]

Consequently G satisfies `W_k`, meaning every nonempty X contains a vertex of potential at least k.

Fix any high vertex s, put `H=G-s` and `A=N_G(s)`. The exact residual condition is

\[
 \forall\varnothing\ne X\subseteq V(H),\quad
 \exists v\in X:\quad
 2d_H(v)-d_{H[X]}(v)+2\mathbf1_A(v)\ge k.                \tag{2}
\]

For `u in V(T)`, the components of `T-u` are rooted at the former neighbors of u. The **actual zero-defect deck** asks for an embedding of this forest in H with every root in A. This is equivalent to a full copy with `u -> s`.

A different, more restrictive object is its **star-certificate deck**: replace each nontrivial component of `T-u` by a star of the same edge count, retaining its marked root as center, and ask for disjoint stars with centers in A. Isolated components may be omitted at this stage and placed later in unused A.

The reviewed theorem in `WeightedListForestFindings.md` makes a star certificate sufficient when its degree hypotheses are met. It does **not** make a star certificate necessary for a particular rooted forest. Section 3 shows that this distinction survives optimizing over every u and every high s.

The one-defect initialization from `WkGlobalContinuation.md` is retained: in a least-parameter counterexample, smaller-parameter induction initializes an actual defect-one state at every high s. Nothing below replaces that actual state by an assumed star certificate.

---

## 2. A sharp simultaneous-root degree discount

### 2.1 Statement

Let `(T_i,r_i)` be nontrivial rooted trees, with

\[
 a_i=e(T_i),\qquad e=\sum_i a_i.
\]

Suppose H has a star certificate at distinct prescribed centers x_i: the sets

\[
 \{x_i\}\cup B_i,\qquad B_i\subseteq N_H(x_i),\quad |B_i|=a_i,
\]

are pairwise disjoint.

Select any set S of components that are not root-centered stars. For `i in S`, let

\[
 d_i=d_{T_i}(r_i),\qquad
 q_i=|\{v\in N_{T_i}(r_i):d_{T_i}(v)=1\}|,
 \qquad h_i=d_i-q_i\ge1.
\]

Thus h_i counts the neighbors that are nonleaves **in that rooted component**. Define

\[
 g(S)=\sum_{i\in S}(h_i-1).
\]

**Theorem 1 — discounted rooted-star dominance.** If

\[
 \boxed{\delta(H)\ge e-g(S),}                           \tag{3}
\]

then all T_i embed disjointly with every `r_i -> x_i`.

The empty choice S recovers the reviewed rooted-star dominance theorem. In maximizing the discount, one may select exactly the roots with `h_i>=2`; adding roots with `h_i=1` has no effect on the bound. Root-centered stars are not discounted as though their entire leaf demand were free.

### 2.2 Proof, with the entire deletion budget displayed

Write

\[
 t=|S|,\qquad q=\sum_{i\in S}q_i,
 \qquad D=\sum_{i\in S}d_i,
 \qquad E=e-D.
\]

Delete all t selected host centers x_i. In each selected target component delete r_i and root its resulting branches at the former neighbors of r_i. Partition its old leaf reservoir B_i into branch reservoirs of the respective branch orders. This is possible because those orders sum to `a_i=|B_i|`.

The resulting star problem has:

* the unselected centers frozen, with their original positive-demand star certificates;
* every selected-root branch flexible in its allocated reservoir;
* exactly q flexible zero-demand branches;
* total leaf demand E.

The original packing makes all reservoirs clean with respect to all frozen stars. Also

\[
 g(S)=D-q-t.
\]

Therefore, in `H'=H-{x_i:i in S}`,

\[
 \begin{aligned}
 \delta(H')
 &\ge\delta(H)-t\\
 &\ge e-g(S)-t\\
 &=e-D+q=E+q.                                          \tag{4}
 \end{aligned}
\]

Apply the reviewed **protected-center star lemma** in H'. It packs all these stars, keeping the unselected original centers fixed and choosing each branch center in its own old-leaf reservoir.

Delete the q centers assigned to isolated branches. The remaining host H'' satisfies

\[
 \delta(H'')\ge E+q-q=E.                               \tag{5}
\]

The remaining nontrivial forest has exactly E edges and has the star certificate just constructed. Apply the reviewed rooted-star dominance theorem **at parameter E**, not at parameter e. It preserves all its centers.

Restore the isolated branch vertices and all deleted original roots. Every branch root is still in its reservoir inside its original B_i, so its edge to the restored root is present. Distinctness follows from the deletions and the disjoint packing. Unselected original roots stayed frozen throughout. This proves (3). **QED.**

This is a simultaneous expansion, not a claim that an under-budget first expansion can be performed and paid for by later steps. Inequality (4) is required before the protected Hall lemma is invoked.

### 2.3 Sharpness

For `i=1,...,t`, let T_i be a spider rooted at its center with d_i legs, each of length two; allow `d_i>=1`. Put

\[
 s_0=\sum_i d_i.
\]

Then

\[
 e=2s_0,\qquad h_i=d_i,\qquad
 g=s_0-t,\qquad e-g=s_0+t.
\]

Take

\[
 H=K_{s_0+t-1,\,2s_0},
\]

and prescribe all t roots in the first part. Partition the second part into star leaf sets of sizes `2d_i`. These are valid disjoint star certificates, and

\[
 \delta(H)=s_0+t-1=e-g-1.
\]

But each desired T_i, with its root in the first part, needs `d_i+1` vertices there: the root and all its terminal leaves. All components together require `s_0+t` such vertices, one more than available. The required rooted forest does not embed.

Thus the degree bound in Theorem 1 cannot be lowered uniformly, even for these simple rooted forests. For a concrete nonzero discount, two center-rooted `P_5`s have `e=8`, `g=2`; `K_{5,8}` fails at degree five despite the star certificate, whereas degree six suffices.

### 2.4 A legitimate punctured-tree consequence

Fix high s and a target hole u. Omit the isolated components of `T-u`, and suppose a star certificate for its nontrivial components has actually been found with centers in A. Their total edge count is

\[
 e_u=k-d_T(u).
\]

Compute g_u from their rooted shapes as in Theorem 1. Then

\[
 \boxed{\delta(G-s)\ge e_u-g_u}                         \tag{6}
\]

suffices for a full copy with `u -> s`.

Indeed, Theorem 1 embeds the nontrivial components. If there are q_0 isolated components, they have used `k-q_0` vertices, leaving at least q_0 members of A unused because `|A|>=k`. Put the isolated marks there and restore u at s.

The star-certificate premise in this corollary is substantial. Weighted Hall for the **root lists** alone cannot manufacture the initial stars at degree `e_u-g_u`; Section 3 gives a critical counterexample to that shortcut.

---

## 3. No global punctured-star certificate, despite coverage at every high vertex

### 3.1 A fully critical family

For `r>=2`, let

\[
 k=2r+1,\qquad b=r(r+1)+1,\qquad G=K_{r+1,b},
\]

with parts P,Q of sizes `r+1,b`. Then

\[
 |G|=r+1+b,\qquad e(G)=(r+1)b=r|G|+1.                 \tag{7}
\]

Every proper induced subset is r-sparse. If its part counts are x,y and `x<=r`, then `xy<=r(x+y)`. If `x=r+1`, properness gives `y<=b-1=r(r+1)`, and

\[
 xy-r(x+y)=y-r(r+1)\le0.
\]

Thus this satisfies the literal surplus-one threshold and all proper-induced criticality inequalities.

Exactly the vertices of P are high: their degree b is at least k, while vertices of Q have degree `r+1<k`.

### 3.2 All choices of high vertex and target hole fail the star certificate

Let T be **any** k-edge tree with `Delta(T)<=r`. Fix arbitrary `s in P` and arbitrary `u in V(T)`. Then

\[
 H=G-s=K_{r,b},\qquad A=N_G(s)=Q.
\]

Every center of a punctured star certificate must lie in Q. Consequently every star leaf must lie in `P-{s}`, which has only r vertices. The total required number of star leaves is

\[
 \sum_i e(T_i)=e(T-u)=k-d_T(u)\ge r+1.                 \tag{8}
\]

This is impossible. More explicitly, for the set R of all nontrivial-component centers, the Hall witness consisting of **all their leaf slots** has neighborhood

\[
 \bigcup_i(N_H(x_i)\setminus R)=P-\{s\},
\]

of size r, smaller than the total demand (8).

This argument permits:

* every hole u, including leaves and nonleaves;
* every high host vertex s;
* arbitrary center choices and arbitrary leaf rematchings;
* arbitrary reservoirs and root-list subchoices inside A;
* passing to any residual subgraph while keeping those attachment requirements.

None can increase the r-vertex leaf capacity. In particular, this is not an obstruction confined to a bounded-support reconfiguration class.

### 3.3 Yet every target embeds and every high vertex is covered

A k-edge tree has `2r+2` vertices, so its smaller bipartition class has size at most `r+1`. Its other class has size at most k, and `b>=k`. Inject the smaller class into P and the other into Q. A chosen member of the smaller class can be sent to any prescribed s in P.

This embeds **every** k-edge tree and covers every high s, including all targets in Section 3.2.

For `r=2`, the host is `K_{3,7}` with `n=10`, `e=21=2n+1`. The 5-edge path has maximum degree two, so all its punctured star certificates fail, while its full alternating copy uses three vertices of each host part.

### 3.4 Why the failed Hall certificate is not a resistance certificate

All root lists may be the full set A=Q. They satisfy weighted Hall for the nontrivial component orders since

\[
 |A|=b\ge k\ge\sum_{i\text{ nontrivial}}|T_i|.
\]

Nevertheless the stars themselves cannot be packed. For vertices of A, the exact weighted-apex potential on X=A is

\[
 2d_H(v)-d_{H[A]}(v)+2=2r+2=k+1,                      \tag{9}
\]

not a resistant value. Moreover,

\[
 I_G(A)=(r+1)|A|>r|A|.
\]

Every center transversal has zero induced edges, so the reviewed star-exchange potential is already zero; its missing degree hypothesis cannot be repaired by minimizing that same potential more globally.

**Conclusion.** The implication

> no zero-defect punctured **star** certificate at any high vertex and any hole implies a resistant set or a low-incidence set

is false. This does **not** refute the desired implication with the premise “no zero-defect embedding in the actual punctured-forest deck.” In this family the actual deck has zero-defect states. Any successful WH-based global optimization must retain that distinction or introduce genuinely richer, shape-sensitive certificates.

---

## 4. A shape-general chamber theorem: full copy or an actual W-resistant set

This is the positive global extraction obtained by combining the certificate viewpoint with exact two-color capacities. The one-unit-deficient side is not embedded by falsely applying WH at too large an edge parameter.

### 4.1 Target and host hypotheses

Choose an edge xy of a k-edge tree T. Let T_x,T_y be the two components of `T-xy`, rooted at x,y respectively. For `z in {x,y}`, let

\[
 \alpha_z=|\{v\in T_z:d_{T_z}(z,v)\text{ is even}\}|,
 \qquad
 \beta_z=|\{v\in T_z:d_{T_z}(z,v)\text{ is odd}\}|.
\]

Thus alpha is the size of the root's color class, and

\[
 k+1=\alpha_x+\beta_x+\alpha_y+\beta_y.
\]

Suppose some integer `c>=1` satisfies

\[
 \boxed{
 3c\le k-1,\qquad
 \alpha_x,\alpha_y\le c+1,\qquad
 \beta_x,\beta_y\le c.
 }                                                       \tag{10}
\]

Suppose the **entire host vertex set** is partitioned into a nonempty finite family of chambers

\[
 M_i=A_i\mathbin{\dot\cup}B_i,\qquad
 |A_i|=c,\quad |B_i|=c+1,
\]

and every A_i–B_i interface is complete. All other edges—inside the parts and between chambers—are arbitrary.

**Theorem 2 — copy-or-resistance dichotomy.** At least one of the following holds:

* T embeds in G;
* some B_i is W-resistant:
  \[
  \boxed{2d_G(v)-d_{G[B_i]}(v)\le k-1\quad(v\in B_i).}   \tag{11}
  \]

In the second outcome,

\[
 I_G(B_i)\le (k-1)|B_i|/2.                              \tag{12}
\]

Consequently every `W_k` host in this chamber class contains T. Full induced criticality is more than sufficient.

The target halves can have arbitrary shape and arbitrary depth subject to (10). They are not assumed to be stars or forests of uniform twigs.

### 4.2 First full-copy certificates

Call any cross-chamber edge from B_i to A_j an **arc** `i -> j`. This records the part types of an undirected edge; it is not an assumed orientation of G. There are no loops in this auxiliary digraph.

**A B_i–B_j edge, i distinct from j, gives T immediately.** Use it for xy and put one half in each chamber with its root in B. Its root-color class needs at most `c+1` B positions and its other class at most c A positions. Completeness supplies all its edges. Hence T-freeness excludes every cross-chamber B–B edge.

**If at least one alpha is at most c, a single arc gives T.** Put that half's root at the A endpoint and the other half's root at the B endpoint. The recipient uses at most c A positions and at most c B positions; the donor fits by (10). The choice of which target endpoint goes to which host endpoint is adaptive.

In this nonexceptional case, a T-free host has no arcs at all. The resistance bound will follow from Section 4.5.

It remains to handle

\[
 \alpha_x=\alpha_y=c+1.                                \tag{13}
\]

### 4.3 A movable leaf always exists in the exceptional case

Each rooted half in (13) has a **nonroot leaf in its root-color class**.

To prove this, suppose all c nonroot vertices of that color had degree at least two within the half. The root has degree at least one, because `c+1>=2`. The degree sum over this color would be at least `2c+1`. But that sum equals the half's number of edges,

\[
 \alpha_z+\beta_z-1=c+\beta_z\le2c,
\]

a contradiction. Such a nonroot leaf is also a leaf of the full T. Its distance from the root need not be two; it can be arbitrarily far away within the permitted half size.

Fix such a leaf ell in a recipient half and let w be its parent. In the usual placement of the recipient root in A_j, ell would use an A_j position and w a B_j position. Moving ell elsewhere releases exactly the one excessive A_j position in (13).

**An arc `i -> j` plus an internal edge in B_j gives T.** Put the donor root at the arc's B_i endpoint and the recipient root at its A_j endpoint. Use the internal B_j edge for `w ell`, with w at one endpoint and ell at the other. Place the rest of the recipient by its two colors.

The recipient's remaining root-color vertices number exactly c and fit A_j, including its prescribed root. Its opposite-color vertices, together with the relocated leaf, use `beta+1<=c+1` positions in B_j. Fixing w at the chosen edge endpoint causes no collision. Thus, in a T-free host, **every chamber receiving an arc has independent B_j**.

### 4.4 Two arcs, including a return to the donor chamber

Suppose there are arcs `i -> j -> h`. Use the first for xy. Put the recipient's chosen leaf parent w at the B_j endpoint of the second arc, and ell at its A_h endpoint. All other recipient vertices fit A_j,B_j as above, now with ell outside chamber j.

If `h != i`, all three chambers are distinct, so the donor and the external leaf are automatically disjoint.

If `h=i`, the external leaf occupies one A_i position. The donor can still be embedded whenever its opposite-color count is at most `c-1`: choose its beta A_i positions avoiding that port. Its root-color class fits B_i as before. This explicitly accounts for the repeated chamber, rather than treating the three indices as distinct.

Therefore:

* If one of `beta_x,beta_y` is at most `c-1`, always choose that half as donor. Every directed walk of length two gives a full copy, including a two-arc return.
* If both beta values equal c, a walk on three distinct chambers still gives a copy, but the return construction has a real one-position collision. In this case
  \[
  k+1=2(c+1)+2c=4c+2,\qquad k-1=4c.                    \tag{14}
  \]

We do not claim the colliding return construction works in the latter case.

### 4.5 Extracting an original-host resistant set

Assume T is absent.

If the arc digraph has a sink i, there are no B–B cross edges by Section 4.2 and no B_i–A_j edges with `j != i`. Hence, for every `v in B_i`,

\[
 d_G(v)=c+d_{G[B_i]}(v),
\]

and therefore

\[
 p_G(v,B_i)=2c+d_{G[B_i]}(v)\le3c\le k-1.              \tag{15}
\]

This proves (11).

A sink exists automatically in the nonexceptional case, since there are no arcs. It also exists in the exceptional case whenever one beta is at most `c-1`: otherwise every vertex has an outgoing arc and hence starts a directed walk of length two, forbidden by Section 4.4.

The remaining case has (13), both beta values c, and no sink. There can be no directed two-arc path on three distinct chambers. The auxiliary digraph is therefore a disjoint union of closed two-cycles. Indeed, for any `i -> j`, every outgoing arc of j must return to i; since j has one, every outgoing arc of i must return to j. An incoming arc from a third chamber would also give a forbidden three-chamber path.

Every chamber receives an arc, so its B part is independent by Section 4.3. For a paired i,j, all neighbors of B_i lie in `A_i union A_j`. Consequently

\[
 d_G(v)\le2c,\qquad d_{G[B_i]}(v)=0,
 \qquad p_G(v,B_i)\le4c=k-1,                            \tag{16}
\]

using (14). This again proves (11). Summing (11) and using the incidence identity in (1) gives (12). The proof is complete. **QED.**

### 4.6 Where dominance applies, and where a different certificate is essential

Suppose a half is formed by attaching p nontrivial rooted branches to its root and the branches have total edge count c. Its branch forest has at most c vertices in each color class: each of the p components has at least one vertex of each color. Thus its half satisfies `alpha<=c+1`, `beta<=c`.

When the half-root is placed in B, the bare chamber with that root deleted is `K_{c,c}`. One can put the p branch roots in A, allocate c disjoint B leaves as a star certificate, and use the reviewed dominance theorem at the **correct** edge budget c. This justifies arbitrary branch-shape replacement there.

When the half-root is instead placed in A, the bare residual chamber is `K_{c-1,c+1}`. One cannot apply the same c-edge forest theorem at minimum degree `c-1`. Sections 4.2–4.4 use exact color capacity and, when necessary, a relocated target leaf. The two-cycle case is resolved by resistance, not by pretending the lost unit is absent.

In particular, if the two branch forests each have c edges and component counts p,q with `p+q>=c`, then `k-1=2c+p+q>=3c`, and Theorem 2 applies to **all their rooted shapes**. This is one concrete shape-general extension suggested by star dominance; the theorem's actual color-profile formulation is more general still.

---

## 5. A fully critical application outside every coarse connected-core budget

### 5.1 Target

Let `d>=2`. Form T from an edge xy by attaching d paths of length three at x and d paths of length three at y, otherwise disjoint. Then

\[
 k=6d+1,\qquad \Delta(T)=d+1,\qquad \ell(T)=2d.          \tag{17}
\]

This is a nonspider with two branching hubs. Across xy, each half has

\[
 \alpha=d+1,\qquad \beta=2d.
\]

Take `c=2d`. Condition (10) holds, with `3c=k-1`. Moreover `alpha<=c`, so **a single cross-chamber B–A edge already supplies the entire target**. Its branch shapes are endpoint-rooted `P_3`s, not the root-centered stars of the earlier two-hub chamber target.

### 5.2 A literal-critical host family

Use the host construction from `ActualESCounterexampleAttempt.md`, Section 6. For completeness, its critical certificate is recalled here.

Take `m>=5` cyclically indexed chambers, with

\[
 A_i=H_i\mathbin{\dot\cup}L_i,\quad |H_i|=|L_i|=d,
 \qquad |B_i|=2d+1.
\]

Inside A_i put `K_{2d}` minus an antipodal perfect matching; inside B_i put a clique. Add all own-chamber A_i–B_i edges, and all edges from B_i to `H_{i+1}` and `H_{i+2}`. Finally add one previously absent edge

\[
 s\ell_*,\qquad s=b_{0,0},\quad \ell_*=a_{3,d}\in L_3.
\]

Orient A_i forward at cyclic distances `1,...,d-1`, B_i forward at distances `1,...,d`, own-chamber edges from A to B, and cross-chamber edges from B to H. Every base outdegree is `3d`; the base orientation is strongly connected. Orient the extra edge from s to ell_*.

Thus s reaches every vertex, all outdegrees are `3d` except `3d+1` at s, and

\[
 n=m(4d+1),\qquad e(G)=3dn+1.                           \tag{18}
\]

For every proper vertex set U,

\[
 e_G(U)=3d|U|+\mathbf1_{s\in U}-\operatorname{out}(U)
 \le3d|U|.
\]

If U contains s and is proper, reachability supplies an outgoing arc; otherwise the indicator is zero. This proves full induced criticality.

The minimum degree is

\[
 \delta(G)=4d-1.                                       \tag{19}
\]

Indeed, ordinary L vertices have that degree, H vertices have degree `8d+1`, ordinary B vertices degree `6d`, and the two endpoints of the extra edge gain one.

### 5.3 Full copy, and coverage of all high vertices in this family

Use the base edge `b_{0,0} a_{1,0}` for xy. For `i=0,...,d-1`, write the three vertices on an x-arm as `u_i,v_i,w_i`, and those on a y-arm as `u'_i,v'_i,w'_i`. Map

\[
\begin{array}{c|c}
 x & b_{0,0}\\
 u_i,v_i,w_i & a_{0,i},\ b_{0,i+1},\ a_{0,d+i}\\
 y & a_{1,0}\\
 u'_i,v'_i,w'_i & b_{1,i},\ a_{1,i+1},\ b_{1,d+i}.
\end{array}                                             \tag{20}
\]

All vertices are distinct, all arm edges are own-chamber complete cross edges, and the hub edge is the displayed base cross edge. No surplus edge is used.

The high vertices are all H vertices together with s. The B-root construction covers s. For any chosen `z in H_j`, put the A-root at z and the B-root in the previous chamber; the same color injections work. Thus every high vertex of this particular critical family is covered by this target.

### 5.4 Why the coarse connected-core theorem cannot certify this target here

Every component outside a proper connected subtree of a tree contains a target leaf. Hence every proper connected core C of this T has boundary count

\[
 b(C)\le\ell(T)=2d.
\]

Using (17) and (19),

\[
 \delta(G)+b(C)\le(4d-1)+2d=6d-1<6d+2=k+1.             \tag{21}
\]

So **every** such core fails the coarse cost-free condition, regardless of where its boundary vertices could be embedded. The failure is by at least three units using the actual minimum degree, not merely the generic critical lower bound.

This does not exclude the stronger exact residual-degree interface or every other terminal theorem. It shows that the new global chamber extraction/copy construction is not just that coarse core budget in different notation.

At `d=2,m=5`, this gives

\[
 k=13,\quad \Delta(T)=3,\quad n=45,\quad
 e(G)=271=6n+1,\quad\delta(G)=7,
\]

with all eleven high vertices covered. Every coarse proper-core budget has `delta+b<=11`, whereas fourteen is required.

---

## 6. The other global reductions tested, and their precise stopping points

### 6.1 Global optimization of a one-level star deck

Optimizing root lists, center transversals, initial stars, u, and s jointly does not fix the obstruction in Section 3. There simply are no certificates in that proxy state space, while actual zero-defect states exist. The new dominance theorem is a sufficient conversion theorem, not an equivalence between the two state spaces.

Accordingly, an attempted “no star certificate => resistance” theorem is ruled out, even with all roles free and literal criticality. The desired “no actual zero-defect forest => resistance” theorem is not ruled out and remains unproved.

### 6.2 Paying the forest budget by several root expansions

Theorem 1 is a valid improvement precisely because (4) supplies the protected-star degree threshold **before** the substitution and (5) supplies the remaining forest threshold **after** deleting the isolated branches. This improves a genuine premise rather than simply renaming the residual edge count.

It does not give an automatic sequence of further expansions: if (4) fails, later anticipated branchings do not authorize the current Hall step. Endpoint-rooted path components have no positive `h_i-1` discount, so this mechanism does not cure the critical path/star-deck obstruction.

Also, even when the discounted minimum-degree inequality holds, the initial star certificate is a separate requirement. It cannot be inferred by applying weighted root-list Hall at the undiscounted edge count in a host below that degree threshold.

### 6.3 Splitting the forest into smaller-parameter induction calls

For h deleted host vertices S, the exact W deletion estimate is

\[
 p_{G-S}(v,X)=p_G(v,X)-2d_G(v,S)\ge p_G(v,X)-2h,
\]

so the unconditional lower parameter is `k-2h` (when this parameter is nonnegative).

Deleting h target vertices in a connected core leaves `m=k+1-h` vertices in b components and

\[
 e_F=k+1-h-b.
\]

Even the numerical comparison `e_F<=k-2h` needs `b>=h+1`. That comparison would still **not** authorize a forest version of W; such a version is false in general. If one instead joins those b components by `b-1` virtual edges to create an ordinary tree on the same vertices, its edge count becomes `k-h`, leaving an h-unit gap from the guaranteed parameter `k-2h`.

Nor does sequentially applying WH to two groups solve the simultaneous budget: deleting the first group's occupied vertices reduces the residual degrees of the second. Without an actual bound on those neighborhood losses, one cannot charge only each group's separate edge count. The chamber proof succeeds by keeping the two supports disjoint and calculating their color capacities exactly; those supports have not been extracted from a general host.

### 6.4 Using full incidence rather than pointwise W

A full criticality proof would only need a nonempty set X with `I_G(X)<=a|X|`, so in principle summed extraction could be easier. Theorem 2 actually gives pointwise resistance in its chamber setting: a sink gives (15), and the tight return cycle gives (16).

Outside that setting, the Hall-deficient leaf demand does not identify missing original-host incidence. In Section 3, all candidate centers have residual degree r, but their restored apex edge raises their original degree to `r+1>a`; even their whole candidate set has positive incidence surplus. Summing that Hall failure does not reverse this inequality.

The usable global conclusion therefore depends on the **copy-or-structure argument** excluding all other B-boundary edges, not on a bare count of unmatched star slots. No analogous closure of the actual arbitrary-host forest state space was proved here.

---

## 7. Exact remaining barrier and recommended next mathematical step

The least-parameter one-defect initialization remains available. The unfilled step is still to exploit **absence of every actual zero-defect state**, with both the target hole and the embedding allowed to vary, to obtain either:

\[
 2d_H(v)-d_{H[X]}(v)+2\mathbf1_A(v)\le k-1
 \quad(v\in X\ne\varnothing),                          \tag{22}
\]

or, using full criticality, an original-host set with

\[
 I_G(X)\le a|X|.                                       \tag{23}
\]

Neither (22) nor (23) has been proved for a general critical host by this continuation. The chamber theorem proves a real instance of this kind of extraction, but **no theorem partitions an arbitrary residual critical host into its required chambers**, and not every target has the required target-edge profile for a specified chamber size. These hypotheses are not consequences silently supplied by W or by lower-k induction.

The new negative result sharpens what a viable next route must retain:

* It cannot replace all marked branches simultaneously by one-level stars and then regard lack of a certificate as lack of an actual forest.
* A richer certificate needs to remember shape-dependent reuse of the two sides of an interface, or another invariant of comparable strength. Whole-component reembedding remains legitimate and may be necessary.
* Root roles and, for ordinary ES, the high host vertex must remain free; no prescribed-hole conclusion has been assumed.
* Every use of WH must have a verified residual edge budget. Theorem 1 and the donor/recipient distinction in Section 4.6 are valid examples of such bookkeeping, not permission to apply WH at degree approximately k/2 to an arbitrary forest with approximately k edges.

A reasonable next objective is a **copy-or-interface extraction from the actual global deck**, whose interface certificates include both dominated-star configurations and parity-sensitive configurations such as Section 4. The task is to prove that these or other configurations exhaust an arbitrary T-free critical host. That exhaustion is the missing mathematics; it is not a formalization obligation or a theorem established here.

---

## 8. Targeted verification and files

The universal assertions above have complete mathematical proofs. A deliberately small constructive audit was run, rather than a large host/tree search:

```sh
python3 Submission/GlobalStarDominanceContinuationChecks.py
```

Saved files:

* `Submission/GlobalStarDominanceContinuation.md` — this report;
* `Submission/GlobalStarDominanceContinuationChecks.py` — targeted constructions and budget checks;
* `Submission/GlobalStarDominanceContinuationChecks.log` — successful output.

The audit checks:

* two discounted-dominance constructions, including simultaneous roots and a mixed case with a frozen component and an isolated child branch;
* the exact sharpness star certificate in `K_{5,8}` and its forced six-into-five color obstruction;
* all eighteen high-vertex/hole combinations in the `K_{3,7}` path example, its 31 proper induced-subset count types, and full path embeddings;
* five chamber full-copy certificates, including a repair leaf at distance four from its half-root, an internal B edge, a return to the donor chamber, and a three-chamber path with no donor slack;
* equality examples for both sink and paired-cycle W-resistance;
* the 45-vertex critical orientation certificate and eleven edge-by-edge checked copies covering all its high vertices, together with the all-core coarse-budget failure.

No graph-atlas search or tree-embedding backtracker is used. The discounted construction invokes the existing reviewed protected-star and dominance routines at the newly verified residual parameters.

Every pre-existing `Submission/*.lean` checksum matches the pre-task snapshot. In particular, `Submission/Spec.lean` remains

```text
674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103
```

**Final status:** sharp new rooted-forest budget progress and a shape-general global copy/resistance theorem for a specified host class; a rigorous obstruction to the naive global star-certificate proxy; no unrestricted ES proof and no claimed arbitrary-host resistant-set extraction.
