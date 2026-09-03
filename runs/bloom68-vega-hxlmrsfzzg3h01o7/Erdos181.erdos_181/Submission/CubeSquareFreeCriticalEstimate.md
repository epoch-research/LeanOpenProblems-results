# Actual full-square graphs at critical density: positive lemmas and the unresolved global estimate

## Status

**The requested complete route to `R(Q_d) <= C 2^d` is not obtained.** In particular, this report does not prove

\[
 e(S(G))\le (2-\varepsilon)e(G)^{2-2/(d+1)}
                 +K2^{d-1}Ne(G)                                      \tag{0.1}
\]

for arbitrary cube-free original graphs in the specified density range. No absolute `epsilon,K,C_0` satisfying that assertion are claimed. Neither admitted theorem in `Spec.lean` is used.

The positive results below are all-dimensional mathematical statements, not finite-dimensional verification of the conjecture:

1. **A genuine cube-free dimension descent through an actual complete bipartite reservoir.** It produces an injective `Q_d` from a smaller cube, with every original cube edge checked. Its contrapositive gives a smaller-dimensional cube-free **original graph**, and its full-square loss is at most
   \[
      (u+3m/2)Ne,\qquad m=2^{d-1},
   \]
   where `u` is the number of discarded columns. Thus this branch really has the permitted `O(mNe)` error scale. There is also an explicit multiplicity lower bound for the extension.
2. **Full-square-preserving peeling.** Deleting one original edge destroys *both* auxiliary diagonals of every rectangle through it. Accounting for this factor gives a dense actual full-square core, rather than an arbitrarily selected auxiliary subgraph.
3. **An integral, full-size tree-prism ensemble at the critical density.** If `N >= 512*2^d` and `e >= N(N-1)/8`, then for every tree `T` on `m=2^{d-1}` vertices there are at least
   \[
      (N/32)^{2^d}
   \]
   labelled injective copies of `T square K_2`, with an explicit sequential endpoint-capacity bound. All `2^d` original vertices are distinct. When `T` is a spanning tree of `Q_(d-1)`, this enforces all squares along that tree, **not** the other cube edges.
4. **An unconditional paired-colour conclusion for this positive subproblem:**
   \[
      \boxed{R(T\square K_2)\le128|T|\quad\text{for every finite tree }T.}
   \]
   This is not asserted to be a new literature result and is not the hypercube Ramsey theorem.
5. **A quantitative critical-energy route and an exact injective counting calculation.** The energy argument finds a large subrectangle with square density close to its Cauchy--Schwarz floor. A direct, finite-population counting estimate shows precisely why the available cut-norm control does not close a growing cube.
6. **An exact actual-rectangle switching calculation.** It identifies the simultaneous constraints needed for a legal switch; it does not assume that preserving one square preserves the rest of a cube.

The unresolved part is the diffuse, moderately completing case: global cube-freeness has not been converted into an upper square count **below** the critical floor, or into a positive joint probability for all the remaining commuting-square constraints. Sections 7--9 make this gap explicit.

`Submission/Spec.lean` was left unchanged.

---

## 1. Conventions and the numerical target

Let `G=(A,B)` be bipartite, `a=|A|`, `b=|B|`, `N=a+b`, and `e=e(G)>0`. Isolated vertices may be added if the supplied bound on the original vertex count is larger. All graphs and copies are simple, and copies need not be induced.

Put

\[
 h=2^d,\qquad m=h/2,\qquad k=d-1,\qquad \alpha=2/(d+1).
\]

Throughout, `S(G)` is the **full** square graph. Its vertices are the actual edges `xy` of `G`; two vertices `xy,x'y'` are adjacent precisely when their endpoints are distinct and both cross edges `xy',x'y` belong to `G`. Every rectangle contributes both opposite pairs. Write `s=e(S(G))`.

For the zero-one matrix `M` of `G`, set

\[
 T_4=\sum_{x,x'\in A}\sum_{y,y'\in B}
      M_{xy}M_{xy'}M_{x'y}M_{x'y'},
 \quad D_A=\sum_{x\in A}d(x)^2,
 \quad D_B=\sum_{y\in B}d(y)^2.
\]

These are bipartition-respecting homomorphism conventions. Directly separating equal-row and equal-column terms gives

\[
 \boxed{s=2C_4(G),\qquad T_4=2s+D_A+D_B-e.}                 \tag{1.1}
\]

Cauchy--Schwarz twice, followed by `ab<=N^2/4` and `D_A+D_B-e<=(N-1)e`, gives

\[
 \boxed{s\ge\frac{e^4}{2a^2b^2}-\frac{(N-1)e}{2}
             \ge\frac{8e^4}{N^4}-\frac{(N-1)e}{2}.}       \tag{1.2}
\]

At the requested density this implies, retaining the finite correction,

\[
 \frac{s}{e^2}\ge\frac18-\frac{17}{4N}.                   \tag{1.3}
\]

Indeed, the more precise lower bound obtained in this substitution is
`1/8 - 17/(4N) + 1/(8N^2)`.

### Why the coefficient below 2 matters

At fixed `N/h=C` and positive original edge density, `e^alpha -> 16`. Thus (0.1) would say

\[
 \frac{s}{e^2}\le\frac18-\frac{\varepsilon}{16}
                         +O(Kh/N)+o(1),                 \tag{1.4}
\]

contradicting (1.3) for sufficiently large fixed `C`.

There is also a finite check. If

\[
 C\ge\max\{C_0,6,128(K+1)/\varepsilon\},\quad N\ge Ch,
\]

then `e>=4h^2` and `e^alpha>=16` for `d>=1`. The proposed upper bound and (1.3) would require

\[
 \frac{\varepsilon}{16}
 \le\frac{8Km}{N-1}+\frac{17}{4N}
 \le\frac{8K+17/8}{C}<\frac{\varepsilon}{16},
\]

which is impossible. A majority colour followed by a maximum cut gives precisely the original edge-density hypothesis. This verifies the sufficiency of the requested estimate; it does not establish it.

An endpoint-disjoint `Q_k` in `S(G)` gives `Q_d` by orienting the two endpoints of each edge label according to the parity of its source vertex. This lift is used below only when both original endpoint maps really are injective.

---

## 2. Full-square deletion identities

These elementary identities are important because deleting an auxiliary edge or auxiliary vertex alone need not leave a full-square graph.

### 2.1 Deleting one original edge

For an original edge `f`,

\[
 \boxed{s(G)-s(G-f)=2d_{S(G)}(f).}                         \tag{2.1}
\]

There is one rectangle through `f` for each auxiliary neighbour of `f`. Deleting `f` destroys each such rectangle, and hence **two** auxiliary edges: the opposite pair containing `f`, and its other diagonal. There are no other lost rectangles.

In particular, it would be incorrect to charge just `d_S(f)` while claiming to keep a full-square graph.

### 2.2 Deleting original vertices

For one original vertex `v`,

\[
 s(G)-s(G-v)=\sum_{f\ni v}d_{S(G)}(f)\le d_G(v)e.          \tag{2.2}
\]

A rectangle through `v` contains two original edges incident with `v`, so both sides count it twice. Applying (2.2) successively gives, for any original vertex set `U`,

\[
 s(G)-s(G-U)\le e\sum_{v\in U}d_G(v)\le |U|Ne.           \tag{2.3}
\]

This is an upper charge, so repetitions in the sum cause no problem.

### 2.3 Deleting many low-degree rows without paying their number

Suppose `L subset A` and every row in `L` has degree at most `Delta`. Then

\[
 \boxed{s(G)-s(G[A\setminus L,B])
       \le (\Delta-1)_+(a-1)e(G[L,B]).}                   \tag{2.4}
\]

For an edge `xy` whose row lies in `L`, its auxiliary neighbours form edges between

\[
 N_G(y)\setminus\{x\},\qquad N_G(x)\setminus\{y\}.
\]

There are at most `(a-1)(Delta-1)_+` such labels. Every lost rectangle contributes at least two to the sum of these auxiliary degrees over the edges in low rows, whereas its contribution to `s` is exactly two. This proves (2.4).

These statements concern actual rectangles of the current original graph, including the other diagonal. No generic endpoint-labelled extremal estimate is involved.

---

## 3. A genuine cube-free dimension descent using an actual rectangle

This route does use **both** cube-freeness and a strong form of actual rectangle completion. It is more than declaring an auxiliary graph cube-free: the smaller cube-free graph below is an original bipartite subgraph, and its cube-freeness has an explicit injective extension proof.

### Theorem 3.1 -- complete row-reservoir extension

Let `d>=2`, `1<=j<=d-1`, and set

\[
 m=2^{d-1},\qquad q=2^{d-j-1},\qquad
 r=m-q,\qquad D=(j+1)q\le m.                             \tag{3.1}
\]

Suppose there are `R subset A`, `B_0 subset B` such that

\[
 |R|=r,\qquad b_0:=|B_0|\ge m,\qquad R\times B_0\subseteq E(G).
\]

Define

\[
 A_+=\{x\in A\setminus R:d_{B_0}(x)\ge D\},\qquad
 H=G[A_+,B_0].                                          \tag{3.2}
\]

If `H` contains `Q_(d-j)`, then `G` contains an injective `Q_d`.

In fact, if `I_t` denotes the number of labelled bipartition-respecting injective `Q_t` embeddings, then

\[
 \boxed{I_d(G[A,B_0])\ge
   r!\,(jq)!\,(b_0-D)_{m-D}\,I_{d-j}(H).}                \tag{3.3}
\]

Here `(n)_t` is a falling factorial and `(n)_0=1`.

#### Proof: all cube edges and all original vertices are accounted for

View source vertices as `(z,w) in {0,1}^j x {0,1}^{d-j}`. Let `E_0,O_0` be the even and odd vertices with `z=0`. Each has `q` vertices and their induced bipartite graph is `Q_(d-j)`.

Start with an injective copy of this smaller cube in `H`, mapping `E_0` to `A_+` and `O_0` to `B_0`. Put all the other `m-q=r` even source vertices bijectively into `R`. There are `r!` choices for this step.

There are exactly `jq` odd vertices with exactly one neighbour in `E_0`: they are `(e_i,w)` with `w` even and `1<=i<=j`. For each, the one external even neighbour is `(0,w)`. Choose a fresh neighbour in `B_0` of the image of `(0,w)`.

Before the `t`-th such choice, indexed from zero, at most `q+t` columns have been used. The relevant external row has at least `D=(j+1)q` neighbours in `B_0`. Consequently at least

\[
 D-q-t=jq-t
\]

choices remain. This gives at least `(jq)!` choices for the whole private-neighbour stage.

Exactly `D=q+jq` odd vertices have now been placed. Every remaining odd vertex has no neighbour in `E_0`, since its first `j` coordinates have weight at least two. Map these `m-D` vertices arbitrarily and injectively into the unused columns of `B_0`, in `(b_0-D)_(m-D)` ways.

Now check every kind of source edge:

* Edges within the face `z=0` were checked by the smaller cube embedding.
* Every edge from `E_0` leaving that face goes to one of its specifically chosen private odd neighbours.
* Every edge with even endpoint outside `E_0` is present because that even endpoint maps to `R` and every odd endpoint maps to `B_0`.

Thus every cube edge is present, including all cycle-closing and commuting-square edges. The even endpoint map is injective into the disjoint sets `A_+` and `R`; the odd endpoint map is injective by the successive fresh-column choices. The two host parts are disjoint. Hence all `2m` original vertices are distinct.

Different choices give different labelled full embeddings, and the restriction to `E_0 union O_0` recovers the starting lower cube. This proves both the extension and (3.3). Notice that this construction never uncrosses one face while ignoring the others. ∎

### Corollary 3.2 -- a smaller-dimensional cube-free ORIGINAL graph

If `G` is `Q_d`-free under the hypotheses of Theorem 3.1, then

\[
 \boxed{H=G[A_+,B_0]\text{ is }Q_{d-j}\text{-free}.}       \tag{3.4}
\]

This is a valid dimension descent. It is not the invalid assertion that `S(G)` is ordinarily `Q_(d-1)`-free.

For example, take `j=d-1`, so `q=1`, `r=m-1`, `D=d`. If a cube-free graph contains `K_(m-1,b_0)` with `b_0>=m`, then every row outside its row side has at most `d-1` neighbours in `B_0`. One extra row with `d` such neighbours would already supply the full cube, not just a homomorphism.

### Corollary 3.3 -- the correct full-square error scale

Put `u=b-b_0`. For the actual original graph `H` in (3.2),

\[
 e-e(H)\le au+rb_0+(D-1)(a-r),                           \tag{3.5}
\]

and

\[
 \boxed{\begin{split}
 s(G)-s(H)
 &\le e\,[au+rb_0+(D-2)(a-r-1)_+]\\
 &\le (u+m+jq)Ne\le (u+3m/2)Ne.
 \end{split}}                                           \tag{3.6}
\]

All square graphs in (3.6) are full-square graphs of the indicated original subgraphs.

#### Proof

Delete the `u` columns outside `B_0`, charging at most `au e` by (2.2). Delete the `r` reservoir rows, charging at most `rb_0 e`. In the remaining original graph, every row outside `A_+` has degree at most `D-1`; deleting these rows costs at most `(D-2)(a-r-1)_+ e` by (2.4). This proves the first line of (3.6). The original-edge losses give (3.5) directly.

Finally, `r+D=m+jq` and `j/2^j<=1/2` for `j>=1`, giving the displayed uniform bound. ∎

If `u<=Lm`, the square loss is at most `(L+3/2)mNe`, exactly the kind of finite-size error permitted in (0.1). This is not a coefficient tending to 8 hidden in a different notation: it is a purely additive, explicitly charged loss for this particular branch.

### A complete positive conclusion when this descent can be iterated

Suppose a `Q_d`-free graph admits successive applications of Theorem 3.1 down to dimension one, with at most `L m_i` columns discarded at stage `i`; here `m_i=2^(d_i-1)`. Since every step reduces dimension,

\[
 \sum_i m_i<2m.
\]

The last original graph is `Q_1`-free and hence edgeless. Equation (3.6), with `N_i<=N` and `e_i<=e`, gives

\[
 \boxed{s(G)\le(2L+3)mNe.}                               \tag{3.7}
\]

Together with (1.3), this is incompatible with the majority-cut density and, for instance,

\[
 N\ge128(2L+4)\,2^d.
\]

Thus an original host admitting such a reservoir chain really does have a constant-linear cube embedding theorem. This is an all-dimensional positive structural criterion, with a complete injection and square-loss proof.

**Remaining gap in this route:** no theorem here guarantees these large reservoirs, or a decomposition with the same square-loss budget, in an arbitrary dense cube-free graph. In particular, critical-density square completion near `1/4` does not itself supply a complete reservoir with `m-q` rows and almost all columns. The existence of cubes in previous diffuse examples is not a proof of a cube-free-qualified reservoir dichotomy. Nor is `H` in (3.4) automatically at the exact original majority-cut density; its edge loss must be retained if using any density-qualified induction.

---

## 4. Full-square peeling and a full-size integral prism ensemble

This second route does not require a reservoir. It works in every original graph at the specified density, so it gives unconditional information even in the diffuse regime. It solves the endpoint-disjointness issue for a spanning tree of auxiliary constraints, but not for their cycle closures.

### Lemma 4.1 -- peeling original edges, not selected auxiliary squares

Fix a real `t>=0`. Repeatedly delete an original edge whose degree in the **current** full-square graph is at most `t`. Let the remaining original graph be `G'`. Then

\[
 \boxed{s(G')\ge s(G)-2te(G),\qquad
        d_{S(G')}(f)>t\quad(f\in E(G')).}                 \tag{4.1}
\]

The first assertion follows by summing (2.1) over at most `e(G)` deletions; the second is the stopping rule. Every intermediate auxiliary graph is rebuilt as `S` of the remaining original graph. If `G` is cube-free, so is `G'`.

In particular, if `s>0`, taking

\[
 t=\frac{s}{4e}                                          \tag{4.2}
\]

leaves `s(G')>=s/2>0`, so the core is nonempty.

### Literal link capacity in the core

For `f=xy`, the auxiliary neighbourhood is exactly the original-edge set of

\[
 L_f=G'[N_{G'}(y)\setminus\{x\},\;N_{G'}(x)\setminus\{y\}].
                                                               \tag{4.3}
\]

If a maximal matching in `L_f` has `q_f` edges, its endpoints cover every edge. There are `q_f` covered vertices in each side, so

\[
 e(L_f)\le q_f\,v(L_f)\le q_f(N-2).
\]

Consequently

\[
 \boxed{\nu(L_f)\ge\frac{d_{S(G')}(f)}{N-2}>\frac{t}{N-2}.}
                                                               \tag{4.4}
\]

This is genuine original-endpoint matching capacity. It is a statement about **one** auxiliary neighbourhood, not arbitrary intersections of many neighbourhoods.

### Lemma 4.2 -- greedy endpoint-disjoint trees, with every prism edge present

Let `T` be a tree on `m>=2` vertices. If a nonempty original graph `F` satisfies

\[
 \delta(S(F))>(m-2)(N-1),                                \tag{4.5}
\]

then it contains an endpoint-disjoint copy of `T` in `S(F)`, and hence an injective `T square K_2` in `F`.

Root and order `T` so that each nonroot vertex has exactly one earlier neighbour, its parent. Choose any original edge for the root. When placing another vertex, its parent's auxiliary neighbours already avoid the parent's two endpoints. There are at most `m-2` other old edge labels. Each such label conflicts with at most

\[
 d_F(a_i)+d_F(b_i)-1\le N-1
\]

edge labels, including itself. Condition (4.5) therefore leaves an auxiliary neighbour avoiding every old original endpoint.

This produces pairwise distinct row labels and pairwise distinct column labels. If `c(x)` is the tree bipartition, map `(x,c(x))` to its row endpoint and `(x,1-c(x))` to its column endpoint. A vertical edge is the selected original edge. For a tree edge, the two horizontal prism edges are the two cross edges in its actual rectangle. This checks every edge of `T square K_2`. ∎

Combining Lemmas 4.1 and 4.2 gives the genuine universal inequality

\[
 \boxed{T\square K_2\nsubseteq G
       \ \Longrightarrow\
       s(G)\le2(m-2)(N-1)e(G).}                          \tag{4.6}
\]

**This hypothesis is prism-freeness, not cube-freeness.** A `Q_d`-free graph can contain the prisms of spanning trees of `Q_(d-1)`. Replacing the hypothesis of (4.6) by cube-freeness would be an invalid step.

### Theorem 4.3 -- explicit critical-density ensemble

Let `h=2m=2^d`, `d>=2`, and suppose

\[
 N\ge512h=1024m,\qquad e\ge N(N-1)/8.                    \tag{4.7}
\]

For every tree `T` on `m` labelled vertices, `G` has at least

\[
 \boxed{(N/32)^h}                                        \tag{4.8}
\]

labelled, injective, bipartition-respecting copies of `T square K_2`.

There is an explicit sequential distribution on these whole injections. Conditioned on any positive-probability history of complete earlier blocks:

* the probability of a specified original edge for the next block is at most `1024/N^2`;
* the probability of a specified original vertex in a specified endpoint coordinate of that next block is at most `1024/N`.

These are block-history conditional statements. They are not assertions after conditioning on future cube-closing constraints.

#### Proof and finite constants

Peel at `t=s/(4e)`. From (1.2),

\[
 t\ge \frac{2e^3}{N^4}-\frac{N-1}{8}
    \ge\frac{(N-1)^3}{256N}-\frac{N-1}{8}
    \ge\frac{N^2}{512}\qquad(N\ge128).                  \tag{4.9}
\]

The final inequality is equivalent to

\[
 N^3-70N^2+70N-2\ge0.
\]

Writing `N=128+x` makes this

\[
 x^3+314x^2+31302x+959230\ge0,
\]

an independent all-size check.

Let `e'=e(G')`. By `s(G')>=s/2` and the simple-graph bound `2s(G')<=e'^2`,

\[
 e'\ge\sqrt{s}\ge e/4\ge N^2/64.                        \tag{4.10}
\]

Here `s/e^2>=1/16` follows from (1.3) for `N>=128`.

At every nonroot tree step, the number of choices after forbidding all previous endpoints is greater than

\[
 t-(m-2)(N-1)
 \ge\frac{N^2}{512}-mN
 \ge\frac{N^2}{1024}.                                   \tag{4.11}
\]

Choose uniformly from the original edges of `G'` for the root, and uniformly from the permitted auxiliary neighbours thereafter. Equations (4.10)--(4.11) give at least

\[
 e'\left(\frac{N^2}{1024}\right)^{m-1}
 \ge\left(\frac N{32}\right)^{2m}
\]

distinct full prism embeddings. A fixed endpoint belongs to at most `N` original edge labels, which proves the conditional marginal bounds. All labels are chosen without repeated original endpoints. ∎

The same core has, for every original edge, an actual link matching of size greater than `N/512>=h`, by (4.4) and (4.9). Thus the route supplies strong one-neighbour capacity and an exponential-size integral family, not merely fractional feasibility.

### What cube-freeness says about this ensemble

Take `T` to be a spanning tree of `Q_k`. Each produced prism has all `h=2m` original vertices and

\[
 3m-2
\]

of the `dm` cube edges. The number of missing source edges is exactly

\[
 \boxed{dm-(3m-2)=(d-3)m+2.}                             \tag{4.12}
\]

Equivalently, the number of untested auxiliary edges is

\[
 L=\frac{km}{2}-(m-1)=\frac{(d-3)m}{2}+1.                \tag{4.13}
\]

If `G` is `Q_d`-free, every one of these endpoint-disjoint tree embeddings has at least one of these auxiliary adjacencies absent. In the actual original graph, that means at least one of the corresponding two cross cells is absent. For the distribution just constructed,

\[
 \sum_{xy\in E(Q_k)\setminus E(T)}
       \Pr\{f(x)\not\sim_{S(G')}f(y)\}\ge1.              \tag{4.14}
\]

This consequence is correct but far too weak: it is compatible with completion probability near `1/4` on each untested pair. Neither the whole-injection count nor the endpoint marginal bounds imply a positive probability of all the remaining adjacencies simultaneously. The missing part is joint compatibility, not a final rounding of a fractional matching.

---

## 5. An actual unconditional paired-colour consequence

This route was also pursued with both colours, rather than assuming that a majority-square restriction remains complete.

### Theorem 5.1 -- uniform linear Ramsey bound for tree prisms

For every tree `T` on `m` vertices,

\[
 \boxed{R(T\square K_2)\le128m.}                         \tag{5.1}
\]

For `m=1`, the target is `K_2`, so this is immediate. Assume `m>=2` and split a complete host of order `N=128m` into two equal parts `A,B`. Its two cross-colour matrices are exactly complementary.

For `p=e(R)/(ab)`, Cauchy--Schwarz in each colour gives

\[
 T_4(R)+T_4(B)\ge[p^4+(1-p)^4](ab)^2\ge\frac{(ab)^2}{8}.
                                                               \tag{5.2}
\]

At a row with red degree `r_x`, the sum of the two degree squares is
`r_x^2+(b-r_x)^2<=b^2`; apply the analogous column inequality. Since `e(R)+e(B)=ab`, (1.1) yields

\[
 \boxed{s_R+s_B\ge\frac{(ab)^2}{16}-\frac{(N-1)ab}{2}.} \tag{5.3}
\]

If neither colour contains the prism, (4.6) applies separately to their actual full-square graphs, giving

\[
 s_R+s_B\le2(m-2)(N-1)ab.                               \tag{5.4}
\]

But `ab=N^2/4` and, at `N=128m`, the left minus right sides after division by `ab` are

\[
 \frac{N^2}{64}-\frac{N-1}{2}-2(m-2)(N-1)
 =\frac{900m-7}{2}>0.
\]

This contradicts (5.3)--(5.4), proving (5.1).

Complementarity was used only in the original complete cut. The proof does **not** assert that the colours stay complementary after separate edge-peeling operations.

For `T` a spanning tree of `Q_(d-1)`, (5.1) gives a monochromatic spanning subgraph of a cube on all `2^d` vertices, with the edge deficit (4.12). Except for `d=2`, it does not give the cube. In dimension three even the two missing original edges cannot simply be declared present. This is a positive all-dimensional conclusion, but not a substitute for the requested theorem.

---

## 6. Critical square energy: an attempted diffuse-case route

The reservoir descent handles a strong concentration branch. The next attempt was to use excess actual rectangle count to increase density, then finish in the low-excess branch. Both the increment and the obstruction in the available finishing estimate can be quantified.

### 6.1 A positive density increment from excess full-square energy

Normalize

\[
 p=\frac e{ab},\qquad \tau=\frac{T_4}{a^2b^2},\qquad W=M-pJ.
\]

Let

\[
 \kappa=\frac1{ab}\max_{X\subseteq A,Y\subseteq B}
              \left|\sum_{X\times Y}W_{xy}\right|,
 \qquad
 \kappa_+=\frac1{ab}\max_{X,Y}\sum_{X\times Y}W_{xy}.
\]

Then

\[
 \boxed{0\le\tau-p^4\le4\kappa\le12\kappa_+.}           \tag{6.1}
\]

To prove the middle bound, telescope the four factors in the rectangle product from `M` to `pJ`. In each term, after fixing the other two source variables, the two endpoints of the changed edge have weights `f(x)g(y)` with `0<=f,g<=1`. Layer-cake decomposition bounds the resulting sum against `W` by `ab*kappa`. There are four terms.

For the last inequality, if the extremizing cut has negative sum `-ab*kappa`, the three other blocks of its two-by-two partition have total sum `ab*kappa`, since the total sum of `W` is zero. One of them has positive sum at least `ab*kappa/3`.

Consequently, if

\[
 \tau>p^4+\eta,\qquad0<\eta<1,
\]

there is an actual subrectangle `X x Y` with

\[
 |X|\ge\frac\eta{12}a,\qquad |Y|\ge\frac\eta{12}b,
 \qquad p(X,Y)>p+\frac\eta{12}.                          \tag{6.2}
\]

The area bound follows because every entry of `W` is at most one; the density increment follows by dividing its positive excess by the rectangle's area, which is at most `ab`.

Iterating (6.2) must stop before `ceil(12/eta)` increments, since density cannot exceed one. Therefore every bipartite graph has a subrectangle with at least a fraction

\[
 c_\eta=\left(\frac\eta{12}\right)^{\lceil12/\eta\rceil}
                                                               \tag{6.3}
\]

of **each** original part, density at least the initial density, and

\[
 \boxed{p^4\le\tau\le p^4+\eta.}                        \tag{6.4}
\]

If the original graph is cube-free, the subrectangle is still cube-free. For any fixed `eta`, a sufficiently large constant initial host ratio retains a constant-linear-sized subrectangle.

This is an existential subrectangle theorem, **not** an upper bound on the total square count of the original graph: squares discarded outside the chosen rectangle have not been charged by an `O(mNe)` budget.

### 6.2 What low excess really gives

Let `r_x=d(x)/b`, `c_y=d(y)/a`, and let

\[
 C_A(x,x')=\frac{|N(x)\cap N(x')|}{b}.
\]

Under (6.4), for `p>0`,

\[
 \begin{split}
 \mathbb E(r_x-p)^2,\;\mathbb E(c_y-p)^2
     &\le\frac{\eta}{2p^2},\\
 \mathbb E_{x,x'}(C_A(x,x')-p^2)^2&\le\eta,
 \end{split}                                            \tag{6.5}
\]

and the analogous column-codegree inequality holds.

For example, put `q_B=E_y c_y^2`. Then

\[
 q_B\ge p^2,\quad q_B^2\le\tau,\quad
 \mathbb E(C_A-p^2)^2=\tau-2p^2q_B+p^4\le\eta.
\]

Also `tau-p^4 >= 2p^2(q_B-p^2)`, proving the degree-variance bound. The other side is symmetric.

These estimates imply the concrete spectral bound

\[
 \|W\|_{\mathrm{op}}\le(6\eta)^{1/4}\sqrt{ab}.           \tag{6.6}
\]

Indeed,

\[
 \frac{(WW^T)_{xx'}}b
   =C_A(x,x')-p^2-p(r_x-p)-p(r_{x'}-p).
\]

Squaring, averaging, and using (6.5) and `(u+v+w)^2<=3(u^2+v^2+w^2)` gives

\[
 \frac{\operatorname{tr}((WW^T)^2)}{a^2b^2}\le6\eta.
\]

This dominates the fourth power of the normalized operator norm.

There is also an **actual full-square** operator consequence. On all original labels `A x B`, set

\[
 K_{(x,y),(x',y')}=M_{xy'}M_{x'y}.
\]

On matrices it acts as `X -> M X^T M`. Writing `M=pJ+W` and putting `theta=(6eta)^(1/4)` gives

\[
 \|K-p^2J_{ab}\|_{\mathrm{op}}
 \le(2p\theta+\theta^2)ab.
\]

Restrict to the actual labels `E(G)`. The entries to be removed to obtain `A_(S(G))` are precisely the pairs sharing an original endpoint, including the diagonal. Their row sums are at most `N-1`. Hence

\[
 \boxed{\|A_{S(G)}-p^2J_e\|_{\mathrm{op}}
       \le(2p\theta+\theta^2)ab+N-1.}                   \tag{6.7}
\]

No arbitrary endpoint-labelled graph has been substituted for this kernel.

### 6.3 The critical normalization remains on the wrong side

If the low-excess rectangle has `p=1/2`, then

\[
 \frac14\le\frac{T_4}{e^2}\le\frac14+4\eta.              \tag{6.8}
\]

On a fixed constant-linear host scale, `e^alpha -> 16` and the degree correction in (1.1) is negligible. Thus (6.8) corresponds to

\[
 2-o(1)\le\frac{s}{e^{2-\alpha}}\le2+32\eta+o(1).       \tag{6.9}
\]

This illustrates the critical coefficient, but gives no strict improvement below it. The extracted density may instead be greater than `1/2`, in which case its floor is higher. Nor does (6.9) concern all the original graph's discarded squares.

Taking `eta=O(1/d)` does not make this a constant-ratio argument: (6.3) then loses a factor `exp(-Theta(d log d))` in each part. A fixed original `N/2^d` cannot absorb that loss.

### 6.4 A direct INJECTIVE counting calculation, and why it does not finish

Here is a finite-population counting inequality that avoids converting homomorphisms by a birthday subtraction.

Let `F` be any fixed labelled bipartite source, with part sizes `u,v` and `ell` edges, and let `a>=u,b>=v`. Then

\[
 \boxed{\left|
 \frac{\operatorname{inj}_{A,B}(F,G)}{(a)_u(b)_v}-p^\ell
 \right|
 \le\ell\,\frac{ab}{(a-u+1)(b-v+1)}\,\kappa.}            \tag{6.10}
\]

To prove it, telescope one source-edge factor at a time. Fix the distinct images of the other `u-1` and `v-1` source vertices. The two unfixed endpoints must avoid their respective used sets; these are separate row and column restrictions. All other incident edge factors therefore split as `f(x)g(y)`, with values in `[0,1]`, and all fully fixed factors contribute a number in `[0,1]`. The cut-norm bound for this term is `ab*kappa`. There are at most `(a)_(u-1)(b)_(v-1)` fixed assignments. Divide by `(a)_u(b)_v` and sum the `ell` terms to obtain (6.10).

For `Q_d`, `u=v=m` and `ell=dm`. Even when `a,b>=2m`, the direct positive criterion from (6.10) requires cut discrepancy on the scale

\[
 \kappa<\frac{p^{dm}}{dm}.                              \tag{6.11}
\]

The stronger condition `kappa<p^(dm)/(4dm)` is sufficient on that size range. At `p=1/2`, this is exponentially small in `d2^d`, rather than a small absolute discrepancy.

In fact, a nontrivial zero-one matrix at `p=1/2` has

\[
 \kappa\ge\frac1{2ab}
\]

just by taking a one-cell rectangle. On `a+b=C2^d`, this is only exponentially small in `d`, and eventually exceeds the right side of (6.11) for every fixed `C`. Thus **this particular direct absolute-error counting bound cannot certify the critical-density cube on the linear host scale**, even after the energy increment.

This is a limitation of the derived counting route, not a refutation of the original theorem or of a cube-free-qualified estimate. A successful diffuse-case argument would have to be relative, capacity-sensitive, or otherwise use considerably more of the cube and full-rectangle structure.

---

## 7. Actual rectangle switches: exact variation and simultaneous constraints

A further attempt was to use the other diagonal of a rectangle to modify matching restrictions of `S(G)` while maintaining cube-freeness of every restriction.

Let `M_0={(a_i,b_i):1<=i<=q}` be an original matching and write

\[
 B_{ij}=1_{a_i b_j\in E(G)}.
\]

Then `B_ii=1`, and the matching restriction has adjacency `B_ij B_ji` for `i!=j`. If `B_ij=B_ji=1`, full rectangle completion permits swapping columns `i,j` in the matching. Call the new matching `M_0'`. Direct calculation gives

\[
 \boxed{e(S(G)[M_0'])-e(S(G)[M_0])
       =-\sum_{k\ne i,j}(B_{ik}-B_{jk})(B_{ki}-B_{kj}).}  \tag{7.1}
\]

The pair `i,j` stays adjacent. For another index `k`, the two new adjacency indicators are `B_ik B_kj` and `B_jk B_ki`, proving the formula.

Thus a matching arrangement maximizing the number of auxiliary edges on its fixed endpoint sets satisfies

\[
 \sum_{k\ne i,j}(B_{ik}-B_{jk})(B_{ki}-B_{kj})\ge0
\]

on every permitted switch. If the original graph is `Q_d`-free, every one of these matching restrictions is ordinarily `Q_(d-1)`-free. These really are coupled constraints on actual full-square restrictions, stronger than merely bounding a generic conflict graph's maximum degree.

They have not yielded the desired global square inequality. In particular, an edge-count-improving switch need not preserve a chosen cube or partial cube.

### Exactly what preservation requires

Suppose auxiliary source positions `x` have pairwise distinct row and column labels `(a_x,b_x)`. Let

\[
 \mathcal R_k=\{(x,x):x\in Q_k\}
             \cup\{(x,y):xy\in E(Q_k)\}
\]

include both orientations of each cube edge. After a column permutation `sigma`, the labels `(a_x,b_(sigma(x)))` form a full endpoint-disjoint auxiliary cube **if and only if**

\[
 \boxed{M_{a_x,b_{\sigma(y)}}=1
                \quad\text{for every }(x,y)\in\mathcal R_k.}       \tag{7.2}
\]

The diagonal pairs check the new original edge labels; the other ordered pairs check both cross edges of every required square. Injectivity is preserved by the permutation.

For a transposition of positions `u,v`, the new column `b_v` at `u` must be adjacent to **all** rows indexed by the closed source neighbourhood of `u`; similarly for `b_u` and `v`. One completed rectangle verifies only the two involved rows, not these other incidences. The same statement applies with the currently required partial source graph in place of `Q_k`.

Moreover, any sequence of pure opposite-diagonal switches preserves the multisets of original row and column endpoints. Starting with repeated endpoints, such switches alone cannot make those multisets injective; an external endpoint must actually be introduced.

Thus neither local switching nor selecting an edge-maximal matching restriction supplies the missing joint cube compatibility. No generic conflict-free Turan additive theorem is invoked here.

---

## 8. How the positive branches do and do not combine

The routes above leave the following rigorous picture for a hypothetical dense `Q_d`-free original graph.

* There is a full-square core retaining at least half of its square count, with every single-edge rectangle link having a large original matching.
* There are integral families of placements of all `h` source labels into distinct original vertices, respecting the connected tree-prism constraints, with the count and block-history marginal bounds in Theorem 4.3.
* Every member of those families is missing at least one of the other source square constraints. Large entropy and one-block capacity have not shown that these omissions can all be removed simultaneously.
* A complete bipartite reservoir of the sizes in Theorem 3.1 would give a genuine smaller-dimensional cube-free original graph, with the explicitly controlled square loss in (3.6). A sufficiently wide reservoir chain is ruled out by (3.7) and the critical-density floor.
* Square-energy increments can reach a large low-excess original subrectangle. They do not force a reservoir there, and the available direct injective counting estimate is far too weak at the resulting diffuse density.

The missing theorem is therefore **not** the assertion that all the used vertices can be rounded to a matching, and it is **not** a missing factor of two in the rectangle count. Those issues are explicitly resolved in their respective positive branches.

What is not proved is a global assertion that cube-freeness plus actual full-square completion forces one of the following useful outcomes:

1. enough reservoir dimension descents/decompositions to charge all remaining square mass within `O(mNe)`; or
2. a family with positive mass on **all** the cube-compatible multi-neighbour constraints, not just on single links and tree-prism placements; or
3. a paired-colour square upper bound contradicting the exact complementary-colour floor.

This is a description of the missing work, not an established dichotomy or an equivalent linear programme being offered as a solution.

In the original target's normalization, a sufficient conclusion would still be

\[
 \frac{T_4(G)}{e^2}
 \le \frac14-\frac\varepsilon8+O(Kh/N)+o(1)              \tag{8.1}
\]

on the majority-cut scale, whereas Cauchy--Schwarz supplies the opposite floor near `1/4`. None of the lemmas above proves (8.1) for arbitrary cube-free original graphs.

The previously exhibited actual full-square graphs with sparse matching restrictions contain cubes. They have not been used as counterexamples to a cube-free-qualified estimate. Likewise, no half-dense matching restriction or constant fraction of conflict-free ordinary auxiliary cube copies has been assumed.

---

## 9. Verification and integrity

The proofs above are universally quantified; the finite checks are independent audits of their counting conventions, algebra, and constructions, not evidence that settles the open Ramsey assertion.

`Submission/check_cube_square_free_critical.py` rebuilds full-square graphs from actual original edges throughout. Its saved output is `Submission/CubeSquareFreeCriticalVerification.txt`. The checks include:

* **4,946 exhaustive small bipartite hosts** and **28,129 individual original-edge deletions**, verifying the factor `2` in (2.1), full-square identities, peeling budgets, and literal link matching capacities.
* **5,566 greedy prism audits**, plus larger complete-host tests up to 32 original source vertices, checking every prism edge and all original endpoint distinctness.
* The paired-colour rectangle floor, the energy-increment bounds, and degree/codegree/Schatten moment inequalities.
* Exact injective cut-counting checks for `C_4` and 256 four-by-four tests for `Q_3`.
* **6,144 permitted actual-rectangle matching switches**, checking (7.1) against independently rebuilt full-square restrictions.
* **28 reservoir dimension-extension constructions**, covering every `1<=j<=d-1` for `2<=d<=8`, with **every edge of the completed original cube** checked. There are also **48 independent lower/full cube-count multiplicity tests** for (3.3), and **128 square-budget tests** for (3.6).
* The all-dimensional constant calculations reduced to the positive polynomial in (4.9), the exact positive gap in Theorem 5.1, and the omitted source-edge count (4.12).

No external admitted Lean theorem was used as a premise, no proof or disproof was fabricated, and no Lean file was edited. The recorded SHA-256 of `Submission/Spec.lean`, checked before and after, is

```text
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```

**Final status:** the reservoir extension/descent and its `O(2^dNe)` square bookkeeping, the critical-density full-square core and tree-prism ensemble, and the paired tree-prism Ramsey bound are proved. The global critical-density cube-free comparison and `R(Q_d)=O(2^d)` remain unproved in this work.
