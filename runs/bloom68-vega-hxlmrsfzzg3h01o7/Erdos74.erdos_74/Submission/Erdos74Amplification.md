# Erdős 74: a graph-independent obstruction to uniform profile compression

## Status and concrete conclusions

This does **not** settle Erdős 74. It proves that one of the proposed ways of settling it cannot work in its stated uniform form, even outside quadrangulations. It also gives a quantitative requirement on any nonuniform replacement for that mechanism.

Write

\[
 t=\tau(G),\qquad
 T_G(n)=\max\{\tau(H):H\subseteq G,\ |V(H)|\le n\}.
\]

All graphs below are finite and simple. The order bound is on an actual subgraph, not a minor or a graph with added edges.

**Main extraction theorem.** For every integer \(r\ge0\), if \(\chi(G)\ge4\), \(\operatorname{og}(G)>2r\), and \(t=\tau(G)\), then there is \(H\subseteq G\) with

\[
 \tau(H)\ge r+1,\qquad |V(H)|\le 2(16t)^{r+1}.                 \tag{1}
\]

There is no embedding, degree, criticality, or bounded cycle-generator hypothesis here. The dependence on **global** \(t\) is essential; the delayed-frustration Hajós examples in `Erdos74LocalParity.md` do not contradict (1).

**Uniform-compression no-go.** Fix \(C>0\) and an integer \(c\ge0\). There is no transformation applicable to all sufficiently large-odd-girth annular inputs from `Erdos74Notes.md` which outputs a graph \(A(G)\) satisfying all three conditions

\[
 \chi(A(G))\ge4,
 \quad \operatorname{og}(A(G))>2c,
 \quad T_{A(G)}(n)\le T_G(\lceil C\log_2(n+1)\rceil)+c
       \quad\hbox{for every }n.                              \tag{2}
\]

Thus the precise suggested all-sizes logarithmic-profile composition with bounded additive overhead is impossible already at chromatic number four. Increasing constraint arity or leaving surfaces does not evade this particular theorem.

**What it does not exclude.** A construction may escape by restricting its input domain to graphs whose total frustration is already enormous relative to odd girth, by allowing its new total frustration to become very large, by proving compression only over a restricted size range, by charging a nonconstant overhead, or by using a different profile relation altogether. These alternatives have not been constructed here with the properties required by Erdős 74.

The proofs and the quantitative restrictions follow.

## 1. Short parity defects localize chromatic number

For an integer \(L\ge3\), let \(a_L(G)\) be the minimum size of an edge set \(S\subseteq E(G)\) such that

\[
 |S\cap E(Q)|\equiv |E(Q)|\pmod2
       \quad\hbox{for every cycle }Q\hbox{ of length at most }L.
                                                               \tag{3}
\]

This is a parity requirement on short **even** cycles as well as on short odd cycles. A minimum bipartizing cut supplies such an \(S\), so \(a_L(G)\le t\).

### Localization lemma

Let \(p_0:V(G)\to\{0,1\}\) be a two-colouring, and let \(F\) be its monochromatic edges, with \(|F|=t\). Suppose \(S\) satisfies (3), has size \(s\), and

\[
 L\ge 8(t+s).
\]

Let \(U\) be the endpoints of the edges of \(S\). Then

\[
 \chi(G)\le\max\{3,\chi(G[U])+1\}.                            \tag{4}
\]

In particular, if \(G[U]\) is bipartite, then \(G\) is three-colourable.

### Proof, including the extension step

Put \(B=G-(F\cup S)\). The colouring \(p_0\) is proper on \(B\). Let \(W\) be the endpoints of \(F\cup S\); thus

\[
 |W|\le2(t+s).
\]

Construct a labelled auxiliary multigraph on \(W\):

* Retain each edge \(uv\in F\cup S\), labelled \(1+1_S(uv)\in\mathbb F_2\).
* For each pair \(u,v\in W\) with \(d_B(u,v)\le4\), choose a shortest such path and add an auxiliary edge labelled by its length modulo two.

Every simple auxiliary cycle, including a two-edge cycle of parallel edges, traces a closed walk in \(G\) of length at most \(4|W|\le L\). Its label sum is zero by (3): decompose the closed walk into simple cycles and doubled edges. The chosen \(B\)-paths contain no edge of \(S\), so their labels are exactly the sums of \(1+1_S\) along the paths.

Consequently the auxiliary labels integrate to a map \(q:W\to\mathbb F_2\). In particular,

\[
 q(u)+q(v)=1+1_S(uv)\quad(uv\in F\cup S),
\]

and \(q(u)+p_0(u)=q(v)+p_0(v)\) whenever \(d_B(u,v)\le4\).

Let

\[
 X=\{w\in W:q(w)\ne p_0(w)\},\quad Y=W\setminus X.
\]

Then \(d_B(X,Y)>4\). We can explicitly interpolate between the flipped bipartition near \(X\) and the original bipartition near \(Y\). If \(d=d_B(v,X)\), colour \(v\) according to this table (the two entries are the colours for \(p_0(v)=0,1\)):

| Distance \(d\) | Colour pair |
|---|---|
| 0 or 1 | \((1,0)\) |
| 2 | \((1,2)\) |
| 3 | \((0,2)\) |
| at least 4, or infinity | \((0,1)\) |

This is a proper three-colouring of \(B\). Along a \(B\)-edge the distance changes by at most one and the \(p_0\)-bit changes, and each relevant pair of table entries has distinct colours. It agrees with \(q\) on every terminal. Also, no terminal has a \(B\)-neighbour coloured 2: terminals in \(X\) have neighbours at distance at most 1, while terminals in \(Y\) have distance at least 5 and neighbours at distance at least 4.

If \(G[U]\) is bipartite, take an independent set \(I\subseteq U\) meeting every edge of \(S\), and recolour \(I\) with colour 2. This creates no bad \(B\)-edge by the preceding observation. Edges of \(F\setminus S\) were already proper under \(q\); every edge of \(S\) is now proper. Independence of \(I\) handles edges with both endpoints recoloured. This gives a proper three-colouring of \(G\).

For (4), take an \(h\)-colouring of \(G[U]\). Leave one of its colour classes unchanged and recolour each of the other \(h-1\) classes with a distinct fresh colour \(2,\ldots,h\). These classes meet every edge of \(S\). The same extension argument works, using at most \(\max(3,h+1)\) colours. If \(S\) is empty, just use the displayed three-colouring. This proves the lemma.

## 2. A short-parity certificate is a small actual subgraph

We recall the elementary sparse-certificate argument, with its size dependence explicit.

If \(a_L(G)\ge R\), construct a search tree with nodes carrying sets \(D\) of fewer than \(R\) edges. Start at \(D=\varnothing\). At a node choose a cycle \(Q_D\) of length at most \(L\) on which \(D\) has the wrong parity. Branch to \(D\cup\{e\}\) for every \(e\in E(Q_D)\setminus D\). Stop at depth \(R\). There are at most \(1+L+\cdots+L^{R-1}\) selected cycles.

Let \(H\) be their union. If a cut on \(H\) had fewer than \(R\) monochromatic edges, follow a branch while keeping \(D\) inside its bad-edge set. The parity failure at \(Q_D\) supplies another bad edge in \(Q_D\setminus D\). The branch therefore reaches \(R\) distinct bad edges, a contradiction. Hence

\[
 \tau(H)\ge R,\quad
 |V(H)|\le L+L^2+\cdots+L^R\le2L^R.                         \tag{5}
\]

This counts only original edges and vertices, and needs no bound on equation occurrences.

## 3. Proof of the main extraction theorem

Take a minimum cut \(F\) of size \(t\), set \(L=16t\), and take a minimum short-parity solution \(S\), of size \(s=a_L(G)\le t\). The localization lemma applies because \(8(t+s)\le16t\).

If \(s\le r\) and \(\operatorname{og}(G)>2r\), its endpoint set \(U\) has at most \(2r\) vertices, so \(G[U]\) is bipartite. The lemma would give \(\chi(G)\le3\). Therefore

\[
 a_{16t}(G)\ge r+1.
\]

Apply (5) with \(R=r+1\) to obtain (1).

### A version incorporating chromatic number as well as odd girth

If \(\chi(G)=k\ge4\) and \(g=\operatorname{og}(G)\), the same argument gives

\[
 a_{16t}(G)\ge R(g,k):=
 \max\left\{\left\lceil\frac g2\right\rceil,
               \left\lfloor\frac{(k-2)^2}{4}\right\rfloor\right\}.
                                                               \tag{6}
\]

Indeed (4) forces \(\chi(G[U])\ge k-1\), in particular at least three, so \(2s\ge g\). Moreover \(S\) is the bad-edge set of the terminal colouring \(q\) on \(G[U]\), hence \(\tau(G[U])\le s\). The elementary universal bound

\[
 \tau(J)\ge\left\lfloor\frac{(\chi(J)-1)^2}{4}\right\rfloor     \tag{7}
\]

then proves the other part of (6).

For completeness, to prove (7), take any cut, let the two induced sides have chromatic numbers \(a,b\), and note that they contain at least \(\binom a2+\binom b2\) edges. Also \(\chi(J)\le a+b\). Minimizing over \(a,b\) with prescribed sum gives (7).

Thus there is always a subgraph with

\[
 \tau(H)\ge R(g,k),\qquad |V(H)|\le2(16t)^{R(g,k)}.             \tag{8}
\]

## 4. Why the proposed uniform logarithmic compression is impossible

The graphs in the supplied notes have

\[
 \chi(G)=4,\quad g=3L,\quad \tau(G)\le24L+2=8g+2,
\]

where \(g\) tends to infinity, and their annular depth can be arbitrary after the odd-girth threshold.

Suppose (2) holds and write \(K=A(G)\). Applying (2) at the full order of \(K\) gives

\[
 \tau(K)\le\tau(G)+c\le8g+2+c.                               \tag{9}
\]

By (1), since \(\operatorname{og}(K)>2c\), there is a subgraph requiring at least \(c+1\) deletions with at most

\[
 N_g=2\,[16(8g+2+c)]^{c+1}
\]

vertices. For fixed \(C,c\), this is polynomial in \(g\), so for all sufficiently large \(g\),

\[
 \lceil C\log_2(N_g+1)\rceil<g.
\]

Every subgraph of the input \(G\) on fewer than \(g\) vertices is bipartite. The assumed profile inequality therefore gives \(T_K(N_g)\le c\), contradicting the extracted witness. This proves the no-go theorem.

Notice the strength of the conclusion: the output need not preserve the input's large odd girth. Merely requiring output odd girth greater than the fixed number \(2c\) already suffices. For \(c=0\) or \(c=1\), this condition is automatic for a nonbipartite simple graph: the suggested **+1 version cannot preserve four-chromaticity at all** on these inputs. An arbitrary prescribed divergent function may vanish throughout the fixed initial interval up to \(2c\), so allowing short odd cycles is not an adequate escape for Erdős 74.

There is also an output chromatic bound without an odd-girth assumption. For an input of odd girth \(g\) and total frustration \(t\), put \(N=2[16(t+c)]^{c+1}\). Whenever \(\lceil C\log_2(N+1)\rceil<g\), (2) implies \(a_{16\tau(K)}(K)\le c\), by (5). Applying (4) and (7) gives

\[
 \chi(K)\le\max\{3,\ 2+\lfloor\sqrt{4c+1}\rfloor\}.           \tag{9a}
\]

In particular a fixed additive overhead cannot uniformly preserve unbounded chromatic number on inputs of large odd girth and polynomial total frustration. Classical iterated generalized Mycielski graphs supply such inputs for each fixed chromatic number: \(M_r^{k-2}(K_2)\) has chromatic number \(k\), odd girth \(2r+1\), and order polynomial in \(r\), using the standard chromatic theorem for iterated generalized Mycielski graphs. This last example is a standard external fact, recorded in Anton Dochtermann and Carsten Schultz, *Topology of Hom complexes and test graphs for bounding chromatic number*, arXiv:0907.5079, in the discussion of generalized Mycielski graphs (verified in the local corpus source `/corpus/src/0907.5079/graphtest.tex`). The four-chromatic no-go proof above only needs the supplied annular family.

### A quantitative overhead requirement

More generally, let the input have odd girth \(g\) and total frustration \(t\), and let an output satisfy the all-sizes profile bound in (2). If it is non-three-colourable and has odd girth greater than \(2c\), then necessarily

\[
 g\le\left\lceil C\log_2\bigl(2[16(t+c)]^{c+1}+1\bigr)\right\rceil.
                                                               \tag{10}
\]

In particular, for the annular inputs \(t\le8g+2\), an output of odd girth at least \(g\) requires either \(c\ge g/2\), or

\[
 c+1=\Omega_C(g/\log g).
\]

Thus, when the output preserves odd girth, the additive cost cannot grow more slowly than order \(g/\log g\) for fixed \(C\); in particular it cannot be a fixed constant.

### Restricted-range compression: the precise escape condition

Suppose instead that a proposed output \(K\) only satisfies

\[
 T_K(n)\le T_G(\lceil C\log_2(n+1)\rceil)+c\quad(n\le M),
 \qquad \tau(K)\le B,
\]

and \(\chi(K)\ge4\), \(\operatorname{og}(K)>2c\). Put

\[
 N=2(16B)^{c+1}.
\]

If \(N\le M\), it is necessary that

\[
 \lceil C\log_2(N+1)\rceil\ge \operatorname{og}(G).             \tag{11}
\]

Otherwise (1) supplies a forbidden witness inside the advertised compression range. For fixed \(C,c\), (11) requires \(B\) to be exponential in the input odd girth, up to constants in the exponent. The other escape is to stop the compression range before \(N\).

This leaves open a much more expensive, nonuniform amplifier. It does not leave open the bounded-overhead all-sizes formula (2).

## 5. A necessary total-frustration budget for any target function

Let \(f\) be a nondecreasing divergent integer-valued function, and suppose \(T_G(n)\le f(n)\), \(\chi(G)=k\ge4\), and \(g=\operatorname{og}(G)\). Set \(R=R(g,k)\) as in (6), and write

\[
 N_f(R)=\min\{n:f(n)\ge R\}.
\]

Then (8) gives the necessary condition

\[
 N_f(R)\le 2(16\tau(G))^R,
 \qquad
 \tau(G)\ge\frac1{16}\left(\frac{N_f(R)}2\right)^{1/R}.         \tag{12}
\]

For example, if \(f(n)=\lfloor\log_2\log_2(n+4)\rfloor\), then

\[
 \tau(G)\ge\frac1{16}
       \left(\frac{2^{2^R}-4}{2}\right)^{1/R}.                 \tag{13}
\]

Already at \(k=4\), \(R=(g+1)/2\). So even this particular sublogarithmic target requires a doubly exponential global frustration budget in odd girth (with a division by \(R\) in the outer exponent). Increasing a depth parameter while keeping the old \(O(g)\) global budget cannot achieve it, irrespective of the geometric mechanism.

Some further consequences:

* If \(\tau(G)\le A g^d\), (8) gives an actual subgraph with \(\tau(H)\ge c_{A,d}\log |V(H)|/\log\log |V(H)|\), with regularized logarithms for small orders. This conclusion now applies to **arbitrary graphs** with that total-budget condition, not only graphs whose cycle space has short generators.
* If \(\tau(G)\le\exp(A g^d)\), the same calculation gives a witness with \(\tau(H)\ge c_{A,d}(\log |V(H)|)^{1/(d+1)}\).

### Diagonal exclusion of any fixed budget scheme

Let \(B(g,k)\) be any prescribed finite bound, however fast-growing. Consider a family of graphs with \(\chi(G)=k\ge4\), odd girth \(g\), and \(\tau(G)\le B(g,k)\), possibly with an arbitrarily large additional depth or padding parameter. There exists a nondecreasing divergent function \(f\) for which **no member of this family** satisfies \(T_G\le f\).

To see this, enlarge \(B(g,k)\), if necessary, so it is at least \(g+k\), and put

\[
 R_{g,k}=R(g,k),\quad N_{g,k}=2[16B(g,k)]^{R_{g,k}},
 \quad f(n)=\min\{R_{g,k}-1:N_{g,k}\ge n\},                    \tag{14}
\]

where \(g\ge3\) is odd and \(k\ge4\). The defining set is nonempty. The function is nondecreasing and diverges: for every fixed bound on \(R_{g,k}\) there are only finitely many pairs \((g,k)\), and all their \(N_{g,k}\) are finite. But (8) supplies a witness with frustration \(R_{g,k}\) on at most \(N_{g,k}\) vertices, whereas \(f(N_{g,k})\le R_{g,k}-1\).

Thus even a wildly growing predetermined budget \(B(g,k)\), independent of all remaining free parameters, cannot handle **every** divergent target. A successful universal scheme has to have further genuinely unbounded frustration parameters, not only unbounded size parameters.

## 6. Bipartite star gadgets cannot hide their cut cost, even at unbounded arity

Here is a separate obstruction aimed at context-independent recursive gadgets.

Fix a palette size \(q\ge3\). Let \(D\) be a bipartite graph with a set of distinct terminals \(P\), where \(d=|P|\ge q\). Suppose every proper \(q\)-colouring of \(D\) omits at least one colour on \(P\). This property is necessary for a bipartite gadget replacing a star centre while forbidding exactly the terminal assignments that use all \(q\) colours.

**Terminal lemma.** All terminals are on the same side of a bipartition, and every pair of distinct terminals has a common neighbour in \(D\).

**Proof.** If terminals lie on both sides, distribute the \(q\) colours between the two sides in disjoint nonempty palettes, using all colours on the terminals. This is possible since there are at least \(q\) terminals. Colour the remaining vertices with one of their side's palette colours. This is a proper colouring with a rainbow terminal set, a contradiction.

Now let all terminals lie in side \(A\). If terminals \(a,b\) have no common neighbour, give \(a\) colour 1, \(b\) colour 2, and use all colours \(3,\ldots,q\) on the remaining terminals. Colour other \(A\)-vertices with colour 3. Colour neighbours of \(a\) with 2 and other vertices in side \(B\) with 1. The absence of a common neighbour makes this proper at \(b\), and all other edges are also proper. Again the terminal set is rainbow. Contradiction.

For every terminal pair choose one common neighbour, and retain just the corresponding two-edge paths. This gives a subgraph \(D_0\) with at most

\[
 d+\binom d2
\]

vertices. For every two-colouring of \(D_0\), if the terminals have colour-class sizes \(a,b\), at least \(\min(a,b)\) edges of \(D_0\) are monochromatic. Indeed let \(Z\) be the terminals incident with a monochromatic edge. Two differently coloured terminals outside \(Z\) cannot share one of the selected two-edge paths. Thus all terminals outside \(Z\) have the same colour, so \(|Z|\ge\min(a,b)\); each bad edge has exactly one terminal endpoint.

But \(\min(a,b)\) is exactly the minimum bad-edge cost of the original star for those terminal colours. Therefore its cut cost has survived in a small actual subgraph, independently of the internal size or depth of \(D\).

### Hereditary consequence

Suppose an independent set of vertices of a base graph \(J\), each of degree at least \(q\), is replaced by internally disjoint bipartite gadgets of the preceding type, with the original neighbours retained as terminals. Call the result \(J'\). Then, for every \(n\ge2\),

\[
 T_{J'}(n^3)\ge T_J(n).                                      \tag{15}
\]

Given an \(n\)-vertex subgraph \(H\subseteq J\), retain its unreplaced vertices. At a replaced vertex use one chosen two-edge path for each pair of its neighbours appearing in \(H\). This uses at most \(n+\sum_v\binom{d_H(v)}2\le n^3\) vertices. Every cut of the resulting subgraph extends, by choosing the old star centres optimally, to a cut of \(H\) with no more bad edges. Vertices of degree zero or one in \(H\) cost nothing. This proves (15).

This addresses **unbounded terminal arity**, not only bounded fan-in. A recursive bipartite gadget that continues to enforce the same star relation on the same terminals still has this short witness at the end, whatever its depth. The result does not apply to a context-dependent constraint that is only enforced in conjunction with the rest of a graph, or to gadgets whose own nonbipartiteness contributes an additional budget.

Two-terminal bipartite edge gadgets are even more restrictive: if their two terminals are nonadjacent, every precolouring of them extends to a three-colouring. Thus a context-independent bipartite gadget enforcing inequality of two terminal colours has to retain the terminal edge itself. One cannot replace an edge by an arbitrarily long bipartite equality/inequality sender for three-colouring.

## 7. What remains for Erdős 74

The following finite-block formulation is genuinely sufficient and makes the two missing requirements precise:

> For every nondecreasing divergent integer function \(h\) and every \(k\), construct a finite \(G\) with \(\chi(G)\ge k\) and \(T_G(n)\le h(n)\) for every \(n\).

To obtain the infinite graph, for a target \(f\) first pass to its nondecreasing tail-minimum minorant. Apply the finite statement with \(h_j(n)=\lfloor2^{-j}f(n)\rfloor\), obtaining blocks with chromatic numbers tending to infinity, and take their disjoint union. A finite subgraph decomposes into pieces of orders \(n_j\), and

\[
 \sum_j\tau(H_j)\le\sum_j2^{-j}f(n_j)\le f\left(\sum_jn_j\right).
\]

Conversely an infinite-chromatic graph supplies finite blocks of every chromatic number by compactness. Achieving only \(\chi=4\), even for every divergent function, is not by itself this finite-block theorem.

No construction proving that finite-block statement, and no universal counterexample function for unrestricted graphs, is established here. What is established is:

1. the exact bounded-overhead logarithmic-profile amplifier suggested in the question is impossible;
2. a fixed total-frustration budget depending only on odd girth and chromatic number cannot handle all divergent functions by increasing annular depth or any other size-only parameter;
3. context-independent bipartite star replacements cannot evade this by using unbounded constraint arity;
4. any remaining positive approach must both pay the quantitative nonuniform budget in (12) and control its hereditary profile, rather than only its final order.

These are mathematical proofs, not formal Lean proofs. No claim of novelty or of an up-to-date resolution of the literature problem is made.

## Verification performed

The full arguments above are mathematical proofs. The script `Submission/check_Erdos74Amplification.py` performs independent finite consistency checks of their delicate explicit steps; its output is saved in `Submission/Erdos74AmplificationChecks.txt`.

The checks passed:

* all 38 relevant bit/adjacent-layer configurations in the interpolation table;
* six long-odd-cycle extensions with an empty short-parity support that is not a full cut support;
* three long Hajós-cycle examples with nonempty short-parity support, again not a full cut support;
* all 16,384 five-vertex graph/cut cases, including nonbipartite support graphs;
* 500 arbitrary-support random cases, verifying the construction on all 307 cases with balanced auxiliary labels;
* all 6,080 cuts of 54 pair-witness star skeletons, including shared internal witnesses;
* 200 explicit rainbow-extension certificates for palettes of sizes 3 through 6.

These computations do not substitute for the proofs and do not test or establish Erdős 74. They verify the phase interpolation, terminal recolouring, and star cut-count assertions used in the proofs. Reproduce with `python3 Submission/check_Erdos74Amplification.py` from the project directory (requires NetworkX).

