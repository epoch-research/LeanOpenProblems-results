# Exact short-parity minima do not admit quantitative cut-gluing

## Status

This does **not** prove or disprove Erdős 74. It rules out a specific proposed intermediate step: obtaining one global cut whose defect count on every short-cycle core is controlled by the minimum short-parity support, even after an arbitrary prescribed change of scale. Section 6 strengthens the obstruction to **every finite ensemble of global cuts**, including ensembles chosen after the graph is known.

The counterexample has chromatic number exactly three. Consequently it is **not** a counterexample to a finite-chromatic-bound conjecture under a sufficiently slow bound on `a_L`, and it does not provide the requested infinite-chromatic construction. The result concerns the failure of quantitative compatibility of minimum supports, not the existence of cuts as such.

No global-frustration localization or no-delay lemma is used.

## 1. The quantitative gluing assertion that fails

For a simple graph `G`, let

\[
 E_{\le L}(G)=\bigcup\{E(C): C\text{ is a cycle of length at most }L\}.
\]

For a two-colouring `p:V(G) -> F_2`, write

\[
 F_p=\{uv\in E(G):p(u)=p(v)\},\qquad
 b_p(L)=|F_p\cap E_{\le L}(G)|.
\]

Recall that `a_L(G)` minimizes the size of a finite edge set `S` satisfying

\[
 |S\cap E(C)|\equiv |C|\pmod 2
 \quad\text{for every cycle }C\text{ of length at most }L.
\]

A tempting compactness/gluing step is to seek one `p` for which `b_p(L)` is at most a constant times `a_{phi(L)}(G)` at every scale. The following disproves that assertion, with arbitrarily slow profiles.

### Theorem

Let

* `h:{3,4,...}->N` be nondecreasing and divergent;
* `phi:{3,4,...}->{3,4,...}` satisfy `phi(L)>=L`;
* `B:{3,4,...}->N` be any finite-valued function.

There is a countable connected simple graph `G` such that:

1. `chi(G)=3`;
2. `a_L(G)<=h(L)` for every `L>=3`, and `a_L(G)->infinity`;
3. every `E_{<=L}(G)` is finite;
4. for every two-colouring `p`,

   \[
   \sup_{L\ge3}\frac{b_p(L)}{\max\{1,a_{\phi(L)}(G)\}}=\infty;
   \]

5. in fact, for every `p`, `b_p(L)>B(L)` at infinitely many scales;
6. along a sequence `L_j`, **every** minimum support has alternating parity on one fixed two-edge path.

Thus this failure persists when `h(L)=o(L)`, when `h` diverges arbitrarily slowly, and after any prescribed scale inflation `phi`. Since `B` is arbitrary, one may in particular take `B(L)=C h(phi(L))` for any fixed integer `C`.

In this example the short cycles already span the full cycle space of each finite short-cycle core. There is no local integration defect inside those cores. The obstruction is to retaining small defect counts while making their minimizing cuts compatible.

## 2. Exact parity calculation for a multi-theta graph

Take two vertices `u,v` and internally vertex-disjoint `u-v` paths `P_i` of lengths `ell_i>=2`. There are no other edges. Assume `P_0` is the unique shortest path, with `ell_0=2`, and only finitely many paths have length below any fixed bound.

Every simple cycle is exactly `P_i union P_j`, for distinct `i,j`. For a finite support `S`, put

\[
 y_i=|S\cap E(P_i)|\pmod2,\qquad
 \epsilon_i=\ell_i\pmod2.
\]

The complete short-cycle parity system is

\[
 y_i+y_j=\epsilon_i+\epsilon_j
 \quad\text{whenever }\ell_i+\ell_j\le L.                 \tag{1}
\]

This includes the even-cycle equations, whose right-hand side is zero.

Let

\[
 A_L=\{i:\ell_i+2\le L\},\quad
 e_L=|\{i\in A_L:\epsilon_i=0\}|,\quad
 o_L=|\{i\in A_L:\epsilon_i=1\}|.
\]

If any short cycle exists, every index appearing in a short cycle lies in `A_L`, and every index in `A_L` is connected to index `0` by a check in (1). Indeed, `P_0 union P_i` has length `2+ell_i<=L`. Therefore the quantities

\[
 z_i=y_i+\epsilon_i
\]

have one common value on `A_L`. Indices outside `A_L` appear in no equation.

A path with `y_i=1` costs at least one support edge, and one edge on that path realizes this parity. Hence

\[
 \boxed{a_L(G)=\min(e_L,o_L).}                             \tag{2}
\]

The formula also covers the case of no short cycles: `A_L` is empty or consists just of index `0`, and the minimum is zero.

If `e_L != o_L` and both are positive, the common value of `z_i` is forced in every minimum support: it is the parity of the majority of active paths. Such a support has exactly one edge on each minority-parity path and no other edges. In particular its parity on `P_0` is the majority parity.

The cycles `P_0 union P_i`, `i in A_L-{0}`, are a cycle basis of the finite short-cycle core, and all have length at most `L`. This proves the assertion about integration on those cores.

## 3. Construction with arbitrarily slow minima and forced oscillation

Begin with `P_0`, of length two. Set `N_0=1`, the number of paths so far, and set `L_0=4`.

At stage `j>=1`, set `epsilon_j=j mod 2`. Choose an integer `L_j` satisfying

\[
 L_j>\phi(L_{j-1}),\qquad L_j\ge5,\qquad
 L_j-2\equiv\epsilon_j\pmod2,\qquad h(L_j)\ge N_{j-1}.
                                                               \tag{3}
\]

This is possible because `h` is nondecreasing and divergent. Put `n_j=L_j-2` and choose an integer

\[
 M_j>\max\{jN_{j-1},B(L_j)\}.                             \tag{4}
\]

Add `M_j` internally disjoint `u-v` paths, all of length `n_j`, sharing no internal vertex with any earlier path. Set `N_j=N_{j-1}+M_j`.

The graph is simple since every path has length at least two and their internal vertices are distinct. The path lengths strictly increase, so each short-cycle core is finite.

The new paths become active exactly at `L_j`. On the entire interval

\[
 L_j\le L<L_{j+1},
\]

the active paths are precisely `P_0` and the first `j` batches. Since `M_j>N_{j-1}`, the new batch determines their strict majority parity. Formula (2) therefore gives

\[
 a_L(G)=r_j,
 \qquad 1\le r_j\le N_{j-1}\le h(L_j)\le h(L).            \tag{5}
\]

Before `L_1` there is no odd cycle, so `a_L=0`. Both parity classes contain an unbounded number of paths as `j` grows, and consequently `r_j` tends to infinity. This proves the desired slow, divergent bound.

Moreover `L_j<=phi(L_j)<L_{j+1}`, so

\[
 a_{\phi(L_j)}(G)=a_{L_j}(G)=r_j\le N_{j-1}.              \tag{6}
\]

Every minimum support at `L_j` has

\[
 |S\cap E(P_0)|\equiv\epsilon_j\pmod2.                    \tag{7}
\]

Thus the minimum-support parity on a fixed finite path is forced to alternate indefinitely. This is not merely a choice between inconvenient minimizers.

## 4. Why every coherent cut loses arbitrarily badly

Fix any two-colouring `p` of the whole graph and put

\[
 d=p(u)+p(v)\in\mathbb F_2.
\]

On every path `P_i`, cancellation at internal vertices gives

\[
 |F_p\cap E(P_i)|\equiv \ell_i+d\pmod2.                  \tag{8}
\]

For every stage with `epsilon_j != d`, each of its `M_j` paths therefore has at least one monochromatic edge. Each such path lies in the short-cycle core at `L_j`, because its union with `P_0` is a cycle of length exactly `L_j`. Distinct paths have disjoint edge sets. Consequently

\[
 b_p(L_j)\ge M_j
   >\max\{B(L_j),jN_{j-1}\}
   \ge\max\{B(L_j),j a_{\phi(L_j)}(G)\}.                 \tag{9}
\]

There are infinitely many such stages for either value of `d`. Equations (6) and (9) prove the theorem's quantitative incompatibility assertions.

Equation (8) on `P_0` also shows directly why no single global cut can restrict to minimum supports at all the scales in (7): its parity on that path is the fixed bit `d`.

Finally, `G` is three-colourable. Give `u` and `v` colour zero. Every path of length at least two admits a proper three-colouring with both endpoints zero, and the interiors of the paths are disjoint. An odd-length batch together with `P_0` gives an odd cycle, so `chi(G)=3` exactly.

## 5. The even checks really matter

For a small finite example use paths of lengths

    2, 3, 3, 6, 6, 6, 6.

At `L=5`, the two five-cycle equations are solved optimally by one edge of the length-two path, and the minimum is one.

At `L=8`, the four newly imposed **even** cycles, each a length-six path together with the length-two path, force all those five path parities to agree. The minimum becomes two: put one support edge on each length-three path. Every minimum now has zero support parity on the length-two path.

There is no new short odd cycle involving a length-six path at `L=8`: the first such odd cycles have length nine. If only the odd-cycle equations were imposed, the minimum at `L=8` would still be one. Thus treating a parity support as merely a short-odd-cycle hitting set would miss the transition used here.

## 6. Strengthening: no finite ensemble of cuts suffices

For a single multi-theta graph, two global cuts with opposite terminal parities can collectively attain all the minima: at each scale select the better cut. Thus Section 1 alone does not exclude that escape from single-cut gluing. The following strengthening does.

### Finite-ensemble theorem

For the same arbitrary `h`, `phi`, and `B`, there is a countable connected simple graph `G` with `chi(G)=3`, finite short-cycle cores, and divergent `a_L(G)<=h(L)`, such that for **every finite nonempty family** `P` of global two-colourings,

\[
 \sup_{L\ge3}
 \frac{\min_{p\in P} b_p(L)}{\max\{1,a_{\phi(L)}(G)\}}
 =\infty.                                                \tag{10}
\]

Also `min_{p in P} b_p(L)>B(L)` at infinitely many scales. The family may be chosen after the graph is known; no finite family works.

### Proof

Use countably many multi-theta lobes, with terminal pairs `u,v_i`, sharing only `u`. Each lobe has its own length-two root path. Simple cycles stay inside individual lobes, so `a_L` is the sum of their separate minima (2). Future lobes with only their root path active contribute zero.

Schedule stages by listing, first, all bit vectors of length one, then all bit vectors of length two, then all bit vectors of length three, and so on. At a stage `j`, let the scheduled vector be `epsilon in {0,1}^d`; the first `d` lobes will be active. Introduce a new root path if this is the first stage of a new dimension. Let `P_j` denote the total number of paths introduced so far, including these roots but before the new batches. This is a positive finite integer.

Set `L_0=4`. Choose `L_j` so that

\[
 L_j\ge6,\qquad L_j-1>\phi(L_{j-1}),\qquad
 h(L_j-1)\ge P_j,                                        \tag{11}
\]

and choose

\[
 M_j>\max\{jP_j,B(L_j)\}.                                \tag{12}
\]

In every lobe `i<=d`, add `M_j` paths whose common length is either `L_j-2` or `L_j-3`, choosing the one with parity `epsilon_i`. Thus these paths become active at `L_j` or `L_j-1`. They are longer than all previously introduced non-root paths.

During either activation event, each lobe's minimum remains at most its number of old paths: if a new batch is active, use all old opposite-parity paths as the minority support; if not, its old minimum already has this bound. Consequently

\[
 a_L(G)\le P_j\le h(L_j-1)\le h(L)
 \quad\text{for }L_j-1\le L<L_{j+1}-1.                  \tag{13}
\]

Before the first activation the minimum is zero. At `L_j`, every active lobe has strict majority parity `epsilon_i`, because `M_j>P_j`. Moreover no subsequent batch is active by `phi(L_j)`, so

\[
 a_{\phi(L_j)}(G)=a_{L_j}(G)\le P_j.                     \tag{14}
\]

For a global cut `p`, its terminal vector on these lobes is

\[
 d(p)=(p(u)+p(v_1),\ldots,p(u)+p(v_d)).
\]

If `d(p)!=epsilon`, equation (8) forces at least `M_j` bad edges in some batch, all in `E_{<=L_j}(G)`. Hence

\[
 b_p(L_j)\ge M_j>
 \max\{B(L_j),j\max(1,a_{\phi(L_j)}(G))\}.               \tag{15}
\]

Now fix any family of `K` cuts. In every round of dimension `d` with `2^d>K`, some scheduled vector differs from all `K` restricted terminal vectors. At its stage, (15) holds for every cut in the family. Such rounds occur infinitely often, and their stage indices tend to infinity. This proves (10) and the `B` assertion.

The graph is three-colourable by giving all terminals colour zero and colouring path interiors separately. It contains odd cycles, so its chromatic number is exactly three. The first lobe receives infinitely many batches of each parity; its minimum alone tends to infinity. Every short-cycle core is finite, since only finitely many stages have become active. This completes the proof.

In particular, choosing `B(L)=L(1+h(phi(L)))` gives the cleaner consequence

\[
 \limsup_{L\to\infty}
 \frac{\min_{p\in P} b_p(L)}{1+h(\phi(L))}=\infty
 \quad\text{for every finite nonempty family }P.          \tag{16}
\]

Thus even the prescribed envelope, rather than the possibly much smaller actual minima, cannot be retained by a finite ensemble.

This strengthening still does **not** contradict bounded chromatic number. A proper colouring can yield several cuts which collectively separate every edge without any one of those cuts having a small defect count on the entire short-cycle core. These are different requirements.

## 7. Consequences and the remaining problem

The construction disproves, even for connected three-colourable graphs:

* existence of a coherent family of **minimum** short-core cuts;
* existence of one global cut with a constant-factor short-core defect approximation;
* the same approximation after any prescribed scale inflation;
* the same assertion with any prescribed finite-valued defect envelope in place of the minima;
* all these quantitative approximation claims using any finite ensemble of global cuts, even if the ensemble is chosen after the graph.

It does **not** disprove compatibility statements that give up defect-count control and instead seek a bounded-colour structure. Indeed these examples are themselves three-colourable. Compactness can produce full two-colourings, but cannot retain the separate quantitative minima in these examples.

Accordingly, a proof from `a_L<=h(L)` to bounded chromatic number would have to use something beyond this quantitative globalization of minimum supports. Conversely, obtaining infinite chromatic number still requires constructing genuinely high-chromatic finite blocks with the entire profile bound. Neither of those remaining steps is established here.

## Verification

The arguments above prove the results for arbitrary functions `h`, `phi`, and `B`. The companion script `check_Erdos74CompatibleCuts.py` independently checks finite instances of the exact minimum formula, forced majority phases, the even-check transition, failure of simultaneous minimum cuts, and the finite-ensemble scheduling and budget inequalities. It uses only the Python standard library.

The saved output in `Erdos74CompatibleCutsChecks.txt` records successful checks of:

* 3,782 exhaustive path-parity minima and 1,937 forced-majority phases;
* 20 enumerations using actual original-edge supports, rather than compressed path variables;
* the jump caused specifically by even-cycle checks;
* forced root-parity oscillation across three scales;
* all 32,768 two-colourings, fixing one terminal, of a finite two-scale example;
* every activation budget in a 14-stage finite-ensemble construction, and all 254 proper nonempty families of the eight possible three-lobe terminal phases.

These consistency checks do not prove any infinite-chromatic existence or obstruction theorem.
