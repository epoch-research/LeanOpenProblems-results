# Endpoint conflicts in the square lift: exact relaxation and dense obstructions

## Outcome

**No proof of `R(Q_d) <= C 2^d` is obtained.** Nor is the density-qualified, full-square-graph comparison needed for that proof refuted. The progress is a set of rigorous distinctions and estimates directly concerning that comparison:

1. The **generic two-endpoint-label extremal problem has an exact answer**: on labels `[a] x [b]`, `a <= b`, its extremal number is `b(b-1) ex(a,H)`. This is proved below, not imported from an extremal library.
2. For **actual square graphs**, uniform random matching sampling gives a valid endpoint-disjoint comparison, including its finite variance error. Its leading loss tends to **4**, not less than 2, on the proposed scale.
3. There are **dense, cube-free original graphs** invalidating a small-loss comparison with an `o(2^d) N e(G)` error. An error of order `2^d N e(G)` really is necessary for a comparison over all positive-density original graphs.
4. Even allowing that natural error, the desired leading coefficient is **impossible for generic endpoint-labelled auxiliary graphs**. An explicit probabilistic construction gives the critical obstruction `L A >= 2`, hence `L >= 2` when `A -> L/2`.
5. In a complete balanced original graph, the fraction of ordinary auxiliary cube copies that are endpoint-disjoint is exponentially small at `N=C2^d`. Thus a constant-fraction copy-supersaturation transfer is false even in the most regular dense example.
6. A precise remaining full-square-graph estimate, with a controlled error and a leading coefficient below 2, is stated at the end, and its sufficiency for the Ramsey conclusion is checked with explicit constants.

Items 1 and 4 concern a **relaxation** of the actual square graph. They must not be represented as counterexamples to the density-qualified estimate for `S(G)` itself. In the relaxation's counterexample the original complete bipartite graph already contains the larger cube.

No Lean files were edited, and no unrelated result was formalized. `Submission/Spec.lean` retains SHA-256 `9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b`.

## 1. Notation and the exact hypothesis that must be retained

Let `G=(A,B)` be bipartite, `a=|A| <= b=|B|`, `N=a+b`, and `e=e(G)`. Its square graph has vertex set `E(G)` and

```
xy ~ x'y'  iff  x != x', y != y', xy', x'y are both in E(G).
```

Write `s=e(S(G))`. Labels conflict if they share either endpoint. The conflict degree of a label `xy` is `d_G(x)+d_G(y)-2 <= N-2`.

Put

```
k=d-1,   m=2^k=2^(d-1),   alpha=2/(k+2)=2/(d+1).
```

An endpoint-disjoint copy of `Q_k` in `S(G)` is equivalent to a copy of `Q_d` in `G`: at each vertex of `Q_k`, orient the corresponding original edge according to that vertex's parity. The vertical edges and the two cross edges supplied by each auxiliary adjacency are exactly the required cube edges. Conversely, the edges in one coordinate direction of a `Q_d` supply these labels.

The previously verified square count is

\[
s=2C_4(G)\geq \frac{e^4}{2a^2b^2}-\frac{(N-1)e}{2}
          \geq \frac{8e^4}{N^4}-\frac{(N-1)e}{2}.                 \tag{1}
\]

Besides disjointness of the endpoints of adjacent labels, an actual square graph has the following **full square-completion property**:

> If all four cells `(x,y),(x,y'),(x',y),(x',y')` are vertices, both opposite-cell pairs are auxiliary edges.

Retaining only selected squares can destroy this property. Even retaining both diagonals of every selected square is strictly weaker than full square completion.

## 2. Exact solution of the generic endpoint-label relaxation

Let `H` be any finite simple graph with at least one edge. Let `F(a,b;H)` be the largest edge count of a graph `J` on **all** labels `[a] x [b]` such that

* an edge of `J` joins labels with distinct first and distinct second coordinates;
* `J` has no copy of `H` whose labels have pairwise distinct first coordinates and pairwise distinct second coordinates.

For `a <= b`,

\[
\boxed{F(a,b;H)=b(b-1)\operatorname{ex}(a,H).}                  \tag{2}
\]

Here `ex(a,H)` is ordinary complete-host subgraph extremality, not cube-host extremality.

### Upper bound

Choose a uniformly random injection `pi:[a] -> [b]`. Its graph

```
M_pi = {(i,pi(i)): i in [a]}
```

is an endpoint-disjoint set of `a` labels. Consequently `J[M_pi]` is ordinarily `H`-free and has at most `ex(a,H)` edges.

Every edge of `J` lies in `M_pi` with probability exactly `1/[b(b-1)]`. Taking expectations proves

\[
e(J)/[b(b-1)]\leq\operatorname{ex}(a,H).
\]

The case `b=1` is trivial.

### Matching lower bound

Take an extremal `H`-free graph `T` on `[a]`, and define

\[
(i,j)\sim_J(i',j')\quad\Longleftrightarrow\quad
 ii'\in E(T)\ \text{and}\ j\ne j'.                            \tag{3}
\]

An endpoint-disjoint `H` in `J` would project injectively in its first coordinate to an `H` in `T`. Thus none exists. Each edge of `T` produces exactly `b(b-1)` edges of `J`, proving equality in (2).

This construction also preserves the paired-diagonal symmetry of selected squares. It need not preserve **full** square completion: if `ii'` is a nonedge of `T`, four corresponding labels are present but both square diagonals are absent.

### Why this matters

For `a=b=t`, the auxiliary vertex count is `n=t^2` and the conflict degree is `2(t-1)`. If an ordinary extremal estimate has the form `A t^(2-alpha)`, (2) produces the factor

\[
(1-1/t)t^\alpha
\]

when normalized by `A n^(2-alpha)`. At `t=C2^k` and `alpha=2/(k+2)`, that factor tends to **4**.

Equality in (2) makes the relation to the **actual** number `ex(t,H)` sharp. Merely inserting an ordinary upper bound into that relation incurs the displayed factor; this does not assert that a particular nonsharp coefficient `A` must lose exactly 4. Section 5 gives a separate, unconditional obstruction to the specific leading product below 2 needed here, even with a controlled error.

## 3. A valid comparison for the actual square graph, including the error

Now return to `G`, and suppose it has no `Q_d`. Assume `e>0` and `b>=2`; the other cases are trivial. Use the same random injection `pi:A -> B`, but retain only its edges that belong to `G`:

```
M = {(x,pi(x)) in E(G)},     X=|M|,     mu=E[X]=e/b,
p=e/(ab)=mu/a.
```

For every outcome, `M` is a matching of `G`. Hence `S(G)[M]` is ordinarily `Q_k`-free. In particular the following is **unconditionally valid**:

\[
\boxed{s\leq b(b-1)\,\mathbb E[\operatorname{ex}(X,Q_k)].}     \tag{4}
\]

There is no assertion that `S(G)` itself is ordinarily cube-free. Ordinary extremality is applied only after endpoint disjointness has actually been enforced.

### Exact variance and a useful bound

Let the two original degree-square sums be `D_A=sum_x d(x)^2` and `D_B=sum_y d(y)^2`. Counting ordered disjoint pairs of original edges gives

\[
\mathbb E[X(X-1)]
 =\frac{e^2-D_A-D_B+e}{b(b-1)},
\]
\[
\operatorname{Var}X
 =\frac{e}{b-1}+\frac{e^2}{b^2(b-1)}
       -\frac{D_A+D_B}{b(b-1)}
 \leq \frac{b}{b-1}\mu(1-p).                                  \tag{5}
\]

The last step uses `D_A >= e^2/a` and `D_B >= e^2/b`.

For `0 <= alpha <= 1` and a nonnegative random variable of positive mean `mu`, weighted AM-GM gives

\[
u^{2-\alpha}\leq\alpha u+(1-\alpha)u^2\quad(u\geq0),
\]

and therefore

\[
\mathbb E[X^{2-\alpha}]
 \leq\mu^{2-\alpha}+(1-\alpha)\mu^{-\alpha}\operatorname{Var}X.
                                                                    \tag{6}
\]

Suppose, **only if separately established**, that nonnegative coefficients `A,B` satisfy

\[
\operatorname{ex}(x,Q_k)\leq A x^{2-\alpha}+B x
\quad\text{for every integer }0\leq x\leq a.                   \tag{7}
\]

Combining (4)--(7) yields the valid endpoint-disjoint comparison

\[
\boxed{\begin{aligned}
s\leq{}&A(1-1/b)b^\alpha e^{2-\alpha}\\
       &+A(1-\alpha)b^{1+\alpha}e^{1-\alpha}(1-p)
        +B(b-1)e.
\end{aligned}}                                                \tag{8}
\]

The second term divided by the first, when nonzero, is

\[
\frac{(1-\alpha)b^2(1-p)}{(b-1)e}.
\]

Thus the variance error is relatively `O(1/N)` for balanced positive-density original graphs. The obstruction in (8) is the **leading loss**, not that error: for `a=b=N/2=C2^k`, it tends to 4.

Equation (8) is conditional only on the explicitly stated ordinary bound (7), on its stated size range. No ordinary extremal induction is assumed to be available. A bound valid only above a size threshold cannot be inserted into (4) for smaller outcomes of `X` without accounting for those outcomes.

## 4. Dense original counterexamples force an exponential-in-dimension error coefficient

Fix an integer `C >= 1`, and set

\[
G_d=K_{m-1,(2C-1)m+1},\qquad N=2Cm=C2^d.
\]

This graph is `Q_d`-free: a connected bipartite cube has `m` vertices in each class, while one host class has only `m-1` vertices.

Nevertheless it is dense on this joint scale:

\[
\frac{e}{N^2}\longrightarrow\frac{2C-1}{4C^2}>0.
\]

Every vertex has degree of order `N`, with constants depending only on the fixed `C`. Directly,

\[
e=ab,\qquad s=\frac{a(a-1)b(b-1)}2,
\]
\[
\frac{s}{e^2}\longrightarrow\frac12,
\qquad e^{\alpha}\longrightarrow16,
\qquad\boxed{\frac{s}{e^{2-\alpha}}\longrightarrow8.}          \tag{9}
\]

Thus a comparison `s <= T_d e^(2-alpha) + o(e^2)` over all such dense original graphs requires `liminf T_d >= 8`. In particular it cannot have `T_d=L_d A_(d-1) -> L^2/2 < 2`.

More quantitatively, if `T_d -> T < 8` and the proposed error is `B_d N e`, then (9) forces

\[
\liminf_{d\to\infty}\frac{B_d}{m}
 \geq\left(1-\frac1{2C}\right)\left(\frac12-\frac{T}{16}\right).
                                                                  \tag{10}
\]

Hence `B_d=o(2^d)`, including any polynomial in `d`, is impossible. If the comparison is required for all fixed `C`, an error `K m N e` needs at least

\[
K\geq\frac12-\frac{T}{16}.
\]

### Balanced host parts do not by themselves fix this

For `C >= 2`, use two disjoint components

\[
K_{m-1,(C-1)m+1}\ \dot\cup\ K_{(C-1)m+1,m-1},
\]

with opposite bipartition orientations. Both global parts have size `Cm`; the graph is again cube-free and dense. Its degree ratio tends to `C-1`, a constant independent of dimension, and

\[
s/e^2\to1/4,\qquad s/e^{2-\alpha}\to4.
\]

So global balance plus a dimension-independent almost-regularity constant is not enough to justify a negligible-error comparison.

### Scope of this obstruction

For large `C`, these examples do **not** have `e >= N(N-1)/8`, the density supplied by a majority colour followed by a maximum cut. They refute the comparison over unrestricted positive-density original graphs, **not** the comparison restricted to that majority-cut density.

Moreover, the necessary error `K m N e` is still compatible with the Ramsey goal: at majority-cut density it is only `O(K/C)` relative to `e^2`. Thus (10) is a constraint on a successful finite-error theorem, not a refutation of every corrected square-graph approach.

## 5. Even the corrected small-loss theorem fails for generic endpoint-labelled auxiliaries

The exact relaxation theorem can be combined with a self-contained probabilistic construction. This shows that a loss below 2 cannot be obtained from endpoint conflict degree and regularity alone, **even after allowing `K m N e` errors**.

### Dense cube-free base graphs by alteration

Let `H=Q_k`, `m=2^k`, `ell=km/2`, and `t=Cm`. Choose

\[
p_k=((k-1)!)^{1/(\ell-1)}t^{-(m-2)/(\ell-1)}.
\]

This lies in `(0,1]` for `k>=2` and `t>=m`. A random graph `G(t,p_k)` has expected cube count at most

\[
\frac{t^m p_k^\ell}{m k!}=\frac{p_k t^2}{2\ell}.
\]

The denominator `m k!` is justified by the distinct translations and coordinate permutations of the cube; equality for the full automorphism group is not needed. Deleting one edge from every cube gives some cube-free `T` with

\[
e(T)\geq\frac12\left(1-\frac1t-\frac1\ell\right)p_k t^2.
                                                                  \tag{11}
\]

For every fixed `C`, `p_k -> 1/4`, so

\[
\liminf e(T)/t^2\geq1/8.
\]

One can also choose `T` asymptotically regular, with every degree `(1/4+o(1))t`: binomial concentration makes all original degrees `p_k(t-1)+o(t)` with probability tending to one, while Markov's inequality bounds the number of cubes by twice its expectation with probability at least one half. That expectation is `O_C(t/k)=o(t)`. Deleting at most that many edges changes **each** degree by at most `o(t)`. The two events have positive joint probability. This gives `e(T)/t^2 -> 1/8` as well.

### The auxiliary construction

Choose the asymptotically regular version of `T` just constructed. Use the **complete original label universe** `E(K_(t,t))`, but keep only the auxiliary edges

\[
(i,j)\sim_J(i',j')\quad\Longleftrightarrow\quad
 ii'\in E(T),\ j\ne j'.
\]

Then

* `v(J)=t^2`; the original vertex count is `N=2t=C2^d`, with `d=k+1`;
* the conflict degree is exactly `2(t-1)=O(N)`;
* `J` has no endpoint-disjoint `Q_k`, by the row projection;
* `e(J)=t(t-1)e(T)`, hence `e(J)/t^4 -> 1/8`;
* `J` can be asymptotically regular, of degree `(1/4+o(1))t^2`;
* both diagonals of every retained square are retained.

Write `e=t^2` for the size of this full original edge-label universe. Since `e^alpha -> 16`,

\[
\boxed{\frac{e(J)}{e^{2-\alpha}}\longrightarrow2.}             \tag{12}
\]

For any fixed `K >= 0` and `T_0 < 2`, a generic assertion

\[
e(J)\leq T_0 e^{2-\alpha}+K m N e                            \tag{13}
\]

would imply, after division by `e^2` and passage to the limit,

\[
1/8\leq T_0/16+2K/C.
\]

Choose a fixed integer `C > 32K/(2-T_0)` (and above any prescribed fixed minimum host ratio). This is false. Thus (13) is refuted with exactly the conflict degrees, target size, density, and controlled-error scale under consideration.

If `T_0` is the proposed limiting product `L A` and `A=L/2`, (12) forces `L^2/2 >= 2`, i.e. `L >= 2`, for this generic approach. There is no room for the desired strict loss below 2.

**Crucial qualification:** `J` is a spanning subgraph of `S(K_(t,t))`, not the full square graph. The complete original graph contains `Q_d`. The construction therefore does not refute (13) for `J=S(G)` and `Q_d`-free `G`. It refutes proving that estimate using only the relaxed hypotheses listed above, even with almost regularity and paired-diagonal symmetry.

## 6. A constant fraction of auxiliary cube copies cannot be made endpoint-disjoint

This is a different obstruction, concerning copy counts rather than edge extremality.

Take the actual original graph `G=K_(t,t)`, where `t=Cm`, `m=2^k` and the integer `C>=2` is fixed. Let

* `I_k(t)` be the number of ordinary **injective labelled** `Q_k` embeddings in `S(G)`;
* `D_k(t)` be the number whose original endpoint labels are all disjoint.

There is an exact formula

\[
D_k(t)=(t)_m^2.                                               \tag{14}
\]

Any independent injection of the cube vertices into the row set and into the column set is a valid auxiliary embedding, and these are all the endpoint-disjoint embeddings.

For an arbitrary ordering of the cube vertices, let `r_i <= k` be the number of preceding neighbours of vertex `i`, indexed from zero. After assigning its predecessors, at least

\[
(t-r_i)^2-i\geq t^2\left(1-\frac{2r_i}{t}-\frac{i}{t^2}\right)
\]

choices remain. If `t >= 4k+2` and `m<=t`, each parenthesized loss is at most `1/2`. Using `log(1-u)>=-2u` and `sum r_i=km/2` gives

\[
I_k(t)\geq t^{2m}\exp\left(-\frac{2km}{t}
                              -\frac{m(m-1)}{t^2}\right).
                                                                  \tag{15}
\]

On the other hand,

\[
D_k(t)\leq t^{2m}\exp\left(-\frac{m(m-1)}{t}\right).
\]

Consequently

\[
\frac{D_k(t)}{I_k(t)}
 \leq \exp\left(-\frac{m-1}{C}+\frac{2k}{C}+\frac1{C^2}\right)
 \longrightarrow0.                                           \tag{16}
\]

In fact, a Riemann sum in (14), together with (15) and `I_k(t)<=t^(2m)`, gives the exact exponential rate

\[
\frac1m\log\frac{D_k(Cm)}{I_k(Cm)}\longrightarrow-\gamma_C,
\qquad
\gamma_C=2\left[1+(C-1)\log(1-1/C)\right]>0.                  \tag{17}
\]

For large fixed `C`, `gamma_C=1/C+O(1/C^2)`.

Although `m Delta_conf/v(S) -> 2/C` can be as small as desired, the fraction of good **whole copies** is exponentially small. The accumulated number of potential pair collisions is of order `m^2/N`, not `m/N`.

This refutes a constant-fraction copy-count transfer. It does **not** refute the desired edge-count comparison: an exponentially small fraction of a sufficiently large, sufficiently well-distributed copy family can still leave many good copies. Such a distributional theorem is exactly what is missing.

## 7. What the two cited methods do and do not supply

The local sources were consulted directly; network access was unavailable.

### Correlated matchings, arXiv:1806.02838

For an `H_(s,t)`-free graph, where `H_(s,t)=K_(s,t) square K_2`, the correlated-matching lemma bounds the number of suitably `2t`-correlated `s`-matchings in `N(M)` by

\[
(s-1)(t-1)e(N(M))^{s-1}v(N(M)).
\]

The crucial subsequent step is: for an `s`-matching `L`, `N(L)` has matching number at most `t-1`, since otherwise `L` and a disjoint `t`-matching form `H_(s,t)`. This is a complete-cross-edge condition, not the sparse cube adjacency pattern.

The local common-neighbourhood identity itself remains valid for square graphs. For an endpoint-disjoint matching `M={x_i y_i}`,

\[
\bigcap_{f\in M}N_{S(G)}(f)
 = E\bigl(G[X_M,Y_M]\bigr),
\]

where

\[
X_M=(\bigcap_i N_G(y_i))\setminus\{x_i\},\qquad
Y_M=(\bigcap_i N_G(x_i))\setminus\{y_i\}.
\]

What is not available is the analogous small matching-number bound for a cube's partial neighbour set. For example, in the dense cube-free graph `K_(m-1,b)`, any `r`-matching has neighbourhood graph `K_(m-1-r,b-r)`. For `r` of order `d`, this still has a matching of order `m`, not of order `d`. Thus original density alone does not repair the missing implication.

### Grids, arXiv:2203.05485

The balanced ladder extension bound controls the number of extensions through specified original coordinates. Its final auxiliary embedding is of a **tree**, so each new auxiliary vertex has one previously embedded neighbour. A cube requires simultaneous adjacency to several previously embedded vertices; the necessary multi-neighbour extension estimate is not proved there.

The theorem concerns `T square P`, with `T` a tree and `P` a path. Its displayed parameter choice is `(16K)^(r^2 t^3)`, with `r=|T|` and `t=|P|`. There is neither a small-loss cube-dimension recurrence nor a dimension-uniform error estimate in this argument. Applying it to a cube as if the auxiliary target were a tree would omit the cycle-closing conditions.

Relevant local passages are `/corpus/src/1806.02838/1806.02838.tex` (the correlated-matching lemma and the two counting claims, around lines 401--504), and `/corpus/src/2203.05485/2203.05485.tex` (the good-ladder definition, the two-sided extension lemma, and the final tree embedding, around lines 98--205).

## 8. The exact remaining estimate and a verified sufficiency calculation

The following would be enough; it is **not proved here**.

> There exist absolute `0<epsilon<2`, `K>=0`, `C_0>=1`, and `d_0`, such that every `Q_d`-free bipartite graph with `d>=d_0`, `N>=C_0 2^d`, and `e>=N(N-1)/8` satisfies
> \[
> s\leq(2-\epsilon)e^{2-2/(d+1)}+K2^{d-1}Ne.                 \tag{18}
> \]

The leading coefficient in (18) is the **product** `L_d A_(d-1)`, not `L_d` alone. A limiting loss `L<2` with `A_(d-1)->L/2` would supply such an epsilon for all sufficiently large dimensions.

Here is an explicit verification that the permitted error really is controlled. Put `h=2^d`, `m=h/2`, and choose

\[
C\geq\max\{C_0,6,128(K+1)/\epsilon\}.
\]

For `d>=1`, `N>=Ch`, and `e>=N(N-1)/8`,

\[
e\geq4h^2,\qquad e^{2/(d+1)}\geq16.
\]

The lower bound (1) yields

\[
\frac{s}{e^2}\geq\frac18-\frac{17}{4N}.
\]

The claimed upper bound (18) would yield

\[
\frac{s}{e^2}\leq\frac{2-\epsilon}{16}
                   +\frac{8Km}{N-1}.
\]

But

\[
\frac{8Km}{N-1}+\frac{17}{4N}
 \leq\frac{8K+17/8}{C}<\frac{\epsilon}{16},
\]

a contradiction. A majority colour in `K_N` has at least `N(N-1)/4` edges, and a maximum cut retains at least half, giving exactly the density used above. The finitely many smaller dimensions can be absorbed into a larger Ramsey constant.

Thus an `O(2^d N e)` auxiliary error does **not** itself prevent the linear conclusion. The unresolved task is specifically to prove (18), or a comparably strong statement, using **full square completion in the original graph**. Equations (2), (12), and (16) rigorously explain why treating the auxiliary graph as merely a regular graph with sparse endpoint conflicts, or keeping a constant fraction of ordinary cube copies, cannot supply it.

## Verification

`check_cube_endpoint_conflicts.py` checks the random-injection identities and variance bound on exhaustive small bipartite examples; checks the cube/square-matching equivalence for all `4 x 4` bipartite graphs; exhausts nontrivial small instances of (2); checks its extremizing construction, diagonal symmetry, and the missing full-completion property; checks the dense-obstruction and random-alteration normalizations; checks the birthday-count algebra; and checks the finite constants in the conditional sufficiency calculation.

These checks complement the proofs above. None asserts (18), the unproved ordinary extremal induction, or the Ramsey conclusion.
