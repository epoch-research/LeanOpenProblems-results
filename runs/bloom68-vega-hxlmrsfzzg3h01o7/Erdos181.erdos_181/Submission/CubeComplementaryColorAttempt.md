# Complementary colours and full-square completion: a quantitative partial bound

## Outcome

**The arbitrary-host assertion `R(Q_d) <= C 2^d` remains unproved.** This attempt does not supply an absolute Ramsey constant, a finite-population commonness theorem, or the coefficient below 2 requested in `CubeEndpointConflictInvestigation.md`.

There is a proved, universally quantified full-square bound below. It applies to **every** cube-free bipartite graph in the requested density/host-size range, not to a prescribed family of hosts, boundaries, or extension laws. Its proof produces actual injective cubes when the square-count ceiling is violated.

Write `h=2^d`, `m=h/2`, and let `G=(A,B)` have `a+b=N` vertices, `e>0` edges, and `s=e(S(G))` edges in its **full** square graph. Put

\[
 D_A=\sum_{x\in A}d(x)^2,\qquad D_B=\sum_{y\in B}d(y)^2,
 \qquad \lambda=\frac{e}{Nh}.
\]

For `d>=2` and `lambda>=64`, define

\[
 q=\left(\frac{64}{\lambda}\right)^{1/(d+1)},\qquad
 \psi_d(\lambda)=
 \min\left\{\frac1{12},\frac{1-q}{6-2q}\right\}.
                                                        \tag{A}
\]

The new deduction in this report is the following inequality:

> **Full-square ceiling.** If `G` is `Q_d`-free, then
> \[
> \boxed{
> s<\frac{1-\psi_d(\lambda)}2\,e^2
>       -\frac{D_A+D_B-e}{2}.}
>                                                        \tag{B}
> \]

In particular, under exactly the density qualification relevant to the Ramsey reduction,

\[
 N\ge4096h,\qquad e\ge\frac{N(N-1)}8,
\]

cube-freeness implies the simpler bound

\[
 \boxed{
 s<\frac12\left(1-\frac1{12d}\right)e^2
       -\frac{D_A+D_B-e}{2}.}
                                                        \tag{C}
\]

Conversely, failure of the strict upper bound in (C) gives at least

\[
 \boxed{(N/4096)^h}
                                                        \tag{D}
\]

labelled, bipartition-respecting injective copies of `Q_d`.

This is a genuine numerical restriction on an arbitrary counterexample. **It is quantitatively insufficient:** at fixed `N/h=C`, the coefficient of `e^(2-2/(d+1))` furnished by (B) tends to **8**, whereas the sufficient target requires a coefficient **strictly below 2**. Sections 6–8 make this gap explicit and explain why summing the two complementary colours does not close it.

No Lean file was changed. In particular, `Spec.lean` is unchanged.

---

## 1. The quantity that really records full square completion

Let `M` be the `a x b` zero-one adjacency matrix of `G`. Define

\[
 T_4(G)=\sum_{x,x'\in A}\sum_{y,y'\in B}
          M_{xy}M_{xy'}M_{x'y}M_{x'y'}
       =\operatorname{tr}((MM^T)^2).
                                                        \tag{1.1}
\]

This is the **bipartition-respecting** `C_4` homomorphism count, with repeated vertices allowed. It is not the usual unoriented number of four-cycles; the ordinary full-graph homomorphism count is twice (1.1).

For row codegrees `c(x,x')=|N(x) intersect N(x')|`,

\[
 T_4=\sum_{x,x'}c(x,x')^2
    =4C_4(G)+D_A+D_B-e
    =2s+D_A+D_B-e.
                                                        \tag{1.2}
\]

Define the normalized completion defect

\[
 \delta=1-\frac{T_4}{e^2}.
                                                        \tag{1.3}
\]

It is nonnegative. More importantly, it has the literal interpretation

\[
 \boxed{
 \delta e^2=
 \sum_{(x,y),(x',y')\in E(G)}
       \bigl(1-M_{xy'}M_{x'y}\bigr).}
                                                        \tag{1.4}
\]

Thus `delta` is the probability that two independent uniform original edges fail to complete a rectangle. If the edges share an endpoint, the product in (1.4) is one, as it should be. No spurious loss for such a pair is introduced into this definition.

Equation (1.4), not just the degree of the endpoint-conflict graph, drives the argument. For a generic auxiliary graph on endpoint labels, an absent auxiliary edge need not mean that a cross-cell is absent from the original bipartite graph. Consequently the rectangle extraction in the next section cannot be applied to the endpoint-label relaxation from the earlier report.

---

## 2. An actual rectangle extracted from a small completion defect

### Lemma 2.1 — quantitative rectangle extraction

Suppose `e>0` and `0<=delta<=1/12`. There are sets `X subset A` and `Y subset B` such that

\[
 |X|,|Y|\ge\frac{e}{2N},                                  \tag{2.1}
\]

and

\[
 \boxed{
 \frac{e(G[X,Y])}{|X||Y|}
 \ge p_\delta:=\frac{1-6\delta}{1-2\delta}.}
                                                        \tag{2.2}
\]

More precisely,

\[
 e(G[X,Y])\ge(1-6\delta)e,\qquad
 |X||Y|-e(G[X,Y])\le4\delta e,                            \tag{2.3}
\]

and `|Y|>=e/(2a)`.

### Proof

For a row `x`, write `d_x=d(x)` and

\[
 E_x=d_x e-\sum_{z\in A}c(x,z)^2\ge0.
\]

The inequality follows from `c(x,z)^2<=d_x d_z`. Also,

\[
 \sum_x E_x=e^2-T_4=\delta e^2.                            \tag{2.4}
\]

Sample a positive-degree row with probability `d_x/e`. The expectation of
`E_x/(d_x e)` is `delta`. Rows with `d_x<e/(2a)` have total sampling probability strictly less than `1/2`. It follows that some row `x_0` satisfies simultaneously

\[
 d_{x_0}\ge\frac{e}{2a},\qquad
 \frac{E_{x_0}}{d_{x_0}e}\le2\delta.                      \tag{2.5}
\]

Indeed, otherwise every row in a set of sampling probability greater than `1/2` would have normalized defect greater than `2 delta`, contradicting (2.4). When `delta=0`, every positive-degree row has defect zero and the same conclusion is immediate.

Set

\[
 Y=N(x_0),\qquad t=|Y|,\qquad c_z=|N(z)\cap Y|,
 \qquad \eta=2\delta.
\]

Then (2.5) says

\[
 \sum_{z\in A}\left(d_z-\frac{c_z^2}{t}\right)\le\eta e.
                                                        \tag{2.6}
\]

Every summand is nonnegative. Since `c_z^2/t<=c_z`, the number of edges outside `A x Y` is at most `eta e`.

Now take

\[
 X=\{z\in A:c_z\ge t/2\}.
\]

For `z notin X`,

\[
 d_z-\frac{c_z^2}{t}
 \ge c_z\left(1-\frac{c_z}{t}\right)\ge c_z/2.
\]

Thus at most `2 eta e` edges of `A x Y` have their row outside `X`. This proves

\[
 e(G[X,Y])\ge(1-3\eta)e.                                 \tag{2.7}
\]

For `z in X`, instead use

\[
 d_z-\frac{c_z^2}{t}
 \ge\frac{c_z}{t}(t-c_z)\ge(t-c_z)/2.
\]

Summing shows that `X x Y` has at most `2 eta e` missing edges. Together with (2.7), this gives density at least

\[
 \frac{1-3\eta}{1-3\eta+2\eta}
 =\frac{1-6\delta}{1-2\delta}.
\]

Finally, `|Y|>=e/(2a)` by construction. Since `delta<=1/12`, (2.7) gives at least `e/2` edges in the rectangle, and hence

\[
 |X|\ge\frac{e}{2b}.
\]

Both estimates imply (2.1). ∎

**What has been completed here.** The rectangle is an actual subgraph of `G`, obtained from original neighbourhoods. The proof charges failures to *missing cross-edges*, and keeps the complete rectangle rather than a chosen collection of its diagonals. This is precisely the extra information absent from a generic endpoint-labelled auxiliary graph.

---

## 3. A direct injective count inside the extracted rectangle

The next lemma is included with proof so that the argument does not end at a homomorphism count or at a conditional Hall certificate. The use of dependent random choice is elementary; no novelty claim for that method is intended.

### Lemma 3.1 — balanced density-to-injection bound

Let `d>=2`, `m=2^(d-1)`, and `h=2m`. Let `F=(U,V)` be bipartite with `|U|=|V|=L` and density at least `p`, where `0<p<=1`. If

\[
 \boxed{L p^{d+1}\ge64m,}                                \tag{3.1}
\]

then the number `I_d(F)` of labelled embeddings of `Q_d`, with its fixed even parity class in `U` and odd parity class in `V`, satisfies

\[
 \boxed{
 I_d(F)\ge\left(\frac{p^{d+1/2}L}{32}\right)^h.}
                                                        \tag{3.2}
\]

All maps counted in (3.2) are injective on **both** parity classes, which have disjoint host parts.

### Proof

Put `theta=p^d` and choose `d` independent uniform vertices of `V`, with replacement. Let `W` be their common neighbourhood in `U`. Jensen's inequality gives

\[
 \mathbb E|W|
 =\sum_{u\in U}\left(\frac{d_F(u)}L\right)^d
 \ge \theta L.                                          \tag{3.3}
\]

Set

\[
 T=\left\lfloor\frac{p^{d+1}L}{16}\right\rfloor.
                                                        \tag{3.4}
\]

By (3.1), `T>=4m`. Call an **ordered tuple of d distinct vertices** of `U` bad if its common neighbourhood in `V` has size less than `T`. Let `B(W)` count bad ordered tuples lying in `W`.

For a fixed bad tuple, the probability that it lies in `W` is at most `(T/L)^d`. Consequently

\[
 \mathbb E B(W)\le(L)_d(T/L)^d\le T^d.                    \tag{3.5}
\]

Since `0<=|W|<=L`, (3.3) implies

\[
 \Pr(|W|\ge\theta L/2)\ge\frac{\theta}{2-\theta}
 \ge\theta/2.
\]

By Markov's inequality,

\[
 \Pr\left(B(W)>\frac{4T^d}{\theta}\right)\le\theta/4.
\]

There is therefore an outcome with

\[
 w:=|W|\ge\theta L/2,\qquad B(W)\le4T^d/\theta.            \tag{3.6}
\]

In particular, (3.1) gives `w>=32m/p>=32m`, and `m>=d` for `d>=2`.

Choose a uniform injection of the even cube class into `W`. For each odd source vertex, the images of its `d` neighbours form a uniform ordered distinct `d`-tuple, after fixing an order on those neighbours. The probability that at least one odd vertex gets a bad tuple is at most

\[
 \begin{aligned}
 m\frac{B(W)}{(w)_d}
 &\le\frac{4m}{\theta}
          \left(\frac{4T}{\theta L}\right)^d\\
 &\le\frac{4m}{p^d}\left(\frac p4\right)^d
   =\frac{4m}{4^d}=2^{1-d}\le\frac12.                    \tag{3.7}
 \end{aligned}
\]

Here `(w)_d >= (w/2)^d` follows from `w>=2d`. This retains the finite-population denominator; it is not a replacement-sampling approximation for the source injection.

At least half of the `(w)_m` first-parity injections consequently give every odd vertex at least `T` candidates in `V`. For each such injection, embed the odd vertices greedily. At its `j`-th step there are at least `T-j` choices. There are thus at least

\[
 (T)_m\ge(T/2)^m
\]

extensions, since `T>=4m`. Every source edge is checked by its odd endpoint's candidate list. No edges within a parity class are required.

Finally,

\[
 (w)_m\ge(w/2)^m\ge(\theta L/4)^m,
 \qquad
 T\ge\frac{p^{d+1}L}{32}.
\]

The latter follows from (3.4), since its unfloored quantity is at least `4m>=8`. Hence

\[
 \begin{aligned}
 I_d(F)
 &\ge\frac12(w)_m(T/2)^m\\
 &\ge\frac12\left(\frac{p^{2d+1}L^2}{256}\right)^m
  =\frac12\left(\frac{p^{d+1/2}L}{16}\right)^h\\
 &\ge\left(\frac{p^{d+1/2}L}{32}\right)^h.
 \end{aligned}
\]

This proves (3.2). ∎

---

## 4. Combining full square completion with genuine injection

### Theorem 4.1 — an injection-producing full-square inequality

Let `G`, `delta`, and `lambda` be as in Sections 1–2, with `d>=2`. Suppose

\[
 0\le\delta\le\frac1{12},\qquad
 \boxed{\lambda
     \left(\frac{1-6\delta}{1-2\delta}\right)^{d+1}
     \ge64.}                                             \tag{4.1}
\]

Then

\[
 \boxed{
 I_d(G)\ge
 \left(\frac{e}{64N}
       \left(\frac{1-6\delta}{1-2\delta}\right)^{d+1/2}
 \right)^h>0.}                                           \tag{4.2}
\]

### Proof

Extract `X,Y` by Lemma 2.1 and put `L=min(|X|,|Y|)`. Keep the smaller side and choose an `L`-element subset of the larger side. Averaging over this choice supplies a balanced rectangle of density at least `p_delta`.

Since `L>=e/(2N)=lambda m`, (4.1) implies

\[
 Lp_\delta^{d+1}\ge64m.
\]

Lemma 3.1 applies. Its count is at least (4.2), using `L>=e/(2N)`. The counted embeddings are embeddings in the original graph. ∎

### Corollary 4.2 — proof of the universal ceiling (B)

Assume `lambda>=64`, and let `q,psi` be given by (A). The function

\[
 p_\delta=\frac{1-6\delta}{1-2\delta}
\]

is decreasing on `[0,1/12]`, and

\[
 p_\delta\ge q
 \quad\Longleftrightarrow\quad
 \delta\le\frac{1-q}{6-2q}.                              \tag{4.3}
\]

If `delta<=psi`, (4.1) holds because `lambda q^(d+1)=64`. Theorem 4.1 would give an injective cube. Thus every cube-free `G` has

\[
 \delta>\psi_d(\lambda).
                                                        \tag{4.4}
\]

Substitute (1.2)–(1.3) into (4.4) to obtain (B).

This is not an inequality conditional on a chosen extension distribution: all its inputs are the original graph's order, edge count, degree squares, and number of full squares.

### Corollary 4.3 — explicit linear-host branch

Suppose

\[
 N\ge4096h,\qquad e\ge N(N-1)/8,
 \qquad \delta\le1/(12d).
\]

Then

\[
 p_\delta\ge1-\frac1{2d}.
                                                        \tag{4.5}
\]

Indeed,

\[
 1-p_\delta=\frac{4\delta}{1-2\delta}
 \le\frac2{6d-1}\le\frac1{2d}.
\]

Bernoulli's inequality gives `p_delta^d>=1/2`; also `p_delta>=3/4` because `d>=2`. Therefore

\[
 p_\delta^{d+1}\ge3/8,
 \qquad
 \lambda\ge\frac{N-1}{8h}>511.
\]

These inequalities imply (4.1), with ample margin. Moreover,

\[
 p_\delta^{d+1/2}\ge1/4,
 \qquad \frac{e}{64N}\ge\frac{N-1}{512}\ge\frac N{1024}.
\]

Equation (4.2) now proves (D). Its contrapositive proves (C).

The cases `d=0,1` are elementary and are not needed in the quantitative statement above.

### Application to an arbitrary complete two-coloured host

A majority colour in `K_N` has at least `N(N-1)/4` edges. A maximum cut of that colour keeps at least half of them, so its bipartite graph `G` has exactly the density required above. If its completion defect is at most `1/(12d)`, Corollary 4.3 supplies a monochromatic injective cube, with the count (D). Otherwise it lies in the remaining positive-defect branch. More generally, in a two-colouring with neither monochromatic cube, **every** bipartite colour subgraph with `lambda>=64` must obey (B).

This gives an unconditional restriction on arbitrary countercolourings. It does not show that their remaining branch is empty.

---

## 5. What complementarity supplies exactly

I also pursued the proposed complementary-colour route rather than treating the two colours as unrelated dense graphs.

Fix any host cut `(A,B)`. On this cut the red and blue zero-one matrices satisfy

\[
 M_R+M_B=J_{a,b}
\]

**exactly**, with no diagonal convention to repair. The weakly norming cube inequality therefore gives, for bipartition-respecting homomorphisms,

\[
 \operatorname{hom}_{A,B}(Q_d,R)
 +\operatorname{hom}_{A,B}(Q_d,B)
 \ge2^{1-dh/2}(ab)^{h/2}.                                \tag{5.1}
\]

On the unsplit loopless host, one should instead retain the finite correction. For example the usual density argument gives

\[
 \operatorname{hom}(Q_d,R)+\operatorname{hom}(Q_d,B)
 \ge2^{1-dh/2}(1-1/N)^{dh/2}N^h.
                                                        \tag{5.2}
\]

The norm triangle inequality also gives the stronger exact comparison with `2^(1-dh/2) hom(Q_d,K_N)`. Dropping these diagonal issues is unnecessary here: (5.1) is exact on the cut.

At the full-square level there is a useful exact completion of the two colours. Put

\[
 S=M_R-M_B=2M_R-J,
 \qquad r=S\mathbf1_b,
 \qquad c=S^T\mathbf1_a,
 \qquad \sigma=\mathbf1_a^TS\mathbf1_b.
\]

Then

\[
 \boxed{\begin{aligned}
 T_4(R)+T_4(B)=\frac18\bigl[&a^2b^2
       +2a\|r\|^2+2b\|c\|^2+2\sigma^2\\
       &+\operatorname{tr}((SS^T)^2)\bigr].
 \end{aligned}}                                          \tag{5.3}
\]

For completeness, set

\[
 P=JJ^T,\qquad Q=SS^T,\qquad H=JS^T+SJ^T.
\]

The two Gram matrices are `(P+Q+H)/4` and `(P+Q-H)/4`. Adding the traces of their squares gives

\[
 \frac18\operatorname{tr}((P+Q)^2+H^2).
\]

Now

\[
 \operatorname{tr}P^2=a^2b^2,\quad
 \operatorname{tr}(PQ)=b\|c\|^2,\quad
 H=\mathbf1_a r^T+r\mathbf1_a^T,
\]

and `tr(H^2)=2a||r||^2+2 sigma^2`, proving (5.3).

Equation (5.3) retains all degree variation and uses the actual complementary matrices. But it is a statement about full squares, not a positivity theorem for the finite-population cube partition function. In particular, it does **not** authorize replacing a Kneser-disjointness form by its constant eigenspace, or summing absolute collision errors against the random baseline.

---

## 6. The attempted bootstrap and its quantitative failure

The hope was to use full square completion to turn a sufficiently large monochromatic square contribution into a large, highly compatible region, then pay the entire injectivity cost inside that region. Theorem 4.1 does this when the square count is close enough to its **maximum** `e^2`. It includes a count of whole injections rather than a comparison of individual signed diagrams.

The needed Ramsey regime is very different.

Two Cauchy–Schwarz inequalities give

\[
 T_4(G)\ge\frac{e^4}{a^2b^2},
 \qquad
 \frac{T_4(G)}{e^2}\ge\left(\frac{e}{ab}\right)^2.
                                                        \tag{6.1}
\]

For `e>=N(N-1)/8` and `ab<=N^2/4`, this only forces

\[
 \frac{T_4}{e^2}\ge\frac14(1-1/N)^2,
 \qquad
 \delta\le\frac34+O(1/N).                                \tag{6.2}
\]

The extraction in Section 2 needs `delta<=1/12`, and its constant-multiplier injection condition is much stricter asymptotically: `delta` must be of order `log(N/h)/d`.

To see this directly, suppose `N/h -> C>512` and `e/N^2 -> rho>=1/8`, with `C,rho` fixed. Then

\[
 \begin{aligned}
 \lambda&\longrightarrow\rho C,\\
 \psi_d(\lambda)
 &=\frac{\log(\lambda/64)}{4(d+1)}+O_C(d^{-2})\\
 &=\frac{\log(\rho C/64)}{4(d+1)}+o_C(1/d).
 \end{aligned}                                           \tag{6.3}
\]

The cap `1/12` is inactive for all sufficiently large `d`. Thus (B) only forces a defect tending to zero, whereas commonness is compatible with defect close to `3/4`.

There is no valid iteration that turns (6.2) into the hypothesis of Lemma 2.1. The lemma's proof is based on a *small number of missing rectangle completions*. At a completion ratio near `1/4`, there are roughly `3e^2/4` missing completions, and the estimates (2.7) and (2.3) do not leave a useful almost-complete rectangle.

Likewise, adding the two colours in (5.3) provides a lower bound near the commonness scale; it does not force either colour's completion ratio to be close to one. A claimed implication of that kind would discard precisely the diffuse regime that the original problem must handle.

The injection step in Section 3 only uses the cube's bipartition size and maximum degree. The actual full-square structure is used in Section 2 to extract the host rectangle. There is no claim that this generic density-to-injection step exploits the higher-dimensional commuting-face geometry needed to improve the moderate-completion regime.

---

## 7. Comparison with the sufficient endpoint-conflict target

The requested sufficient inequality was

\[
 s\le(2-\varepsilon)e^{2-\alpha}+K mNe,
 \qquad \alpha=\frac2{d+1},\quad m=h/2.                   \tag{7.1}
\]

At fixed `N/h=C` and positive limiting `e/N^2`,

\[
 e^\alpha\longrightarrow16.
\]

The leading part of our proved upper bound (B), when written in the same normalization, has coefficient

\[
 \frac12(1-\psi_d(\lambda))e^\alpha\longrightarrow8.
                                                        \tag{7.2}
\]

This is not the product below 2 needed in (7.1). A larger **fixed** value of `C` changes the first-order term in (6.3), but not the limit 8 in (7.2).

The gap can also be written without any auxiliary-graph coefficient. Since

\[
 0\le D_A+D_B-e\le(N-1)e,
\]

the degree correction divided by `e^2` is at most `8/N` at the required density. If (7.1) held, then (1.2) would imply

\[
 \frac{T_4}{e^2}
 \le2(2-\varepsilon)e^{-\alpha}
       +\frac{2KmN}{e}+\frac8N.                         \tag{7.3}
\]

At `N/h=C`, this is asymptotically

\[
 \frac{T_4}{e^2}\le\frac14-\frac\varepsilon8
                          +O(K/C)+o(1),
                                                        \tag{7.4}
\]

or

\[
 \delta\ge\frac34+\frac\varepsilon8-O(K/C)-o(1).
                                                        \tag{7.5}
\]

That would contradict (6.2) for a sufficiently large fixed `C`. What is proved here is only `delta>psi_d(lambda)`, with `psi=O_C(1/d)`.

**The remaining unproved step is therefore a genuine moderate-completion estimate:** cube-freeness at majority-cut density must force the full-square completion ratio below its Sidorenko/commonness floor, up to the allowed `O(h/N)` correction. The high-completion rectangle argument does not prove such an estimate. No assertion of it is being included as a lemma or smuggled into the injection count.

---

## 8. Relation to the known reflection obstructions

The earlier reports were used as scope checks:

* `CubeSignedActivityLemmas.md` gives exact collision-contraction and whole-star formulas, but no general bound on negative non-star activities.
* `CubeFinitePopulationReflection.md` constructs actual complementary colourings in which injective-boundary, individually injective half-extensions form intersecting phase families. Their negative Kneser mass can exceed the random baseline by `exp((1/2-o(1))h log h)`. Complementarity and ordinary quasirandomness do not remove that example.
* `CubeEndpointConflictInvestigation.md` distinguishes full square completion from a graph that merely keeps both diagonals of selected squares. The proof of Lemma 2.1 really needs the former.
* The global flow/cut certificates in `CubeAdaptiveBridgeAttempt.md` do not imply the missing moderate-completion estimate and have not been used as if they did.

In particular, the near-maximal-square branch proved here does **not** eliminate the previous quasirandom reflection examples. To check the scale analytically, take a balanced cut with `a,b` of order `N` in a colouring whose signed adjacency operator norm is `o(N)`. On that cut,

\[
 M_R=J/2+E,\qquad\|E\|_{op}=o(N).
\]

Its edge count is `ab/2+o(N^2)`. The largest singular value is `sqrt(ab)/2+o(N)`, and every other singular value is `o(N)`. Since the sum of the squared singular values is `e=O(N^2)`,

\[
 T_4(R)=a^2b^2/16+o(N^4).
\]

Consequently `T_4(R)/e(R)^2 -> 1/4`, and the same holds in blue. Their completion defect tends to `3/4`, outside our high-completion branch. This is a substantive check against the existing obstruction, not a claim that the obstruction colouring is cube-free.

The earlier actual-square obstruction `K_(m-1,b)` is also consistent with the theorem. It has `delta=0`, but

\[
 \lambda=\frac{(m-1)b}{(m-1+b)\,2m}<\frac12,
\]

so it fails (4.1) and lies outside the `lambda>=64` ceiling. A large ratio `N/h` alone cannot replace the density/capacity qualification.

The exact signed activity expansion remains available for a future argument in that diffuse regime. Nothing above bounds its absolute negative part, proves a positive fraction of disjoint half-pairs, or replaces whole-copy injectivity by an occupancy marginal.

---

## 9. Verification and final status

The verification here is by the all-dimensional proofs, not by further enumeration of finite identities. The points checked explicitly were:

1. **Counting convention:** `T_4=2s+D_A+D_B-e`, including equal-row and equal-column terms; `delta e^2` counts actual missing cross-edge completions.
2. **Extraction:** the weighted pivot has both sufficient degree and defect at most `2 delta`; edges outside the rectangle and holes inside it are charged separately.
3. **Finite population:** Lemma 3.1 counts ordered distinct tuples, uses `(w)_d` and `(w)_m`, and embeds the second parity class without replacement into a disjoint host part.
4. **Thresholds and floors:** `L p^(d+1)>=64m` gives `T>=4m`, `w>=32m`, and the union bound is exactly at most `2^(1-d)<=1/2`, including `d=2`.
5. **Multiplicity:** the displayed lower bound counts labelled embeddings of the actual cube, not only candidate lists, matchings of unrelated labels, or homomorphisms.
6. **Universal contrapositive:** (B) holds for every cube-free bipartite `G` with `lambda>=64`; the additional density hypothesis in (C) is the original majority-cut density.
7. **Target normalization:** the proved leading coefficient tends to 8, not to a number below 2; the allowed error in (7.1) does not conceal this factor-four gap.
8. **Known bad phases:** the previous quasirandom reflection constructions lie at completion ratio `1/4`, so the argument has not inadvertently claimed to rule them out.

`Submission/Spec.lean` retains SHA-256

```text
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```

**Final status:** a direct, quantitative full-square-to-injection implication and its universal cube-free square-count ceiling are proved. The complementary-colour commonness calculation does not upgrade that ceiling to the moderate-completion regime. The arbitrary red-blue Ramsey conclusion and the sufficient coefficient-below-2 inequality remain open in this work.
