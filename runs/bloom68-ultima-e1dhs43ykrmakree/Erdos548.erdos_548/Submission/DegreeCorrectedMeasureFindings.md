# A degree-corrected measure: a proved critical-split lemma and the general gap

**Status: no full Erdős–Sós proof.** The additional result is a weighted
leaf-extension theorem for **every tree** in the critical split family, with
a constant extension bound whenever the leaf-deleted tree has a perfect
matching. In particular it repairs, simultaneously at every leaf, the
subcubic counterexample family to uniform counting. The measure is specified
without knowing which embeddings extend. A general critical-host implication
remains explicitly unproved. No specification or other Lean file was changed.

All embeddings below are injective homomorphisms, not induced copies.

## 1. The measure and its exact extension identity

For a nontrivial tree R and a host without isolated vertices, define

\[
 w_R(f)=\prod_{u\in V(R)}d_G(f(u))^{1-d_R(u)},\qquad
 Z(R,G)=\sum_{f\in\operatorname{Emb}(R,G)}w_R(f).                 \tag{1}
\]

These weights are strictly positive on existing embeddings, so
`Z(R,G)>0` is exactly containment.

This is the standard tree-indexed random-walk weight, **not** a claim about
stationary marginals after conditioning on injectivity. Indeed, choose a root
image with probability `d(v)/(2m)` and send each child independently to a
uniform neighbor of its parent. The probability of any homomorphism f is
`w_R(f)/(2m)`, irrespective of the chosen root. Consequently the sum over
**all homomorphisms** is `2m`; the injective sum need not have stationary root
marginals.

For a leaf ell with parent p, put `U=T-ell`. Directly from (1),

\[
 \boxed{Z(T,G)=\sum_{f\in\operatorname{Emb}(U,G)}
 w_U(f)\frac{|N_G(f(p))\setminus f(V(U))|}{d_G(f(p))}.}          \tag{2}
\]

No scalar evaluation of square-zero generators or Jensen step is involved.
Whenever `Z(U,G)>0`, its normalized distribution on embeddings is the Gibbs
law maximizing entropy minus
`sum_u (d_U(u)-1) E[log d_G(f(u))]`. Thus the degree correction is a fixed
energy, not retrospective selection of the extendible states.

## 2. Main lemma: all critical split hosts and all trees

Let

\[
 G_r=K_r\vee\overline K_b,\quad b=r^2+1,\quad
 D=r(r+1),\quad q=\frac1{r+1},\quad k=2r.
\]

The clique A has degree D and the independent part B has degree r.
These are genuine critical hosts:

\[
 2m=(2r-1)n+1.
\]

For a vertex subset using x clique vertices and y independent vertices,

\[
 2e(S)-(2r-1)|S|=x(x-2r)+(2x-2r+1)y.
\]

This is nonpositive if `x<=r-1`; if `x=r` and S is proper, it is
`y-r²<=0`. Thus **all** proper induced-subgraph inequalities hold.

**Theorem.** Let T be any `2r`-edge tree, ell any leaf, and `U=T-ell`.
For `r>=2`,

\[
 \boxed{\frac{Z(T,G_r)}{Z(U,G_r)}
 \ge\frac1{r\left(1+(1+q)^{2r-1}\right)}
 >\frac1{10r}.}                                               \tag{3}
\]

If U has a perfect matching, the stronger bound holds for every `r>=1`:

\[
 \boxed{\frac{Z(T,G_r)}{Z(U,G_r)}
 \ge\frac{r^2-r+1}{r(r+1)\left(1+(1+q)^{r-1}\right)}
 >\frac18.}                                                  \tag{4}
\]

### Proof of (3)

For an embedding of U, let `I=f^{-1}(B)` and `C=V(U)\I`. Then I is an
independent set. Write `s=|I|` and `j=e_U(C)`. Necessarily
`r<=s<=2r-1`. Conversely **every** such independent-set pattern is realizable,
and the number of injections realizing it is
`(r)_(2r-s) (b)_s`.

Since U has `2r-1` edges,

\[
 \sum_{u\in C}(d_U(u)-1)=s-1+j,\qquad
 \sum_{u\in I}(d_U(u)-1)=2r-1-s-j.
\]

Its total weight is therefore exactly

\[
 A_s q^j,\qquad
 A_s=\frac{(r)_{2r-s}(b)_s}{D^{s-1}r^{2r-1-s}}.                \tag{5}
\]

Let p be the deleted leaf's parent. Formula (2)'s extension factor is

\[
 \begin{cases}
 (b-r)/D,&p\in C,\\
 (s-r)/r,&p\in I.
 \end{cases}                                                 \tag{6}
\]

Thus **exactly** the patterns `s=r, p in I` are blocked. Every other pattern
has extension factor at least `1/r` when `r>=2`.

Let `W_0,W_1` be the total blocked and unblocked weights. We prove

\[
 W_0\le A_r(1+q)^{2r-1},\qquad W_1\ge A_r.                    \tag{7}
\]

For the first inequality, fix `p in I`. An independent-set pattern is
uniquely determined by its set `F=E(U[C])`: along edges outside F the two
colors alternate, while along F they agree. Since U is a tree, the root
color and F determine every color. Some choices of F are invalid, but there
is at most one valid pattern per F. Hence

\[
 \sum_{\substack{I\text{ blocked}}}q^{e_U(C)}
 \le\sum_{F\subseteq E(U)}q^{|F|}=(1+q)^{2r-1}.
\]

For the second inequality, choose a proper bipartition of U. If its classes
both have size r, choose the orientation with `p in C`. Otherwise put the
larger class into I; then `s>r`. Either choice is unblocked and has `j=0`.
It remains to verify `A_s>=A_r`.

For `s=r+t`, `0<=t<=r-1`, (5) gives

\[
 \frac{A_{r+t}}{A_r}=
 \frac{\binom{r^2-r+1}{t}}{(r+1)^t}\ge1.                       \tag{8}
\]

Here is an elementary check of the inequality. For `t>=1`, put
`B_0=r²-r+1`. We have

\[
 B_0-t+1\ge\frac{(r+1)(t+1)}2,
\]

because the left-minus-right expression is minimized at `t=r-1`, where
twice the difference is `(r-2)(r-3)>=0`. Also
`t!<=((t+1)/2)^t` by AM–GM. These two facts imply
`(B_0)_t >= (r+1)^t t!`. The case `t=0` is equality.

Now (6)–(7) imply

\[
 Z(T,G_r)\ge W_1/r,\qquad
 Z(U,G_r)=W_0+W_1\le\left(1+(1+q)^{2r-1}\right)W_1.
\]

This proves (3), since `(1+q)^{2r-1}<exp(2)<9`. QED.

### Proof of the perfect-matching improvement

Fix a perfect matching M of U. Every feasible I has exactly r vertices and
selects exactly one endpoint of each matching edge. Contract M. The result
is a tree on r vertices.

Fix the choice on the matching edge containing p. At every subsequent
contracted edge, if its parent endpoint belongs to I, the child endpoint is
forced into C, with weight 1. If the parent endpoint belongs to C, the
child endpoint can be in I, with weight 1, or in C, with weight q.
Induction on this contracted tree shows that the partition sum, for either
fixed root choice, is at most `(1+q)^{r-1}`. It is at least 1: the proper
bipartition respecting that root choice contributes weight 1.

All patterns have the same factor `A_r`. The unblocked root choice is
`p in C`; its partition sum is at least 1, whereas the blocked root
choice's sum is at most `(1+q)^{r-1}`. Every unblocked state has factor
`(b-r)/D` in (6). This proves (4), using `(b-r)/D>=1/2` and
`(1+q)^{r-1}<exp(1)<3`. QED.

### Application to the known exponential obstruction

If T is the full subdivision of an r-edge tree H, then deleting **any**
leaf leaves a perfect matching: root H at that leaf, and match every other
original vertex to the subdivision vertex of its parent edge. Consequently
(4) applies at every leaf, including every leaf of the 82-edge subcubic
example where the uniform recurrence fails.

There is also an exact shape-sensitive formula. For
`R=H-ell`, rooted at the original neighbor h of ell, define

\[
 C_v=\prod_{w\text{ child of }v}(q+C_w).
\]

Then

\[
 \frac{Z(T,G_r)}{Z(T-\ell,G_r)}
 =\frac{r^2-r+1}{r(r+1)(1+C_h)}.                              \tag{9}
\]

To check the correspondence, use the displayed matching and identify each
matched pair with its original vertex in R. The unblocked choice at the
root forces every original vertex into I, giving a unique pattern of weight
1. For the blocked choice, h belongs to C. Across a parent–child edge, a
parent original vertex in I forces the child original vertex into I. A
parent in C permits a child in C with weight 1, or a child in I with weight
q. Thus the original vertices in C form precisely a connected set containing
h, with weight q per boundary edge. This gives the recursion above. It
replaces the exponentially large **unweighted** rooted subtree count by a
boundary-weighted partition function.

## 3. The attempted general implication — not proved

Retain the question's full criticality, writing

\[
 2m=(k-1)n+\epsilon,\quad\epsilon\in\{1,2\},\qquad
 2e_G(S)\le(k-1)|S|\quad(S\subsetneq V(G)).
\]

A possible replacement for the disproved uniform recurrence is

\[
 \boxed{2m\,Z(T,G)\ \stackrel{?}{\ge}\ \epsilon Z(T-\ell,G).}    \tag{CW}
\]

This is **not asserted as a theorem**. It would suffice for induction:
the lower-edge Erdős–Sós statement makes `Z(T-ell,G)>0`, and (CW) would
force `Z(T,G)>0`. In the critical split family it follows from (3), since
`2m=r(2r²+r+1)>10r` for `r>=2`; at `r=1` direct calculation gives equality
in (CW).

The actual missing step is a general critical-host bound on the escape
expectation (2), or merely a proof that it is positive. The split proof
works because every independent-set pattern is realizable and its degree
energy factors as **a capacity term times q per monochromatic edge**.
For an arbitrary host, missing cross edges impose additional coherent tree
constraints. No consequence of full induced criticality establishing a
replacement for (5)–(7) was proved. Ordinary Hall conditions, stationary
marginals, and scalar Jensen do not supply it.

### Why (CW) must not silently become an average-density lemma

Even this degree-corrected inequality is false under average density alone.
Take `k=10`, `U=K_(1,9)`, and obtain T by extending one leaf of U by an edge.
Let G be the disjoint union of 100 copies of `K_11` and one `K_(1,50)`.
Then

\[
 n=1151,\quad m=5550,\quad\epsilon=2m-9n=741>0.
\]

Put `A=11!/10^8` and `B=(50)_9/50^8`. Direct evaluation gives

\[
 Z(U,G)=100A+B,\qquad Z(T,G)=10A,
\]

because the star component contains no T. Nevertheless

\[
 2mZ(T,G)-\epsilon Z(U,G)
 =-\frac{3072907492578}{1220703125}<0.
\]

This is **not** a critical-host counterexample: each `K_11` is a proper
strict-density witness. It prevents extending the weighted proposal merely
by replacing its critical hypotheses with average degree.

## 4. Verification

Run

    python3 Submission/DegreeCorrectedMeasureChecks.py --geng

The exact-rational checks passed:

* 298 independent backtracking/subset-DP or split-DP comparisons, 241 direct
  weighted extension identities, and 292 unconditioned hom-weight identities;
* 3,426,430 proper induced-subset types for the critical split hosts;
* 45,149 coefficient checks of (8);
* all 9,339 tree types of orders `3,5,...,15`, covering 67,371 leaf deletions
  and 4,005 perfect-matching strengthened cases;
* (9) for all 200 H-types through ten vertices, covering 965 leaves;
* all 22 leaves of the 82-edge counterexample: the weighted ratios lie
  between 0.285071 and 0.296296, rigorously above `1/8`;
* the exact average-only counterexample above.

Separately, (CW) survived all 677,211 leaf checks on 24,667 critical
host/parameter pairs through nine vertices. **This is finite evidence, not
an unrestricted proof.** The log is `DegreeCorrectedMeasureChecks.log`.
The mathematical proofs above are not Lean formalizations.

`Spec.lean` retains SHA-256
`674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103`.
