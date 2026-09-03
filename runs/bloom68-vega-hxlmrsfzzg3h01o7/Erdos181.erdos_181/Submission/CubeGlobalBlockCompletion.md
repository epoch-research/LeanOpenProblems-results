# Global block completion: the weighted cover inequality was not closed

**No dimension-uniform embedding or Ramsey bound was obtained.** This file
records the exact failed estimate, not a new completion theorem. No `sorry`
or conjectural Lean declaration is used. `Submission/Spec.lean` is unchanged.

## 1. The global cover test used in the attempt

Let `Q_d = Q_r square Q_k`, `b=2^k`, `m=2^(r-1)`, and let `E,O` be the
outer parity classes. For the proposed parameters, `k=floor(d/4)` and
`N>=4096*2^d`. Fix a colour graph `G` and positive vertex weights `w_v`.
Write `omega(g)=product_a w_(g(a))` for an **actual labelled injection**
`g:Q_k -> G`. Let `Omega` be the set of these injections.

An even placement `F=(F_x)_(x in E)` is required to be globally injective
on `E x Q_k`, with all internal edges present. Its weight is
`omega(F)=product_(v in im F) w_v`. For `y in O`, define

\[
 \mathcal C_y(F)=\{g\in\Omega:\operatorname{im}g\cap\operatorname{im}F
 =\varnothing,\quad
 G(F_x(a),g(a))=1\ (x\sim y,\ a\in Q_k)\}.
\]

Disjointness here is from **all** even blocks, not only the neighbours of
`y`. For an original-vertex set `S` outside `im F`, put

\[
 Z_y(F;S)=\sum_{g\in\mathcal C_y(F),\ \operatorname{im}g\cap S=\varnothing}
                         \omega(g).
\]

Call `F` cover-bad, and write `chi(F)=1`, if there exist

\[
 \varnothing\ne I\subseteq O,\qquad
 S\subseteq V(G)\setminus\operatorname{im}F,\qquad
 |S|\le(2b-1)(|I|-1),\qquad
 \sum_{y\in I}Z_y(F;S)=0.                         \tag{1}
\]

This is a **global union-family cover**, not a demand that each star have
`m` disjoint completions. Positivity of the weights makes the last condition
exactly the assertion that `S` hits every actual option at every site in
`I`. A maximal disjoint subfamily of any such union supplies a cover with
at most `b*t` original vertices, where `t` is its size; no conversion of
that fact into a useful weighted estimate was obtained.

The relevant known matching input is Haxell's condition: an `(b+1)`-uniform
hypergraph with one vertex in a job set and `b` resource vertices in each
edge has a job-saturating matching if no nonempty job set `I` has a resource
cover of size at most `(2b-1)(|I|-1)`. Its exact statement was checked in
`/corpus/src/2205.11421/preliminaries.tex`, theorem labelled `haxell`
(citing Haxell, *A condition for matchability in hypergraphs*, 1995).

Apply it to the hyperedges `{y} union im(g)`, `g in C_y(F)`, retaining a
labelled map witnessing each edge. Thus `chi(F)=0` gives pairwise disjoint
odd blocks. Together with `F` these are an injective `Q_d`: every internal
edge is in a block, and every outer edge is tested at the same label `a`.
There are no edges within an outer parity class. This is a use of the
known sufficient condition, **not a newly proved capacity-existence result**.
Condition (1) is not equivalent to absence of an embedding.

## 2. Product-weighted integral DRC, without counting arbitrary covers

For `A subset Omega`, define its actual ordered packing partition

\[
 P_j(A;w)=\sum_{(g_1,\ldots,g_j)\in A^j\atop
                 \operatorname{im}g_i\text{ pairwise disjoint}}
                 \prod_{i=1}^j\omega(g_i).
\]

Use the prescribed auxiliary adjacency

\[
 W(f,g)=1_{\operatorname{im}f\cap\operatorname{im}g=\varnothing}
                  \prod_{a\in Q_k}G(f(a),g(a)).
\]

For two disjoint test roots `u,v`, let
`A(u,v)=N_W(u) intersection N_W(v)`. Consider the total and bad weighted
partitions

\[
 \begin{split}
 \mathcal T_G(w)
 &=\sum_{u,v\in\Omega\atop \operatorname{im}u\cap\operatorname{im}v=\varnothing}
       \omega(u)\omega(v) P_m(A(u,v);w),\\
 \mathcal B_G(w)
 &=\sum_{u,v\in\Omega\atop \operatorname{im}u\cap\operatorname{im}v=\varnothing}
       \omega(u)\omega(v)
       \sum_{F\in\operatorname{Pack}_E(A(u,v))}\omega(F)\chi(F).
 \end{split}                                                   \tag{2}
\]

The roots need not be adjacent to each other. Every configuration counted
in (2) has mutually disjoint root and even-block images, all internal
edges, and every specified root-to-even edge. `chi` is the indicator of
**existence** of a cover certificate; it is not a sum over the
`binomial(N,|S|)` possible covers.

There is an exact change of summation order. With
`C_all(F)=intersection_(x in E) N_W(F_x)`,

\[
 (\mathcal T_G,\mathcal B_G)
 =\sum_{F\in\operatorname{Pack}_E(\Omega)}
       \omega(F)P_2(\mathcal C_{\rm all}(F);w)\,(1,\chi(F)).       \tag{3}
\]

Indeed both sides enumerate the same triples `(u,v,F)`, with exactly the
same original-vertex disjointness and coordinatewise edge tests. In
particular, the integrality requirement has not been replaced by ordinary
powers of a common-neighbourhood cardinality.

## 3. Exact stopping point

A sufficient inequality for this attempted two-colour argument is

\[
 \boxed{\quad
 \mathcal B_R(w_R)+\mathcal B_B(w_B)
       <\mathcal T_R(w_R)+\mathcal T_B(w_B)
 \quad}                                                       \tag{4}
\]

for every colouring on `N>=C*2^d`, with an absolute `C`, and some positive
product weights. Sparse vertex penalties from the established theorem
are allowed, but no boundary-conditioned capacity theorem is assumed.
All summands in `T-B` are nonnegative. Strictness in (4) would select an
actual even placement with no cover (1) in one colour; Haxell would then
supply the full injective cube with **all** outer edges.

**I did not prove (4), even with no requested quantitative margin.** In
particular, I did not prove positivity of the required integral DRC
partition from the established scalar auxiliary density, nor bound its
cover-bad portion strictly below it. This DRC scheme is a sufficient
strengthening, not an equivalent Farkas reformulation of the conjecture.

The attempted use of the existing product weights stops precisely at
`Z_y(F;S)`: deleting `S` leaves different domains

\[
 L_a=(V\setminus(\operatorname{im}F\cup S))
               \cap\bigcap_{x\sim y}N_G(F_x(a)).
\]

The proved residual lower bound for `I_k(G-S,w)` is not a lower bound for
this coordinate-restricted partition. Also `P_m(A;w)` in (2) cannot be
lower-bounded by substituting `(sum_(g in A) omega(g))^m`: that expression
includes overlapping blocks. Thus `B q^r >= 2^(d*2^k/64)` does not establish
(4). No simultaneous-colour estimate removing these two restrictions was
found. No counterexample to (4) in the requested size range has been
established either.

## 4. Small exact audit and integrity

Run `python3 -u Submission/check_cube_global_block_completion.py`.
Output is saved in `Submission/CubeGlobalBlockCompletionVerification.txt`.
The script checks (3), coordinate-domain partitions after every residual
deletion, genuine original-vertex covers, and fully injective lifts with
all `d*2^(d-1)` edges. It includes noncomplete hosts and complementary
colour graphs; its small cases are not in the asymptotic parameter range.
All checks passed: **9 host/blocking cases, 12,912 integral even placements,
and 724,992 exact coordinate-domain partition checks**. The script also
checks that cover-bad need not mean unembeddable. These audits do not test
or establish (4) at a constant-linear Ramsey scale. The pre-existing
`check_cube_higher_block_capacity.py` audit was rerun and also passed.

Unchanged `Submission/Spec.lean` SHA-256:

```text
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```

**Outcome: no completing theorem; (4) remains unproved.**
