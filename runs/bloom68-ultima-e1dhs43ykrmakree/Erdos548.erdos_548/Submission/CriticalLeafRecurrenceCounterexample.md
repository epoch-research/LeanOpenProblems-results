# Candidate C is false, including its existential-leaf version

**Outcome.** The critical counting inequality

\[
 n I(T,G)\geq \epsilon I(T-\ell,G)
\]

is false. It can fail **for every leaf of the same tree**, even in an
actual critical host and with `Delta(T)=3`. Thus neither selecting another
leaf nor a global injection into `Emb(T,G) x V(G)` can establish this
particular recurrence. The counterexamples also preclude any repair using
only a fixed polynomial number of output tags.

This is **not** an Erdős–Sós counterexample or a complete Erdős–Sós proof.
All displayed trees have explicit embeddings in their displayed hosts.
A genuinely weaker, positivity-only transport argument remains unresolved.
No Lean specification was changed.

Throughout, `I` counts labelled injective homomorphisms, not induced copies,
and `(b)_j` is the falling factorial.

## 1. A family of actual critical hosts

For an integer `a>=1`, set

\[
 k=2a,\qquad b=a^2+1,\qquad n=a+b=a^2+a+1.
\]

Let `G_a` be the join of a clique `A` of order `a` and an independent set
`B` of order `b`. Thus every cross edge is present. Its degrees are `n-1`
on `A` and `a` on `B`, and

\[
 2e(G_a)=a(a-1)+2ab=(2a-1)n+1.
\]

Consequently `epsilon=1`. The host is nonbipartite when `a>=2`.

For an arbitrary induced vertex set `S`, put `x=|S intersect A|` and
`y=|S intersect B|`. Its doubled surplus is exactly

\[
 2e(S)-(2a-1)|S|=x(x-2a)+(2x-2a+1)y.                 \tag{1}
\]

If `x<=a-1`, both terms on the right are nonpositive. If `x=a` and `S` is
proper, then `y<=a^2` and the expression is `y-a^2<=0`. This verifies
**every** proper-set inequality required in Candidate C. In particular,
`G_a` is a minimum-cardinality strict-density witness, not merely an
edge-minimal graph.

## 2. An exact identity for subdivisions

Let `H` be any tree with `a` edges. Subdivide every edge once, obtaining a
`2a`-edge tree `T`. Call the original `a+1` vertices the original class and
the `a` new vertices the subdivision class.

For a leaf `ell` of `H` (also a leaf of `T`), define

\[
 R_H(\ell)=|\{W\subseteq V(H):\ell\in W,\ H[W]\text{ is connected}\}|.
\]

The singleton `{ell}` is included. Then

\[
 \boxed{I(T,G_a)=a!(b)_{a+1}},\qquad
 \boxed{I(T-\ell,G_a)=R_H(\ell)\,a!(b)_a}.           \tag{2}
\]

### Full-tree count

In any embedding, the preimage of `B` is an independent set of `T` and has
at least `a+1` vertices. The original class is the **unique** independent
set of size `a+1`.

Indeed, if an independent set uses the subdivision vertices corresponding
to a nonempty edge set `F` of `H`, it cannot use any original vertex in
`V(F)`. If `F` has `c>=1` edge-containing components, then
`|V(F)|=|F|+c`, so that independent set has size at most

\[
 |F|+(a+1-|V(F)|)=a+1-c\leq a.
\]

Thus all original vertices must map to `B` and all subdivision vertices to
`A`. Every such injection is valid, giving the first formula in (2).

### Leaf-deleted count

Put `U=T-ell`. Its independent sets have size at most `a`. For a nonempty
set `F` of subdivision vertices, the same calculation now gives the bound

\[
 |F|+a-|V(F)\setminus\{\ell\}|
    =a-c(F)+\mathbf 1_{\ell\in V(F)}\leq a.        \tag{3}
\]

To reach size `a`, either:

* `F` is empty, and all remaining original vertices are used; or
* `F` is connected and contains `ell` in its original-vertex support, and
  all original vertices not incident with `F` are used.

These possibilities are in bijection with the connected vertex sets of
`H` containing `ell`: the empty `F` corresponds to `{ell}`. Since the
host clique has only `a` vertices, the preimage of `B` in any embedding of
`U` must be one of these size-`a` independent sets. Each contributes exactly
`a!(b)_a` embeddings. This proves the second formula in (2).

### The exact extension mechanism

Let `p` be the parent of the deleted leaf; it is a subdivision vertex.
Of the `R_H(ell)` independent-set patterns in the preceding count, exactly
one maps `p` into `A`: the pattern with `F` empty. It supplies exactly

\[
 a!(b)_a
\]

partial embeddings, each with `b-a=n-k` extensions. In every other pattern,
the connected edge set `F` contains the unique edge incident with `ell`,
so `p` maps into `B`. All `a` vertices of `A` are occupied, and those
partial embeddings have **zero** extensions.

This independently explains the ratio

\[
 \frac{I(T,G_a)}{I(T-\ell,G_a)}
       =\frac{b-a}{R_H(\ell)}.                    \tag{4}
\]

There is no claim that a stationary marginal is available; the exact good
root-class probability is `1/R_H(ell)`.

## 3. A 36-edge counterexample with equivalent leaves

Take `a=18` and `H=K_(1,18)`. Then `T` is the once-subdivided 18-star,
with `k=36`, and `Delta(T)=18=floor(k/2)`. For every leaf,

\[
 R_H(\ell)=1+2^{17}=131073.
\]

The host has

\[
 b=325,\quad n=343,\quad e(G)=6003,\quad\epsilon=1.
\]

But

\[
 n\frac{I(T,G)}{I(T-\ell,G)}
     =\frac{343\cdot307}{131073}
     =\frac{105301}{131073}<1.                     \tag{5}
\]

All leaves are equivalent, so the existential-leaf version of C also fails.

## 4. Failure for every leaf with maximum degree three

Let `H_h`, `h>=2`, have a path `v_1,...,v_h`, two extra leaves at each
endpoint, and one extra leaf at each internal path vertex. It has

\[
 a=2h+1\text{ edges},\qquad h+2\text{ leaves},\qquad\Delta(H_h)=3.
\]

Let `T_h` be its full subdivision. Thus

\[
 e(T_h)=4h+2,\qquad\Delta(T_h)=3.
\]

Every leaf-parent in `T_h` has degree two and belongs to the smaller color
class (the subdivision class). Choosing a leaf whose parent lies in that
class therefore cannot avoid this example.

The number of rooted connected vertex sets in a tree obeys

\[
 f(v)=\prod_{w\text{ child of }v}(1+f(w)).
\]

For a leaf attached to an endpoint of the spine, this gives

\[
 R_{H_h}(\ell)=3\cdot2^h-1.                        \tag{6}
\]

For a leaf attached at `v_i`, `2<=i<=h-1`, it gives

\[
 R_{H_h}(\ell)
   =1+(6\cdot2^{i-2}-1)(6\cdot2^{h-i-1}-1)
   \geq3\cdot2^h-1.                               \tag{7}
\]

For completeness, put `P=2^(h-3)`. The difference between the expression
in (7) and (6) is
`12P-6(2^(i-2)+2^(h-i-1))+3`. Since the two exponents sum to `h-3`,
their powers sum to at most `P+1`; the difference is at least `6P-3>0`.
There are no internal spine leaves when `h=2`.

Choose `h=20`. Then

\[
 a=41,\ b=1682,\ k=82,\ n=1723,\ e(G)=69782,
 \quad\epsilon=1,\quad\Delta(T)=3.
\]

For every one of the 22 leaves,

\[
 R_H(\ell)\geq3145727
     >2827443
     =1723\cdot1641
     =n(b-a).                                    \tag{8}
\]

Equations (2)--(4) prove the strict reverse of C for **every leaf**.
This is a bounded-degree, nonspider target well inside the case left open
by the high-maximum-degree CL corollary.

## 5. Implications and scope

1. The map `Emb(T-ell,G) -> Emb(T,G) x V(G)` cannot be injective in these
   examples: its proposed source has strictly larger cardinality than its
   target. This is a global cardinality obstruction, not a failure of a
   particular local move or root choice.
2. Since every leaf fails, selecting a different final deletion or taking a
   nonzero nonnegative weighted average of these inequalities cannot help.
   In the subcubic example all leaf-parent `deg_T-1` weights equal one.
3. A fixed polynomial number of output tags also cannot repair uniform
   counting in this family. For `T_h`, `n=Theta(h^2)` but (4), (6), and (7)
   give, for **every leaf**,

   \[
   I(T_h,G)/I(T_h-\ell,G)
       \leq\frac{a^2-a+1}{3\cdot2^h-1}.
   \]

   Multiplication by `n^d` tends to zero for every fixed `d`. Hence even
   `Emb(T-ell,G) -> Emb(T,G) x V(G)^d` is eventually impossible.
4. These are **not** Erdős–Sós counterexamples. An explicit full embedding
   maps the original vertices of `H` to distinct vertices of `B` and the
   subdivision vertices to distinct vertices of `A`.
5. The `epsilon=1` instances are legitimate critical cores from the question.
   The literal `+1` edge hypothesis in `Spec.lean` is not an escape: the
   disjoint union of two copies of `G_a` has exactly `(k-1)|V|/2+1` edges,
   and each component is a strict-density critical core of this form.
6. Biasing toward only the single extendible pattern succeeds *in this host*,
   but is not a proved general selection theorem. No positivity-only
   recurrence for arbitrary critical hosts, and no unrestricted ES proof,
   follows from this calculation.

## 6. Verification

Run

    python3 Submission/CriticalLeafRecurrenceChecks.py

All checks pass. The script independently uses an include/exclude
independent-set polynomial DP, explicit injective backtracking, connected
subset enumeration, and direct host constructions. The audits include:

* 3,426,430 exact proper induced-subset types for `a=1,...,60`;
* the subdivision identities for all 200 tree types `H` through ten
  vertices, covering 965 leaf deletions;
* 140,228 independently enumerated nonempty vertex subsets for the rooted
  connected-subtree counts;
* 13 direct embedding-count comparisons and 85 rooted extension checks;
* 1,947 checks of the caterpillar formulas;
* all leaves of the 36-edge and 82-edge counterexamples, using arbitrary
  precision integers, and explicit valid full embeddings;
* an additional leaf-transitive subcubic example: `k=90`, `a=45`, `n=2071`,
  `e(G)=92160`, and `R_H(ell)=119165813>4102651=n(b-a)` at all 24 leaves.

Results and log:

* `/tmp/es_leaf_transport/verified_counterexamples.json`
* `/tmp/es_leaf_transport/verified_counterexamples.log`

`Spec.lean` remains unchanged, SHA-256
`674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103`.

**Conclusion:** Candidate C and its same-factor existential-leaf weakening
are disproved. Unrestricted Erdős–Sós is not completed here. In particular,
the surviving positivity-only task must not be represented as if this
uniform counting recurrence had been established.
