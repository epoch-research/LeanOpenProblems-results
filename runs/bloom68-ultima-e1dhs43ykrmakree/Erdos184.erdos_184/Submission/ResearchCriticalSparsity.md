# Critical sparsity: graphic dimension accounting and the remaining gap

## Status

**The sharp critical sparsity inequality is neither proved nor refuted here.**
No inequality `beta(F) <= a c(F) + b |V(F)|` with universal `a<3` and fixed `b`
is established. Consequently this investigation gives **no universal linear
Erdős–Gallai bound**, and no genuine critical counterexample to the proposed
route. `Spec.lean` is unchanged.

The completed, paper-level results are:

1. The sharp sparsity defect has an exact separator calculus. A counterexample
   can be reduced to a loopless, minimum-degree-four, 4-edge-connected,
   2.5-connected critical core, of cost at least four, with
   `Delta <= 2q-2`. The degree-saturated case satisfies the proposed sparsity
   inequality by a direct forest argument, without assuming fixed count.
2. There are exact graphic formulas for the cycle-space dimension lost by
   deleting a cycle and by subsequently extracting a genuinely critical
   restriction. They identify two separate charges: **attachments of the
   deleted cycle**, and **dimension discarded during critical extraction**.
   Criticality controls the costs, but the needed combined rank charge is
   not bounded here.
3. A self-contained nonlinear bound does follow:
   \[
       \boxed{\beta(F)<64q^2\log_2(2q)}.                 \tag{0.1}
   \]
   The constant is deliberately unoptimized. This is a finite-core bound,
   **not** a bound of the requested form and not a reason to undertake an
   exhaustive cost-four search.
4. Targeted exact checks distinguish the accounting issues. In a natural
   genuinely critical graphic bundle chain, deleting one cycle can lose
   arbitrarily many units of `beta`; the component correction repairs this
   exactly. In the **already supplied, noncritical** graph `S`, all cycle
   complements have cost three, but every such complement has hereditary
   cost at least four. A cost-three critical anchor can be ten dimension-
   potential units below `S`. Thus the single-cycle shortcut still cannot
   supply the missing estimate.

Only this note and the root-level **`ResearchCriticalSparsityCheck.py`** were
created. No all-critical-fixed-count theorem is assumed or claimed. The
nonlinear bound and accounting arguments do not use such a theorem.

---

## 1. Definitions, and why the requested inequality would suffice

Cycles are vertex-simple. Auxiliary loopless multigraph cores retain edge
identities, and two parallel edges form a core cycle. Subdivision converts
these to actual simple graphs.

For an even edge set `W`, `c(W)` is its minimum number of cycles in an edge
partition. For any graph `X`, whether even or not, put

\[
 Q(X)=\max\{c(W):W\subseteq E(X),\ W\text{ even}\}.
\]

A nonempty even graph `F` is **q-critical** if `c(F)=q` and every proper even
edge restriction has cost less than `q`. Properness is about edge support;
removing an isolated vertex does not make a restriction proper.

Write `n_+(X)` for the number of nonisolated vertices and `k(X)=kappa_e(X)`
for the number of edge-containing components. Then

\[
 \beta(X)=m(X)-n_+(X)+k(X)=m(X)-n(X)+\kappa(X),\qquad
 \sigma(X)=\beta(X)+k(X).                              \tag{1.1}
\]

Both are insensitive to isolated vertices. The sharp target is

\[
             \sigma(F)\le 2q.                         \tag{S}
\]

For any nonempty even simple `G`, choose a minimum-edge restriction attaining
`Q(G)`. It is genuinely `q`-critical, where `q=Q(G)>=c(G)`. A minimum partition
of this **simple** restriction uses at least `3q` edges. Thus (S) would give

\[
 3q-n_+(F)+k(F)\le\beta(F)\le2q-k(F),
 \quad q\le n_+(F)-2k(F)\le n(G).                     \tag{1.2}
\]

For a connected nonempty critical graph this is `q<=n_+(F)-2`. No Hajós or
fixed-count conclusion is needed for this implication.

More generally, if `beta(F)<=a q+b n_+(F)` universally on critical simple
graphs, with `a<3`, we may increase `b` to be nonnegative. Then

\[
 c(G)\le Q(G)\le \frac{b+1}{3-a}\,n(G).               \tag{1.3}
\]

The edge lower bound is applied to the critical **simple restriction**, not
to a suppressed parallel-edge core, where two-edge cycles are permitted.

---

## 2. The defect survives the genuine critical reductions

For a connected nonempty graph set

\[
           D(F)=\beta(F)-2c(F)+1.
\]

The all-restriction separator lemmas in `ResearchCriticalGraphic.md`, §5,
apply. They concern actual even restrictions, not merely selected partitions:

* At a disjoint or articulation sum, costs add, and criticality holds exactly
  when it holds on the nonempty pieces.
* A two-edge splice deletes one marked edge in each of two disjoint even
  graphs and adds the two cross connectors.
* A vertex-edge splice deletes marked edges `u_i v_i`, identifies the two
  `v_i`, and adds `u_1u_2`.
* In either splice `c=c_1+c_2-1`, and the whole graph is critical exactly
  when both capped pieces are critical.
* Subdivision/suppression of degree-two paths preserves the entire poset of
  even restrictions, its cycle partitions, and criticality.

For clarity, the splice criticality assertion uses both marked states. An
inactive restriction has two even traces avoiding the marks. An active
restriction caps to two even traces containing the marks, with cost the sum
of their costs minus one. These two states account for **every** even
restriction. This is why a partition-only splice argument would be inadequate.

Counting edges and vertices gives the following additional rank account for
connected pieces:

| Operation | `beta` of the result | `c` of the result | `D` of the result |
|---|---:|---:|---:|
| articulation sum | `beta_1+beta_2` | `q_1+q_2` | `D_1+D_2-1` |
| two-edge splice | `beta_1+beta_2-1` | `q_1+q_2-1` | `D_1+D_2` |
| vertex-edge splice | `beta_1+beta_2-1` | `q_1+q_2-1` | `D_1+D_2` |
| subdivision | unchanged | unchanged | unchanged |

For disjoint unions, `sigma-2c` adds. Hence a positive defect in a critical
graph forces a positive defect in a critical piece of any of these
nontrivial separations. At an articulation this is even stronger: the extra
minus one cannot create a positive defect from nonpositive pieces.

An even `2q`-edge parallel bundle has `beta=2q-1`. The fixed-count
Heinrich–Streicher construction, arXiv:1708.09141, therefore implies (S) on
its fixed-count class by this table. We use the supplied cost-at-most-three
critical theorem from `ResearchCriticalStructure.md` only to conclude that
**a sparsity counterexample has critical cost at least four**. Its cost-three
part remains a previously supplied computer-assisted theorem, not a new
paper-only classification here.

### A direct graphic case: degree saturation

Every partition gives `d_F(v)<=2q`. If a critical graph has `d_F(v)=2q`, every
cycle contains `v`: otherwise deleting a cycle avoiding `v` leaves a proper
even restriction whose degree at `v` still forces cost at least `q`.

For connected `F`, it follows that `F-v` is a forest. If that forest has `t`
components, including its isolated vertices, then

\[
 \beta(F)=d_F(v)-t=2q-t\le2q-1.                       \tag{2.1}
\]

Here `t>=1` in a nonempty loopless graph. This proves the proposed bound in
the saturated case directly, without invoking fixed-count classification.

Consequently the standard minimal-counterexample reduction, now applied to
`D` rather than to a fractional gap, leaves only critical cores with

\[
 q\ge4,\qquad 4\le\delta(F)\le\Delta(F)\le2q-2,       \tag{2.2}
\]

no articulation, no two-edge cut, and no separating vertex-edge pair. The
last condition is the 2.5-connectivity condition used in the earlier note.
Loops would be separate cycle blocks, and series-only pieces are removed by
suppression. These are **reductions**, not a proof that the remaining atoms
are absent or sparse. In particular, the aim here is not to exclude all
non-fixed atoms.

---

## 3. Exact graphic cycle-space accounting

### 3.1 Two complementary even restrictions

Let `H` be an even restriction of `F`, and put `B=F\H`. Form a bipartite
multigraph `I(H,B)`:

* its nodes are the edge-containing components of `H` and of `B`;
* for each vertex belonging to both supports, put an edge between its two
  component nodes;
* component nodes with no such shared vertex are retained as isolated nodes.

If `t=|V_+(H) intersect V_+(B)|`, the component count of this incidence graph
is `k(F)`. Therefore

\[
 \boxed{\beta(F)=\beta(H)+\beta(B)+\beta(I(H,B)),}
 \qquad
 \beta(I(H,B))=t-k(H)-k(B)+k(F).                       \tag{3.1}
\]

**Proof.** Connectivity in the union is precisely connectivity through the
shared vertices between the two kinds of components. Now use
`n_+(F)=n_+(H)+n_+(B)-t` and add the edge counts. This also handles a missing
side or disconnected supports. ∎

Thus there is a real extra **attachment-cycle dimension**, in addition to
the intrinsic cycle dimension of the discarded even edge set. It is not
legitimate to count only the cycles explicitly deleted from a partition.

### 3.2 Deleting one cycle

Let `C` be any cycle of an even graph `F`, set `R=F-E(C)`, and define

\[
 b_C=|\{v\in V(C):d_F(v)\ge4\}|.
\]

These are the branch vertices of `C` in the **current** graph. Exactly the
other vertices of `C` become isolated upon deletion. Hence

\[
 \boxed{\begin{aligned}
 \beta(F)-\beta(R)&=b_C+k(F)-k(R),\\
 \sigma(F)-\sigma(R)&=b_C+2\bigl(k(F)-k(R)\bigr).
 \end{aligned}}                                      \tag{3.2}
\]

For connected non-cycle `F` this reads

\[
        \sigma(F)-\sigma(R)=b_C+2-2k(R).              \tag{3.3}
\]

Subdivision changes the length of a cycle but not `b_C`. Thus the relevant
ear charge is the number of branch attachments, together with the change
in edge-containing components, **not** the length of the subdivided cycle.

An ordinary open ear is not itself an even restriction: its two ends have
odd degree in the ear. Criticality cannot be applied to intermediate open-ear
graphs without an additional parity-state argument. Pairing ears restores
parity but does not bound the attachment dimension in (3.1).

---

## 4. The exact critical-extraction gap

Suppose now that `F` is genuinely `q`-critical and `q>=2`. For every cycle
`C`, with `R=F-E(C)`, one has the stronger statement

\[
                    c(R)=Q(R)=q-1.                  \tag{4.1}
\]

Indeed, `c(R)<=q-1` by criticality, and a smaller value would give a partition
of `F` with fewer than `q` cycles. Every even restriction of `R` is proper
in `F`, proving the bound on `Q(R)` as well.

Choose a minimum-edge restriction `H subseteq R` attaining this value.
Then `H` is genuinely `(q-1)`-critical. **It need not have been shown to equal
`R`.** Define the extraction charge

\[
             T(R,H)=\sigma(R)-\sigma(H).             \tag{4.2}
\]

The charge is not automatically zero. Monotonicity of `beta` alone does
not assign it a sign: the component term can increase under restriction.
No sign theorem for these critical-extraction pairs is being assumed.
Combining (3.2) with (4.2) gives the exact identity

\[
\begin{aligned}
 \sigma(F)-2q
   &=\sigma(H)-2(q-1)+\eta(C,H),\\
 \eta(C,H)
   &=b_C+2\bigl(k(F)-k(R)\bigr)-2+T(R,H).
\end{aligned}                                        \tag{4.3}
\]

For connected `F`,

\[
                   \eta(C,H)=b_C-2k(R)+T(R,H).        \tag{4.4}
\]

Under an inductive bound for `H`, put
`slack(H)=2(q-1)-sigma(H)>=0`. The precise missing estimate is

\[
          b_C-2k(R)+T(R,H)\le \operatorname{slack}(H) \tag{4.5}
\]

for a suitable cycle and extracted anchor, or a valid amortized substitute
along successive critical extractions. No such estimate is proved here.
The condition with zero on the right would be sufficient but stronger than
needed; **it is not being asserted as a universal critical-extension lemma**.
Equation (4.5) is an accounting statement identifying what an induction would
have to establish, not a repackaged proof of sparsity.

Equivalently, for `B=F\H`, (3.1) says that the rank charge to be controlled is

\[
 \beta(B)+\beta(I(H,B))
       \le k(H)+1+\operatorname{slack}(H)             \tag{4.6}
\]

when `F` is connected. Neither the number of ears nor the number of removed
cycles alone controls the left side.

### Why the tempting absorption step does not repair this

If `H` is proper in `R`, then `H union C` is proper in `F`, so criticality
only gives `c(H union C)<=q-1`. This does **not** imply
`c(R union C)<=q-1`, even though `H` and `R` have the same minimum cost.
Restoring the omitted even edge set may require complete reoptimization.

In particular, the argument cannot say “extract a cheaper critical core,
absorb the removed cycle there, and restore the rest.” That would be a
monotone-absorption assertion not provided by (4.1). Nor can it induct on `R`
as though (4.1) made `R` critical: (4.1) allows proper restrictions of `R` to
have cost exactly `q-1`.

A general estimate `Q(X)>=beta(X)/2` is unavailable. For example, in `K9`,
`beta=28`, whereas every even restriction has a partition with at most
`36/3=12` cycles, so `Q(K9)<=12<14`. Dimension control must therefore use the
special minimal support, rather than apply a rank-to-`Q` inequality to an
arbitrary remainder. The binary and regular nongraphic obstructions supplied
in the task likewise rule out treating (4.5) as a generic code/TU fact.

---

## 5. Boundary controls: what is and is not a counterexample

### 5.1 A genuinely critical graphic family: raw rank loss is unbounded

For `t>=2`, take vertices `u_i,v_i` cyclically indexed by `i`. Put three
parallel edges between each `u_i,v_i`, and one connector from `v_i` to
`u_(i+1)`. This is an iterated two-edge splice of four-parallel-edge cores.
It has

\[
             n=2t,\quad m=4t,\quad\beta=2t+1.
\]

Every cycle is either a parallel pair in one bundle or a global cycle using
all connectors and one edge of each bundle. Every partition must have
exactly one global cycle, followed by one parallel-pair cycle per bundle.
Thus every partition has `q=t+1` cycles. This **proves** genuine criticality:
a partition of a proper even restriction together with a nonempty partition
of its complement has exactly `q` members.

Deleting a global cycle leaves `t` edge-containing cycle components. Hence

\[
 \beta(F)-\beta(R)=t+1,\qquad
 \sigma(F)-\sigma(R)=2.                              \tag{5.1}
\]

Deleting a bundle-pair cycle also drops `sigma` by exactly two. This is a
counterexample only to the naive claim that **raw** rank loss is always at
most two. It is **not** a counterexample to (S); it attains equality in (S).

Keep one edge of each triple bundle and subdivide each of the other two
once. The resulting graph is simple, has `n=4t,m=6t`, and preserves all these
costs, ranks, component counts, and criticality statements. Thus (5.1) is
not merely a parallel-edge phenomenon. The checker verifies the full
restriction bijection for `t=2,3,4,5`; the family proof is not based on that
finite check.

### 5.2 The supplied S: single-cycle costs miss the extraction charge

Use exactly the simple graph `S` from `ResearchCriticalGraphic.md`:

* start with doubled pairs
  `03,04,05,13,15,16,24,25,26`;
* for the `j`th pair `uv`, replace one copy by `u-(7+j)-v`;
* retain the triangle `34,36,46`.

It has `n=16,m=30,beta=15,sigma=16`. The new checker independently audits
all 32,768 even restrictions and all 1,058 simple cycles. It confirms

\[
 c(S)=4,\quad \nu(S)=10,\quad Q(S)=6,\quad
 c(S-E(C))=3\quad\text{for every cycle }C.
\]

The new rank-accounting diagnostics are:

| `Q(S-E(C))` | Number of cycles `C` |
|---:|---:|
| 4 | 640 |
| 5 | 384 |
| 6 | 34 |

So **none** of these cost-three remainders has hereditary cost three.
Among all restrictions of `S`, there are 5,637 genuinely 3-critical anchors;
each is tested over all its proper even restrictions. They satisfy

\[
 \max_H\sigma(H)=6,\qquad
 \min_H\bigl(\sigma(S)-\sigma(H)\bigr)=10.            \tag{5.2}
\]

For an explicit maximizing anchor, take the three vertex-disjoint triangles
arising from pairs `05,13,24`. It has `beta=3,k=3`. The triangle on `3,4,6`
is edge-disjoint from it, and their union is a proper even restriction of
cost four. Thus it also gives a direct all-restriction obstruction to
criticality of `S`.

**Scope:** `S` is not q-critical and does not refute the proposed critical
sparsity inequality, or any assertion confined to genuine critical graphs.
It refutes using only the single-cycle cost equalities to obtain the needed
rank control. In particular, it is not a counterexample to the still
unproved assertion that a genuine critical graph's cycle complement might
itself be critical.

---

## 6. A nonlinear graphic rank bound that can actually be proved

The following bound gives a theoretical limit on reduced core size without
presuming fixed count or undertaking a search. It also quantifies how far
the available packing argument falls short of (S).

### Lemma 6.1 — a cycle with a logarithmic rank-deletion charge

Let `X` be a finite graph of maximum degree at most `D`, where `D>=3`, and
let `b=beta(X)>=1`. Set

\[
             L(b)=2\lceil\log_2(2b)\rceil+2.
\]

There exists a simple cycle `C` such that

\[
       \beta(X)-\beta(X-V(C))\le1+(D-2)L(b).          \tag{6.1}
\]

Auxiliary loops and parallel edges arising from suppression are allowed in
the proof; the lifted cycle is an actual cycle of `X`.

**Proof.** Delete leaves and forest components. These operations preserve
cycle rank. If a component of the resulting 2-core is a cycle, choose it;
its deletion costs exactly one unit of cycle rank, including any trees
originally attached to it.

Otherwise choose a component with a branch vertex and suppress its
maximal degree-two paths. Its connected core `J` has minimum degree at
least three and maximum degree at most `D`. Suppression can create loops
or parallel edges. If `s=|V(J)|`, the degree sum gives

\[
 s\le 2(\beta(J)-1)\le2b-2.                           \tag{6.2}
\]

A loop or parallel pair is already a cycle of length at most two. If `J`
is simple, a radius-`r` breadth-first tree in a graph of minimum degree
three has at least `1+3(2^r-1)` vertices when there is no cycle of length at
most `2r+1`. Taking `r=ceil(log_2(2b))` contradicts (6.2). Thus in all cases
there is a core cycle of length `g<=L(b)`.

Deleting its `g` vertices removes at most `Dg-g` edges: at least its own
`g` edges were counted twice in the degree sum. The component count of
what remains is nonnegative, so

\[
 \beta(J)-\beta(J-V(C_J))\le (Dg-g)-g+1
                              =g(D-2)+1.             \tag{6.3}
\]

Lift the core cycle through the suppressed paths. A path not selected by
the cycle but incident with a deleted core vertex leaves at most dangling
path fragments; these contribute no cycle dimension. Pruned trees also
contribute no dimension. Hence the rank difference in the original
component is the same as that in (6.3). Other components are unaffected.
This proves (6.1). ∎

### Proposition 6.2 — all-size, but nonlinear, critical sparsity

Every nonempty q-critical loopless even graph satisfies (0.1).

**Proof.** First let `F` be connected and `q>=2`. It cannot contain `q`
vertex-disjoint cycles: their union would be a disconnected, hence proper,
even restriction of cost exactly `q`. Thus every vertex-disjoint cycle
packing has size at most `q-1`. Also `Delta(F)<=2q` by a minimum partition.

Repeatedly use Lemma 6.1 in the remaining vertex-deleted graph until it is a
forest. The selected cycles are vertex-disjoint in the original graph, so
there are `r<=q-1` of them. Maximum degree never increases and cycle rank
never exceeds the initial value `b`. Summing the rank losses yields

\[
 \boxed{b\le(q-1)\bigl[1+(2q-2)L(b)\bigr].}           \tag{6.4}
\]

On a nonsaturated critical core, `2q-2` inside the brackets may be replaced
by `2q-4`, using (2.2). No criticality of any intermediate vertex-deleted
graph is assumed.

Since `L(b)<=2 log_2 b+6`, (6.4) implies

\[
                  b\le q^2(4\log_2 b+13).            \tag{6.5}
\]

To make the bound explicit, put `h=log_2(2q)>=1` and `B=64q^2h`. Then

\[
 4\log_2 B+13=29+8h+4\log_2 h\le41h<64h.
\]

The function `x/(4 log_2 x+13)` is strictly increasing on `x>=1`; its
derivative has positive numerator `4 log_2 x+13-4/ln 2`. Thus (6.5) forces
`b<B`, proving (0.1). The connected case `q=1` is a single cycle and is
immediate.

For disconnected `F`, criticality passes to its components. Write their
costs as `q_i`, summing to `q`, and add the bounds, using
`sum q_i^2<=q^2` and `log_2(2q_i)<=log_2(2q)`. ∎

For a connected suppressed core of minimum degree four,

\[
                   n_{\rm core}\le\beta(F)-1,
 \qquad m_{\rm core}\le2\beta(F)-2.                  \tag{6.6}
\]

Thus this proves a finite bound on core size for each fixed critical cost.
It neither classifies the cores nor shows their rank is at most `2q-1`.
The argument uses only two consequences of criticality — the degree bound
and exclusion of `q` vertex-disjoint cycles — and has not used the full
strength of (4.1) to reduce its quadratic-logarithmic scale to a linear one.

Substituting (0.1) into `3q-n_+(F)+k(F)<=beta(F)` imposes no useful upper
bound on `q/n_+(F)`. In particular **(0.1) does not establish EG**, nor an
inequality with coefficient `a<3` of the kind requested.

---

## 7. Reproduction, verification, and exact stopping point

Run from the project root:

```sh
PYTHONHASHSEED=0 python3 -B ResearchCriticalSparsityCheck.py
```

The checker uses only the standard library and writes no files. It does not
import old checkers or generate a catalog of cost-four candidates. Its
bounded fixtures are:

* empty and isolated-vertex controls;
* a cycle, a figure eight, disjoint cycles, and the basic bundle/splice
  controls;
* the cores and simple lifts of the explicit family in §5.1 for `2<=t<=5`;
* exactly the previously supplied graph `S`.

For each input, it enumerates the complete binary incidence kernel and
checks its dimension against `m-n_++kappa_e`. Simple-cycle DFS is independently
compared with the connected nonempty 2-regular words in that full kernel.
Exact minimum and maximum partition DPs are reconstructed on **every** even
word. Hereditary `Q` uses all deletable cycles, not just cycles through the
first edge. Every reported critical word receives an additional direct
all-subrestriction audit by enumerating its own incidence kernel.

The component-incidence identity (3.1) is checked on every complementary
pair of even words in each input; the cycle-deletion identity (3.2) is
checked for every input cycle. Subdivision bijections and the diagnoses in
§5 are checked exactly. Finite checks support the explicit controls and
accounting formulas; the proof of the asymptotic bound is §6, not an
extrapolation from these inputs. In total there are **17 bounded inputs and
38,355 even-word audits**, counting core/lift presentations separately.

**Verification completed:** syntax parsing passed, and complete runs with
`PYTHONHASHSEED=0` and `17` both ended with `ALL EXACT CHECKS PASSED`. Their
stdout was byte-identical, with SHA-256

```
dc173b0a76c63b6a9ec6bc97d6d49dedefb3c799c97ce96920c6446686554c1e
```

These are paper proofs and exact finite checks, not Lean formalizations or
literature-priority claims.

The pre-work fingerprint protects all **247 existing non-cache project
files outside `.lake` and `.git`**, excluding the two permitted new files:

```
c77214a70863969fd5e180303d9f8ecbf31e4141b4502c003583c7cb5b30d9c3
```

The unchanged specification SHA-256 is

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

Both are checked before and after execution. No specification or existing
research file is edited.

**Exact stopping point.** After the legitimate separator reductions, a
sharp sparsity argument still needs to control the combined attachment and
critical-extraction charge (4.5), or replace it by another graphic estimate
strong enough to give `beta<=a q+b n` with `a<3`. The proved logarithmic
cycle-rank deletion bound does not do this. There is no established estimate
for the required charge on the remaining genuine critical atoms, and no
certified genuine critical atom violating (S). The proposed weaker
structural route remains open in this investigation.
