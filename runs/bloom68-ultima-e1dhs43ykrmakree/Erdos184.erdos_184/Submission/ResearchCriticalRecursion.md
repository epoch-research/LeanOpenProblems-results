# Critical cycle-complement recursion: a focused attempt and a longest-cycle obstruction

## Outcome — the requested recursion remains unresolved

**I have neither proved nor refuted the universal cycle-complement recursion.**
No genuinely critical counterexample to it is supplied. The related conditional
fixed-count induction also remains unresolved. In particular, **there is no
universal Erdős–Gallai proof, no new universal critical sparsity bound, and no
edit to `Spec.lean`.**

The completed results are more limited, but separate the proposed steps:

1. The recursion holds for **every cycle** of a fixed-count graph, hence for
   all genuinely critical graphs of cost at most three using the supplied
   cost-three theorem. Its existential version is preserved by articulation
   sums, two-edge splices, and vertex-edge splices.
2. There is a paper-level, all-size obstruction to the **longest-cycle rank
   accounting**: for every `q>=3`, an explicitly defined simple, genuinely
   `q`-critical graph has **every** longest-cycle complement genuinely
   `(q-1)`-critical and connected, yet
   \[
     \sigma(F)-\sigma(F-E(C))=q,
     \qquad \sigma=\beta+\kappa_e.
   \]
   Thus even setting the extraction remainder `B` to zero does not give a
   bounded longest-cycle charge. No tie-break among longest cycles repairs
   this example. Criticality of **all** even restrictions is proved, not
   inferred from single-cycle deletions.
3. On the fixed-count constructive class, a *different* cycle can be proved
   to have charge at most two: use a loop or parallel pair after series
   suppression, justified by treewidth at most two. This gives a legitimate
   proof of `sigma<=2c` on that class without assuming that an arbitrarily
   added cycle has a good intersection.
4. A small, explicitly **noncritical** control illustrates precisely why
   absorbing `C` into a fixed-count critical anchor `H` need not remain an
   absorption after restoring discarded `B`. It is not a negative answer
   to the recursion, and is not the supplied `S` or a Petersen ring.

Only these files are created:

* `Submission/ResearchCriticalRecursion.md`;
* `ResearchCriticalRecursionCheck.py` at the project root.

The checker is self-contained and uses only the Python standard library.
There is no new graph catalog or enumeration of cost-four candidate cores.
These are paper arguments and exact checks, not Lean formalizations.

---

## 1. Definitions and the precise missing quantifier

All cycles are vertex-simple. A parallel pair is allowed as a cycle in a
loopless auxiliary multigraph; subdivision gives corresponding simple graphs.
For an even edge set `W`, write

\[
 c(W)=\min_{\mathcal D\text{ partition of }W}|\mathcal D|,
 \qquad
 \nu(W)=\max_{\mathcal D\text{ partition of }W}|\mathcal D|.
\]

For any graph `X`, set

\[
 Q(X)=\max_{W\subseteq E(X),\ W\text{ even}}c(W).
\]

A nonempty even `F` is genuinely `q`-critical precisely when

\[
 c(F)=q,\qquad c(W)<q\quad
 \text{for every proper even }W\subsetneq E(F).          \tag{1.1}
\]

Isolated vertices are ignored. For the recursion's terminal case only, the
empty edge set is called 0-critical: it has cost zero and no proper edge
restrictions. The substantive question is for `q>=2`.

For every cycle `C` of a genuinely `q`-critical graph, put `R=F-E(C)`. Then

\[
                 c(R)=Q(R)=q-1.                       \tag{1.2}
\]

Indeed, criticality bounds every even restriction of `R` by `q-1`, while
`c(R)<q-1` would give a partition of `F` with fewer than `q` cycles.

The requested assertion is

> **(R)** Every genuinely `q`-critical graph has **some** cycle `C` for
> which `R=F-E(C)` is genuinely `(q-1)`-critical.

Equation (1.2) alone does not prove (R). Equivalently, for the chosen cycle
one must show

\[
 \max_{W\subsetneq R,\ W\text{ even}}c(W)\le q-2.       \tag{1.3}
\]

An exact way of testing the distinction is

\[
 \begin{aligned}
 Q(W)&=\max\left(c(W),\max_{D\subseteq W\text{ cycle}}Q(W-E(D))\right),\\
 W\ne\varnothing\text{ is critical}
 &\iff c(W)>\max_{D\subseteq W\text{ cycle}}Q(W-E(D)).   \tag{1.4}
 \end{aligned}
\]

Every proper even restriction omits a cycle in its nonempty even complement,
which proves these identities. The maximum must use **all** cycles, not just
cycles through the edge used for a minimum-partition dynamic program.

### What a failed extraction actually supplies

Choose an inclusion-minimal `H subseteq R` of cost `q-1`. By (1.2), it is
**genuinely** `(q-1)`-critical. Write

\[
             F=H\mathbin{\dot\cup}B\mathbin{\dot\cup}C,
             \qquad B=R\setminus H.                  \tag{1.5}
\]

The dot denotes edge-disjointness, not vertex-disjointness. The set `B` is
even. If `B` is nonempty, `K=H union C` is proper in `F`, and therefore

\[
 c(K)\le q-1,\qquad Q(K)=q-1,\qquad \nu(K)\ge q.       \tag{1.6}
\]

For the last inequality, concatenate a minimum `(q-1)`-partition of `H`
with `C`. Thus the absorption occurs in a **proper non-fixed** restriction.
The hypothesis that all proper **critical** restrictions are fixed-count
does not say that this `K` is fixed-count; it contains the proper cost-`q-1`
restriction `H` and is itself noncritical.

If in addition `B` is a single cycle, then

\[
             c(H\cup C)=c(H\cup B)=q-1.               \tag{1.7}
\]

The first equality also uses `q=c(F)<=1+c(H union C)`; the second is (1.2).
These are two absorptions over the same anchor, not a proof that their union
is absorbed. Section 5 gives a completely explicit control for that error.
No proof was found that a lexicographic choice of `C,H` forces `B` empty.

---

## 2. Where the recursion is valid, and how it passes through separators

### 2.1 Fixed count gives every-cycle recursion

If every partition of `F` has `q` cycles, every even restriction is fixed-count:
partitions of that restriction can be completed using any partition of its
even complement. Different counts would give different counts on `F`.

Furthermore every nonempty fixed-count graph is genuinely critical. If
`W subsetneq F` is even, concatenating partitions of `W` and its nonempty
even complement gives

\[
                       c(W)+c(F\setminus W)=q,
\]

so `c(W)<=q-1`. For any cycle `C`, every partition of `F-E(C)` has `q-1`
cycles, hence that complement is genuinely `(q-1)`-critical.

Consequently (R) holds, in fact for **every** cycle:

* for critical costs one and two, by the elementary small-cost arguments;
* for critical cost three, by the previously supplied computer-assisted
  theorem in `ResearchCriticalStructure.md`;
* for the entire Heinrich–Streicher fixed-count constructive class;
* for any critical `F` with a vertex of degree `2q`. In that case every
  cycle contains that vertex, or its deletion contradicts criticality.
  Counting incidences gives fixed count.

The new checker does **not** reprove the all-size cost-three theorem by its
small fixtures. That theorem is an explicitly identified prior input.

### 2.2 The existential recursion is splice-stable

Call a cycle *removable* if its complement is critical of one lower cost.
Use the genuine all-restriction separator formulas already proved in
`ResearchCriticalGraphic.md`, Section 5. At a disjoint or articulation sum,
criticality and costs add. At either edge-splice operation,

\[
 c(F)=q_1+q_2-1,
 \qquad F\text{ critical}\iff F_1,F_2\text{ critical}.   \tag{2.1}
\]

Here the pieces are capped even graphs with marked edges `e_1,e_2`.

**Proposition.** If each critical piece has a removable cycle, so does its
sum or splice.

**Proof.** At a disjoint or articulation sum, remove a removable cycle in
one piece; the other critical pieces are unchanged.

For a splice there are two cases.

* If some piece has a removable cycle avoiding its mark, that same cycle
  occurs in `F`. The complement is the splice of its critical complement
  with the other critical piece. Formula (2.1) gives the required cost.
* Otherwise choose removable cycles `C_i` containing both marks. Splice
  `C_1,C_2` themselves to form one simple cycle of `F`. Its complement is
  the disjoint union, or articulation sum, of `F_i-E(C_i)`. Its cost is
  `(q_1-1)+(q_2-1)=c(F)-1`, and it is genuinely critical.

Empty terminal pieces cause no difficulty with the 0-critical convention.
The graphs in each complement identity have exactly the stated edge sets;
there is no claim that an arbitrary minimum partition retains old cycles. ∎

Thus a least-cost, series-reduced counterexample to (R), if one exists, has
cost at least four and can be reduced to a nonsaturated irreducible core:
no articulation, no nontrivial two-edge splice, and no nontrivial
vertex-edge splice. In the usual loopless core this is the same
4-edge-connected, 2.5-connected setting left by the supplied reductions.
This closure result does not establish (R) on those remaining atoms.

---

## 3. A genuinely critical obstruction to longest-cycle rank charging

Let `k(X)=kappa_e(X)` count edge-containing components, and put

\[
 \beta(X)=|E(X)|-|V_+(X)|+k(X),\qquad \sigma(X)=\beta(X)+k(X).
\]

Both ignore isolates. For connected non-cycle `F` and `R=F-E(C)`, the exact
accounting in `ResearchCriticalSparsity.md` gives

\[
 \sigma(F)-\sigma(R)=b_C+2-2k(R),\qquad
 b_C=|\{v\in V(C):d_F(v)\ge4\}|.                      \tag{3.1}
\]

The following family has `B=empty`, so the extraction issue is entirely
absent, but the longest-cycle charge is still unbounded.

### 3.1 Construction

Fix `r>=2`. Let `T_r` be the tree with vertices

\[
 a_1,\ldots,a_r,\quad b_1,\ldots,b_r,\quad x,y
\]

and edges

\[
 a_i b_i\ (1\le i\le r),\quad
 a_i a_{i+1}\ (1\le i<r),\quad xa_1,\quad a_r y.
\]

Every `a_i` has tree degree three; all the other vertices are leaves.
Add an apex `v` adjacent to **every** vertex of `T_r`, obtaining `F_r`.
This is a simple even graph, with

\[
 n=2r+3,\quad m=4r+3,\quad
 d(v)=2r+2,\quad d(a_i)=4,\quad d(b_i)=d(x)=d(y)=2.     \tag{3.2}
\]

### 3.2 An all-restriction criticality proof

**Apex-forest lemma.** If an even nonempty graph `G` has `G-v` a forest,
then every even restriction `W` satisfies

\[
                   c(W)=\nu(W)=d_W(v)/2.              \tag{3.3}
\]

Every nonempty such restriction is genuinely critical.

**Proof.** Every simple cycle contains `v`. Every cycle in every partition
therefore uses exactly two edges at `v`, proving (3.3). If `U` is a proper
even restriction of `W`, then `W\U` is nonempty even and contains a cycle
through `v`. Consequently `d_U(v)<=d_W(v)-2`, so
`c(U)<=c(W)-1`. This covers **every** proper even edge restriction. ∎

Apply the lemma to `F_r-v=T_r`. With `q=r+1`, it proves

\[
 F_r\text{ genuinely }q\text{-critical},\qquad
 c(F_r)=\nu(F_r)=q,\qquad
 \beta(F_r)=2r+1=2q-1,\quad \sigma(F_r)=2q.             \tag{3.4}
\]

Moreover **every cycle complement** is genuinely `r`-critical, either by
(3.3) or Section 2.1. Thus this family positively satisfies (R) for every
cycle; it is not a counterexample to the recursion.

### 3.3 Every longest cycle has the large charge

A cycle of `F_r` is exactly `v` together with the unique tree path between
two distinct vertices of `T_r`. The diameter paths of `T_r` have length
`r+1`, run through all the `a_i`, and have endpoints in

\[
                  \{x,b_1\}\quad\text{and}\quad\{y,b_r\}.
\]

Hence there are exactly four longest cycles, each of length `r+3`.
For one of them,

\[
                  C_0=vxa_1a_2\cdots a_ryv,
\]

the complement consists of the `r` triangles `v a_i b_i v`, meeting only
at `v`. The other three longest cycles merely interchange the unused leaf
at either end. Every longest complement is therefore a **connected bouquet
of `r` triangles**. In particular,

\[
 \begin{aligned}
 c(R)&=\nu(R)=r=q-1, & R&\text{ is genuinely critical},\\
 k(R)&=1, & \beta(R)&=r, & \sigma(R)&=r+1=q.            \tag{3.5}
 \end{aligned}
\]

All `r+1` vertices `v,a_1,...,a_r` are branch attachments on the deleted
cycle. Thus, for **every** longest cycle,

\[
 \boxed{\sigma(F_r)-\sigma(R)=q,\qquad
        [\sigma(F_r)-\sigma(R)]-2=q-2.}               \tag{3.6}
\]

The second expression is exactly the excess over the two-unit inductive
budget when `B=empty`. It is unbounded. Here `k(F_r)=k(R)=1`, so unlike the
previous bundle-chain example, a component correction does **not** repair
the large deletion charge.

What does repair the actual sharp inequality is the complement's unused
slack:

\[
 \sigma(R)-2(q-1)=2-q,
 \qquad (2-q)+(q-2)=0.                                \tag{3.7}
\]

Discarding this slack and using only the inductive upper bound
`sigma(R)<=2(q-1)` loses the argument. Nor can a secondary tie-break among
longest cycles help: all four have the same quantities (3.5)–(3.6).

There **are** better cycles. For example the triangle `v a_1 b_1 v` has
just two branch attachments, has connected complement, and loses exactly
two units of `sigma`. Therefore this example does not disprove the
existence of a well-charged cycle, or rule out longest cycles as a way to
prove **criticality of the complement alone**. It refutes using maximal
length to obtain a bounded rank increment for that complement.

---

## 4. The conditional fixed-count step and a valid rank argument on its class

### 4.1 The conditional induction is not a weaker universal theorem

Consider the assertion

> **(I)** If `F` is critical and every proper critical restriction of `F`
> is fixed-count, then `F` is fixed-count.

As a universal assertion, (I) is equivalent to “every critical graph is
fixed-count.” If the latter fails, take a non-fixed critical graph of least
critical cost. Every proper critical restriction has strictly smaller cost
and is fixed-count, so this graph violates (I). The converse implication is
immediate.

For the proposed recursive proof it is useful to distinguish a second
unproved assertion:

> **(E)** If `F` is critical and `F-E(C)` is fixed-count for some cycle
> `C`, then `F` is fixed-count.

Universal fixed count implies both (R) and (E). Conversely, **(R) and (E)
together** imply universal fixed count by induction on critical cost. This
is a correct conditional route, but neither (R) nor (E) is proved here in
the remaining generality. In particular, after applying (R), the supplied
constructive description of `H=F-E(C)` does not by itself make the addition
of `C` an allowed construction operation. The cycle may meet many pieces
and destroy their separators. Section 3 supplies a genuinely critical
example where it meets one connected `H` in arbitrarily many vertices.

### 4.2 Good intersections really can be proved after fixed count is known

The supplied source, arXiv:1708.09141, characterizes fixed-count connected
even graphs by even multiedges, articulation sums, and vertex-edge splices.
It also gives treewidth at most two for this class. The following is a
legitimate way to obtain a good deletion cycle, rather than assuming that
the inductively added cycle was good.

**Lemma.** A nonempty fixed-count even graph contains a cycle `D` such that

\[
                 \sigma(F)-\sigma(F-E(D))\le2.        \tag{4.1}
\]

Its complement is fixed-count and genuinely critical when nonempty.

**Proof.** If a component is a cycle, delete that component; its contribution
to `sigma` is two. Otherwise suppress the degree-two paths of a non-cycle
component. The resulting even core has minimum degree at least four.
Suppression is a minor operation, so its underlying simple graph still
has treewidth at most two. If the core had neither loops nor parallel
edges, it would be a simple graph of minimum degree at least four and
treewidth at most two, impossible: graphs of treewidth at most two are
2-degenerate. Thus the core has a loop or a parallel pair.

Lift that core cycle back to `F`. It meets the remaining edges at at most
one or two branch vertices. The affected component does not disappear,
so deletion cannot decrease the number of edge-containing components.
The cycle-deletion identity gives (4.1). Fixed count of the complement
and its criticality follow from Section 2.1. ∎

Iterating this lemma on the fixed-count complements, their costs decrease
by exactly one. With `sigma(empty)=0`, it proves

\[
                  \boxed{\sigma(F)\le2c(F)}           \tag{4.2}
\]

on the fixed-count class, hence `beta(F)<=2q-1` when connected. The
intersection property is **proved by selecting a suitable cycle in the
current fixed-count graph**, not inherited from an arbitrary extension.

This agrees with the constructive accounting: a `2s`-edge bundle has
`sigma=2s`; at a connected articulation sum `sigma=sigma_1+sigma_2-1`
and `c=c_1+c_2`; at a vertex-edge or two-edge splice
`sigma=sigma_1+sigma_2-2` and `c=c_1+c_2-1`. Subdivision preserves `sigma`.
Neither argument applies to a general critical atom before fixed count is
proved.

If (4.2) were established on all critical graphs, critical extraction in a
simple even `G` would give a critical `F` of cost `q=Q(G)>=c(G)`, and

\[
 3q\le m(F)=\beta(F)+n_+(F)-k(F)
          \le 2q+n_+(F)-2k(F),
\]

so `c(G)<=q<=n_+(F)-2k(F)<=n(G)`. This is a **conditional** implication,
not a universal bound established by this note.

---

## 5. A deliberately noncritical control for restoring the discarded B

This small control is included only to isolate the invalid absorption step.
**It is not a counterexample to (R), (I), or (E).**

On vertices `v,a,b,c,d`, let `H` consist of the two triangles

\[
                         vabv,\qquad vcdv.
\]

Let `B` and `C` be distinct parallel copies of the rim cycle

\[
                              acbda.
\]

The two copies have disjoint edge identities. Then `H` is genuinely
2-critical and fixed-count. Each of `H union B` and `H union C` is `K5`,
so

\[
 c(H\cup B)=Q(H\cup B)=c(H\cup C)=Q(H\cup C)=2.        \tag{5.1}
\]

For completeness, the two five-cycles `vabcdv` and `vbdacv` partition
`K5`. Every proper even restriction of `K5` has at most seven edges,
since its nonempty even complement has at least three. Its cycle
partitions therefore have at most two cycles; this proves the stated
hereditary value.

However, for `F=H union B union C`,

\[
                              c(F)=3.                 \tag{5.2}
\]

A rim vertex has degree six, giving the lower bound; a two-cycle partition
of `H union B` completed by `C` gives the upper bound. Thus absorption of
`C` into `H` in (5.1) does **not** remain cost-neutral after restoring `B`.
In the notation of (1.5), the chosen complement has `c=Q=q-1`, the anchor
is fixed-count and genuinely critical, and `B` is even a single cycle.

Here is the explicit reason this is **not** a genuine critical example:
let `W` consist of the triangle `vabv`, the two parallel `ac` edges, and
the two parallel `ad` edges. This is a proper even restriction; all its
cycles contain `a`, and `d_W(a)=6`. The apex-forest argument proves

\[
               c(W)=\nu(W)=3,\qquad W\text{ genuinely critical}. \tag{5.3}
\]

For an actual simple graph, subdivide each of the four edges in the second
rim copy once, using private new vertices. The resulting `F` has nine
vertices and eighteen edges. All even restrictions, cycles, and partitions
correspond bijectively, and the proper witness (5.3) survives.

The checker audits all 1,024 even restrictions of both presentations. It
also finds `Q(F)=3` and `nu(F)=6`. These additional finite values are not
used to infer criticality: the witness (5.3) explicitly disproves it.
The equalities (5.1) concern the two indicated complements, **not all cycle
complements of `F`**. No all-cycle or genuine-critical premise is smuggled
into this control.

---

## 6. Verification and exact stopping point

Run from the project root:

```sh
PYTHONHASHSEED=0 python3 -B ResearchCriticalRecursionCheck.py
```

The default inputs are the five instances `F_r`, `2<=r<=6`, and the core
and simple lift of Section 5: **seven inputs and 12,960 even-word audits**.
The default writes no files and ends with `ALL EXACT CHECKS PASSED`.

| input | genuine critical? | `c` | `nu` | `beta` | all even words |
|---|---:|---:|---:|---:|---:|
| `F_2` | yes | 3 | 3 | 5 | 32 |
| `F_3` | yes | 4 | 4 | 7 | 128 |
| `F_4` | yes | 5 | 5 | 9 | 512 |
| `F_5` | yes | 6 | 6 | 11 | 2,048 |
| `F_6` | yes | 7 | 7 | 13 | 8,192 |
| double absorber, core | **no** | 3 | 6 | 10 | 1,024 |
| double absorber, simple lift | **no** | 3 | 6 | 10 | 1,024 |

The verification does not merely test deletion of cycles:

* Binary incidence elimination enumerates the **complete** even-edge
  kernel and checks its dimension against `m-n_++kappa_e`. On small edge
  sets this is additionally compared with literal enumeration of all masks.
* Vertex-simple DFS is compared with the connected, nonempty, 2-regular
  words in the complete kernel.
* Exact minimum and maximum partition dynamic programs are run and their
  partitions reconstructed on **every** even restriction.
* Hereditary `Q` and criticality use (1.4) with all cycles. The whole graph
  and every one of its cycle complements receive additional **direct
  containment** audits over all proper even restrictions.
* Formula (3.3), criticality of every nonempty restriction of `F_r`, all
  four longest complements, and the short-cycle two-unit charge are checked.
* The simple-lift bijection is verified on every even word and every cycle;
  the proper critical witness (5.3) is audited directly in both presentations.

The all-size proofs are Sections 2–4, not extrapolations from these bounded
inputs. The optional `--graph-stdin` mode gives exact full-support criticality
and lists cycles with genuinely critical complements, refusing cycle-space
dimension above 16. Empty, isolated-vertex, one-cycle, and disconnected
cycle controls passed separately, including the empty terminal convention.

Syntax parsing passed. Complete runs with `PYTHONHASHSEED=0` and `17` gave
byte-identical output, whose SHA-256 is

```
cbae349d8e2b004b785049fcc8fa0c20d2affb733e76fd0c2546e49a0f329ced
```

### Preservation and source scope

All **249 pre-existing non-cache files outside `.lake` and `.git`** are
protected by the pre-work combined fingerprint, excluding only the two
permitted new files:

```
73e1343c054765d6e6142ef7d82a5684c14461581b447db605188a359bc08b88
```

The unchanged `Submission/Spec.lean` SHA-256 is

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

The checker verifies both before and after running. No old note, checker,
specification, or bytecode cache was written.

The fixed-count construction and its treewidth consequence were read in

```
/corpus/src/1708.09141/heinrichStreicherCycleDecompositionsAndConstructiveCharacterizations.tex
```

That source characterizes **fixed-count graphs**. It does not assert that
genuine criticality implies fixed count, or that attaching an arbitrary
cycle to a member of the class stays in the class. No such claim is used.

### What still has to be proved

The focused attempt stops at the original, genuine gaps:

1. Show that some pair in (1.5) has `B=empty`, or supply a genuinely critical
   graph for which every complement fails (1.3). Neither was obtained.
2. For the proposed fixed-count induction, justify the compatibility of the
   new cycle with the fixed-count anchor — for example prove (E). The
   constructive class is not automatically closed under this attachment.
3. Even if (R) is proved without fixed count, a sparsity induction must
   control attachments **together with available slack**, or prove a
   different existential cycle choice. The longest-cycle charge alone is
   unbounded on the genuinely critical family above.

**No universal Erdős–Gallai proof is obtained.** In particular, neither the
noncritical absorption control nor the genuine longest-cycle obstruction
is misreported as a counterexample to critical cycle-complement recursion.
