# Critical attachment: the anchored-price attempt and its exact gap

## Outcome

**No universal linear cycle-partition bound is proved.** The conditional
induction

> a graphic critical graph whose proper critical restrictions are all
> fixed-count is itself fixed-count

remains unresolved. Neither a proof nor a genuinely critical counterexample
is supplied. No cycle-complement recursion is assumed. `Spec.lean` and all
pre-existing files are unchanged.

This is one focused attempt at the proposed attachment/linear-duality route,
not a new family search. Its concrete conclusions are:

* With a nonempty extraction remainder, preserving the fixed anchor's exact
  prices cannot yield the desired global dual value. Proper **low-cost
  absorbers** already give integral linear certificates obstructing it.
* Summing all those absorptions and cancelling the repeated anchor gives
  exact global edge loads and the desired cost, but potentially **negative
  cycle coefficients**. Neither local integrality nor edge-load accounting
  removes these coefficients.
* Even when the remainder is empty, the circular-interval equations from
  single ears omit equations from simple cycles using several ears. These
  are genuine graphic, multi-terminal compatibility constraints.

The arguments below identify where the proof stops; they do not turn any
of these observations into the missing universal lemma. No new fixture,
catalog, or checker is created.

---

## 1. The induction hypothesis and extraction, with all quantifiers retained

Cycles are vertex-simple; auxiliary loopless multigraphs retain distinct
parallel edges. For an even edge set `W`, let `c(W)` and `nu(W)` be the
minimum and maximum cycle-partition counts. For any edge set `X`, let

\[
 Q(X)=\max_{W\subseteq X,\ W\text{ even}}c(W).
\]

Suppose `F` is `q`-critical, `q>=2`, and put `r=q-1`. Thus `c(F)=q`
and every proper even restriction has cost at most `r`. Assume **only for
this attempted induction** that every proper critical restriction of `F`
is fixed-count.

For every cycle `C`, `R=F-E(C)` satisfies

\[
                         c(R)=Q(R)=r.                 \tag{1}
\]

The upper bounds follow from criticality; `c(R)<r` would contradict
`c(F)=r+1` after restoring `C`. Choose an inclusion-minimal even `H`
inside `R` with `c(H)=r`. Every proper even restriction of `H` has cost
less than `r`: it cannot exceed `r` by (1), and equality contradicts the
choice. Consequently `H` is genuinely critical and the induction
hypothesis makes it fixed-count. Write

\[
 F=H\mathbin{\dot\cup}B\mathbin{\dot\cup}C,
 \qquad J=F\setminus H=B\mathbin{\dot\cup}C.           \tag{2}
\]

All three displayed parts are even. Edge-disjointness does not mean
vertex-disjointness. **Nothing here proves `B` empty.**

The induction hypothesis also implies that, for every proper edge set
`X` of `F`, `Q(X)` is attained by a fixed-count restriction: take a
minimal restriction attaining `Q(X)` and apply the hypothesis. It does
**not** make `X`, or even an even `X`, fixed-count.

If `B` is nonempty, `J` is not a simple cycle. For every cycle `D` of `J`,
`D` is proper in `J`, so `K_D=H union D` is proper in `F` and

\[
 c(K_D)\le r,\qquad Q(K_D)=r,\qquad \nu(K_D)\ge r+1.  \tag{3}
\]

Here `H` supplies the lower bound on `Q`, and a partition of `H` followed
by `D` supplies the lower bound on `nu`. In particular `K_D` is
**noncritical and non-fixed**. Its cost need not equal `r` in general.
There is no conflict between (3) and the induction hypothesis.

The graphic fixed-count theorem and its construction are used only for
the available facts about `H`: it has signed edge prices making every
cycle exactly one, and it satisfies `sigma(H)<=2r`. The source
`1708.09141`, Section “Graphs with unique cycle-decomposition size,”
characterizes fixed count; it does not prove criticality implies fixed count.
The signed-price construction is given in `ResearchCriticalGraphic.md`, §3.

---

## 2. What linear duality actually certifies when B is nonempty

For an edge-price vector `y`, write `y(X)=sum_{e in X} y_e`. Consider the
full-graph cycle inequalities together with preservation of the anchor:

\[
 y(Z)\le1\quad\text{for every simple cycle }Z\subseteq F,
 \qquad y(H)=r.                                      \tag{4}
\]

Prices have **no sign restriction**. In particular this is not a failed
attempt to use nonnegative prices in a problem requiring signed prices.

### Lemma — exact-anchor extensions cannot have value above r

If `J=F-H` is not a cycle, every vector satisfying (4) obeys

\[
 y(D)\le0\quad(D\subseteq J\text{ a cycle}),\qquad
 y(J)\le0,\qquad y(F)\le r.                          \tag{5}
\]

**Proof.** Fix a cycle `D` in `J`. By (3), choose a partition `P_D`
of `H union D` with `k_D<=r` members. Summing (4) over that partition
and using edge-disjointness gives

\[
                r+y(D)=y(H\cup D)\le k_D\le r.
\]

Partitioning the even graph `J` into cycles gives the other inequalities.
This uses all-restriction criticality, not just the costs of single-cycle
complements. ∎

The feasible set in (4) is nonempty. Start with exact unit-cycle prices on
`H` and give every edge outside `H` a sufficiently large negative price.
There are finitely many cycles; all cycles not contained in `H` use an
outside edge. This makes all their inequalities hold. Thus (5) is a real
objective bound, not a consequence of inconsistent anchor constraints.

Moreover, the obstruction has an **integral certificate already**. For
any partition `P_H` of `H`, let `chi_Z` denote the edge-incidence vector
of a cycle. Then

\[
 \chi_D=
 \sum_{Z\in P_D}\chi_Z-\sum_{A\in P_H}\chi_A,
 \qquad |P_D|-|P_H|=k_D-r\le0.                       \tag{6}
\]

Every cycle of `H` has price one in any feasible (4): every such cycle
belongs to an `r`-partition of the fixed-count graph `H`, whose total
price is `r`. Applying the cycle inequalities and these equalities to
(6) proves `y(D)<=k_D-r`. This is a linear-duality certificate against
adding the condition `y(D)=1`, with no fractional rounding issue.

**Its direction matters.** The certificate exhibits a proper absorber
of cost **at most** `r`. It does not exhibit a proper restriction of cost
`q`. Even if a network formulation made this certificate integral, that
alone would not supply the required contradiction.

For comparison, if a feasible full-graph dual had value `q`, criticality
would force every cycle to be tight. Indeed each cycle extends to a
minimum `q`-partition by (1); all `q` inequalities in that partition
must be equalities. Such a dual would preserve `y(H)=r`, contradicting
(5). This recovers a fractional obstruction when `B` is nonempty; it is
**not** an integral contradiction to criticality.

---

## 3. The global cancellation attempt, with B included

Choose a partition `D_1,...,D_t` of `J`, where `t>=2`. For each `i`,
choose a partition `P_i` of `H union D_i` with `k_i<=r`, using (3).
Also fix an `r`-partition `P_H` of `H`.

Work now in the vector space indexed by **all simple cycles of F**, not
by edges. Let `1_P` be a partition's incidence vector in this space and
let `A` be the edge-by-cycle incidence matrix. The natural global
cancellation is

\[
 z=\sum_{i=1}^t\mathbf1_{P_i}-(t-1)\mathbf1_{P_H}.
                                                               \tag{7}
\]

It satisfies both desired numerical identities:

\[
 \begin{aligned}
 Az&=t\chi_H+\chi_J-(t-1)\chi_H=\chi_F,\\
 \mathbf1^Tz&=\sum_i k_i-(t-1)r\le r.               \tag{8}
 \end{aligned}
\]

If `z` were nonnegative, it would be a **nonnegative integer** exact
partition vector, hence an actual partition of `F` with at most `r`
cycles. Edge load one prevents a nonempty cycle from having multiplicity
greater than one. This would contradict `c(F)=r+1`.

But the subtraction in (7) need not be nonnegative. Its exact condition is

\[
 \#\{i:A_0\in P_i\}\ge t-1
 \quad\text{for every }A_0\in P_H.                  \tag{9}
\]

There are no possibly negative coordinates outside `P_H`. Fixed count
controls the **numbers** of cycles in partitions of `H`, not the retained
cycle identities required by (9). Neither the existence of each absorber
nor integrality of its local profile proves these simultaneous retention
inequalities. In fact, under the standing criticality assumption every
choice in (7) must have a negative coordinate, by (8).

This calculation includes all discarded edges, rather than silently
restoring `B` after an absorption. It also pinpoints why merely allowing
signed edge cancellation is insufficient: (8) is already correct over
the integers. The unresolved part is positivity in **cycle coordinates**.

Condition (9) is only one sufficient way to glue the absorptions. It is
not asserted necessary for a low-cost partition: a global reoptimization
can use cycles meeting several different `D_i`, which (7) need not use.
Thus failure of this particular cancellation is not a counterexample,
and is not by itself a dual certificate for a proper cost-`q` restriction.
No monotone-absorption or universal retention lemma is assumed here.

---

## 4. Why the single-circle equations do not finish even the B=empty case

Suppose temporarily that `B` is empty, so `F=H union C`. This is an
additional assumption for this paragraph, **not** a consequence of (1).
An exact unit-price extension would have to satisfy

\[
 y(A)=1\ (A\subseteq H\text{ a cycle}),\qquad
 y(C)=1,\qquad
 y(Z)=1\ (Z\subseteq F\text{ a mixed simple cycle}). \tag{10}
\]

Such an extension would immediately give fixed count `r+1`. The
fixed-count graphic theorem supplies the converse, but no existence
argument for (10) follows from that characterization alone.

Here is the precise circular-interval reduction and the equations it
leaves over. Let the attachment vertices be `V_+(H) intersect V(C)`, and
let `x_j` be the total price of each arc between consecutive attachments
on `C`. If there are fewer than two attachments the union is a disjoint
or articulation sum, already fixed-count; consider the remaining case.

An **H-ear** is a simple path in `H` with distinct endpoints on `C` and
interior disjoint from `V(C)`. For such a path `P` with endpoints `u,v`,
both unions with the two complementary `u-v` arcs of `C` are simple
cycles. Their equations in (10), together with `y(C)=1`, imply

\[
 y(P)=\tfrac12,\qquad
 x(C[u,v])=x(C[v,u])=\tfrac12.                       \tag{11}
\]

These are the genuine one-ear interval equations. However, a mixed
simple cycle can use several H-ears. Split its traversal at every vertex
on `C`, including any such vertex visited without using a C-edge there.
If `k(Z)` is the number of H-ears in this splitting, (11) gives the
additional necessary equation

\[
       \sum_{j:\,\text{arc }j\subseteq Z}x_j
                         =1-\frac{k(Z)}2.           \tag{12}
\]

The selected arcs can form several separated intervals. Consecutive
H-ears are allowed in the splitting; no positive-length C-arc between
them is assumed. Which collections of ears actually form a simple cycle
also depends on routing with mutually disjoint interiors and compatible
endpoints, as required for a simple cycle. A proof that solving (11)
satisfies all these rows under the standing critical
hypotheses is still needed. No automatic consecutive-ones or network-matrix
integrality argument has been justified for the full system (10)–(12).

Likewise a two-terminal separator in the construction of `H` need not
remain two-terminal after adding `C`: the added cycle can attach at
additional interior vertices of the piece. With `B` restored there can
also be outside edges with no single circular order. Integral
**two-terminal** traffic profiles do not, without a further theorem,
provide the required global multi-terminal compatibility. This is the
graphic step missing from this attempt; the generic signed-state
extension assertion is not substituted for it.

---

## 5. The corresponding sparsity charge is still uncontrolled

For an even graph `X`, let `n_+(X)` count nonisolated vertices and `k(X)`
edge-containing components. Put

\[
 \beta(X)=|E(X)|-n_+(X)+k(X),\qquad
 \sigma(X)=\beta(X)+k(X).
\]

Write `a=|V_+(J)\setminus V_+(H)|`. Counting vertices and edges directly
in (2), without deleting or forgetting `B`, gives

\[
 \sigma(F)-\sigma(H)
       =|E(J)|-a+2\bigl(k(F)-k(H)\bigr).             \tag{13}
\]

Since the fixed-count anchor satisfies `sigma(H)<=2r`, define its slack
`s=2r-sigma(H)>=0`. The sharp desired induction would need

\[
 |E(J)|-a+2\bigl(k(F)-k(H)\bigr)\le2+s.             \tag{14}
\]

For `J=C` this specializes to the attachment count with its component
correction, not a longest-cycle bound. For `J=B union C`, (14) also
contains the intrinsic contribution of all discarded edges. Neither the
price obstruction (5) nor the signed cancellation (7) bounds that charge.
No replacement inequality with coefficient less than three on `q`,
strong enough to yield the requested linear Erdős–Gallai bound, is proved.

## Exact stopping point and verification

To close the conditional induction one still needs a **graphic global
compatibility theorem** that uses the full critical hypothesis and the
fixed proper critical pieces to produce either a genuine lower-cost
partition of `F` or a proper even restriction of cost at least `q` when
fixed-count extension fails. The linear certificates above do neither:
(6) has the wrong cost direction for such a witness, and (7) has the
wrong sign condition for such a partition. The multi-ear constraints
explain why the suggested two-terminal argument does not yet supply the
missing theorem. This is a stopping point, not a claim that no different
global argument can work.

Verification here is paper-level: (5) follows by summing inequalities on
actual partitions, (6) and (8) are exact incidence identities, (11) uses
two explicitly simple cycles, and (13) follows from
`m(F)=m(H)+m(J)` and `n_+(F)=n_+(H)+a`. No finite check is presented as
verification of a universal implication. In particular no binary
critical-to-fixed assertion, no longest-cycle charging rule, and no
unproved critical-complement recursion enters the argument. An in-memory
sanity check reused only the existing **noncritical** double-absorber
control from `ResearchCriticalRecursionCheck.py`: the incidence identities,
negative-coordinate diagnostic, feasible anchor-price bound, and sparsity
identity passed. No new graph input or checker file was introduced, and
this bounded check is not evidence for the missing criticality theorem.

Only `Submission/ResearchCriticalAttachment.md` is created. The combined
SHA-256 fingerprint of the **251 pre-existing non-cache files** outside
`.lake` and `.git`, using sorted `path + NUL + file_sha256 + newline`
records, is

```
9b878b549c6cc9300c521553ccb0f56cd13ba3b2509937a0d677da96206b2679
```

The specification's SHA-256 remains

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

**The universal bound and the conditional fixed-count induction remain
unproved. No edit to Spec is justified by this attempt.**
