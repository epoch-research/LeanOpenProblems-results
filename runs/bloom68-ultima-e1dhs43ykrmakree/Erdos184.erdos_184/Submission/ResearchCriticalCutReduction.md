# Critical cut reduction and the remaining averaging obstruction

## Status

No proof or disproof of Erdős–Gallai is supplied. `Spec.lean` is unchanged.
The statements below are paper-level reductions, not Lean formalizations.
They were checked directly from genuine simple-cycle partitions. Neither
admitted theorem in Spec is used.

## 1. A cut inequality for hereditary integral cost

For any finite graph X, put

    Q(X) = max { c(H) : H is an even edge restriction of X },
    r(X) = |V(X)| - number_of_components(X),

where c denotes the minimum number of vertex-simple cycles in an exact
edge partition. Isolated vertices contribute to the component count, so
r does not change when isolates are added or discarded.

For a nontrivial vertex bipartition A,B,

    Q(X) <= floor(|delta_X(A)|/2) + Q(X[A]) + Q(X[B]).       (1)

Proof: take any even restriction H and any actual cycle partition of H.
Delete its t cycles meeting both sides. Each such cycle uses at least two
cut edges, and the cycles are edge-disjoint, hence 2t <= |delta_X(A)|.
The remaining edge sets on the two sides are even. Repartitioning them
costs at most Q(X[A]) and Q(X[B]). Then maximize over H. Neither the
induced sides nor the remainders are assumed critical or even initially.

## 2. Minimal failures of a fixed coarse rank bound

Fix an integer K>=1 and suppose c(G)<=K r(G) fails for an even simple graph.
Choose an edge-minimal failure F and remove isolates. Write n=|V(F)|,
q=c(F). Then:

(a) F is connected and genuinely q-critical: every proper even restriction
W has c(W)<=K r(W)<=K r(F)<q. Disconnectedness would allow adding the
bounds for the nonempty components, contradicting minimality.

(b) q=K(n-1)+1. Deleting any cycle C leaves a proper even graph, so
q<=1+c(F-E(C))<=1+K(n-1); integrality and failure of the bound give equality.
In particular c(F-E(C))=q-1 for every cycle.

(c) If t edge-disjoint simple cycles are deleted and the residual R has
rank at most r(F)-s, where s>=1, then t>=Ks+1. Indeed minimality gives

    K r(F)+1 = q <= t+c(R) <= t+K r(R) <= t+K(r(F)-s).

Thus deleting at most K cycles cannot lower rank. The residual must still
be connected on all original vertices, not merely on its nonisolated
support. This holds for every such family, without assuming that the
family extends simultaneously to a minimum partition.

(d) Every nontrivial edge cut has size at least 2K+2. Otherwise choose any
cycle partition and delete the cycles crossing that cut. At most K cycles
are deleted, yet the rank decreases, contradicting (c). Every cut of an
even graph has even size.

More generally, for every partition into ell>=2 nonempty vertex parts,

    |E_between_parts| >= 2K(ell-1)+2.                        (2)

Delete the t crossing cycles of any cycle partition. The residual has at
least ell components, hence (c) gives t>=K(ell-1)+1. Each crossing cycle
uses at least two distinct between-part edges, proving (2).

(e) Every genuinely (q-1)-critical anchor H extracted from F-E(C) is
connected and spanning on the original vertex set. Its cost is q-1 and
minimality yields

    K(n-1)=c(H)<=K r(H)<=K(n-1).

Hence r(H)=n-1. Single-cycle extraction supplies no rank saving in this
minimal obstruction. This is an exact barrier, not a missing term that
can be discarded during induction.

## 3. A sufficient weakening of fixed-count structure

The following statement would suffice, but is NOT proved here:

    There exists an absolute integer K>=1 such that every connected,
    nonempty, critical SIMPLE graph has a cut of size at most 2K.   (BC)

A minimal failure as in Section 2 would contradict (d). Thus (BC) implies
c(G)<=K r(G) for every even simple graph. Taking a critical restriction
attaining Q also gives Q(G)<=K r(G) for arbitrary graphs.

For the final cycle/edge formulation, remove a parity-correcting subset
of a spanning forest, of size at most r(G), leaving an even graph. Return
these edges singly after partitioning the remainder. This would yield
at most (K+1)|V(G)| pieces.

An even weaker sufficient hypothesis is that at most K edge-disjoint
simple cycles can be removed from each connected critical simple graph
so as to decrease rank. Section 2(c) gives the same contradiction.

**Neither sufficient structural hypothesis is established.** They cannot
be transferred unchanged to suppressed multigraph cores: the critical
bundle of 2q parallel edges has edge connectivity 2q and requires deleting
q pair-cycles to lower its rank. Simplicity and subdivision-vertex
accounting are essential.

## 4. Prescribing a circuit for mean-cost induction can fail badly

This section concerns regular matroids, not a graphic counterexample.
Let a(M) be the mean of exact fractional circuit-partition cost over ALL
uniformly sampled cycle-space words, including zero. The elementary
retained-anchor gluing identities and the R10 data are established in
`ResearchUniformFractional.md`, Sections 2.1-2.5.

R10 has cycle dimension five; its 30 proper nonzero words are circuits;
c(R10)=2, cf(E)=5/3, and a(R10)=95/96. Glue t copies with one retained
common anchor p. The result T_t satisfies

    c(T_t)=t+1,       a(T_t)=(47t+48)/96.

Every circuit C through p consists of one anchor-containing circuit from
each factor. In each factor its complement is a circuit avoiding p.
Consequently the remaining restriction is a direct sum of t circuit
codes and

    c(T_t|(E-C))=t,
    a(T_t|(E-C))=t/2,
    a(T_t)-a(T_t|(E-C))=(48-t)/96.                          (3)

Thus EVERY circuit through the prescribed anchor extends a minimum
partition, but deleting it increases the mean by an unbounded amount.
A rooted deletion rule cannot obtain even a fixed additive loss bound.
The same construction with Fano factors gives difference (32-t)/64.

There are 15t anchor-avoiding circuits and 15^t anchor-containing circuits;
all belong to minimum partitions. Deleting an anchor-avoiding circuit
replaces its factor by an anchor-containing circuit and drops the mean
by 47/96. Therefore uniform averaging over the SET of all
optimum-compatible circuits has expected mean drop

    [15^t(48-t)+705t] / [96(15^t+15t)],

which tends to negative infinity. This is not uniform sampling of a part
of one chosen minimum partition: such a partition has one anchor circuit
and t local circuits, and its total mean drops are (46t+48)/96.

## 5. Exact remaining gaps

No uniform bound on cuts or rank-lowering cycle families in critical
simple graphs was proved. No adaptive positive mean-payment theorem was
proved either. For example, the still-unproved choice statement

    c(E-C)=c(E)-1 and a(M)-a(M|(E-C)) >= 1/K

for SOME optimum-compatible circuit, with one universal K, would induct
to c(M)-1 <= K(a(M)-1/2). Equations (3) rule out prescribing a root or
uniformly sampling all eligible circuits; they do not refute the adaptive
statement, and they are not graphic counterexamples.

The universal integral bound required by Spec remains unresolved.

## 6. Criticality-preserving pruning through splices

A subsequent focused investigation gives another paper-level reduction,
not a universal bound. For a two-edge splice or vertex-edge splice of
nonempty even factors F1,F2, with marked edges ei, the full-space mean is

    a(F)=a(F1)+a(F2)-1/2.                                  (5)

An even restriction uses either both connectors (one connector for the
vertex-edge splice) or none. Capping the two sides gives even words Hi
with a common marked-edge bit b. Under uniform sampling b is fair and
each marginal Hi is uniform on its ENTIRE factor cycle space. Fairness
follows by toggling a cycle through the marked edge. The exact fractional
identity is cf(H)=cf(H1)+cf(H2)-b: marked cycle masses sum to one and can
be coupled to glue, or capped to project, actual simple cycles. Averaging
gives (5). There is no restriction to subunions of a supplied partition.

Writing qi=c(Fi), one has c(F)=q1+q2-1, and F is genuinely critical iff
both factors are genuinely critical. For sufficiency, in common state
zero both factors omit their mark, so their costs sum to at most
q1+q2-2. In a proper state-one restriction at least one factor is proper,
and the splice saves one, giving the same bound. For necessity, a proper
factor word containing its mark can be spliced with the other full
factor. For a word H1 omitting its mark and having c(H1)>=q1, choose any
cycle C2 through e2. Since c(F2-C2)>=q2-1, the proper restriction
H1 union (F2-C2) has cost at least q1+q2-1, contradicting criticality.

Replace Fj by any cycle through its mark. The resulting Ki is an actual
even restriction of F, has c(Ki)=qi and a(Ki)=a(Fi), and is critical when
Fi is critical. It is proper if qj>=2. This realizes factor extraction
inside the original simple graph, even if a capped factor has parallel
edges: its marked edge is replaced by the chosen opposite path.

If a graphic splice factor has FIXED partition count qi>=2, choose a
partition of it and delete a part not containing the mark. Its remaining
factor is fixed-count and critical of cost qi-1. The full splice therefore
remains critical of cost q-1. Graphic fixed-count factors have a=qi/2 by
exact unit-cycle signed prices, so (5) shows this deletion decreases a
by exactly 1/2. This is a legitimate local adaptive step, including the
known critical factors of cost two and three. It does not imply that an
arbitrary critical cycle complement is critical.

The splice-stable defect for K>=2 is

    D_K(F)=c(F)-1-K*(a(F)-1/2).

It adds exactly under the two splice operations. For articulation or
disjoint sums it is D_K(F1)+D_K(F2)-(K/2-1). Thus the useful strengthened
targets are q<=4a-1 or q<=8a-3. A positive defect across a nontrivial
splice has a positive-defect factor, realizable by the critical
restriction Ki above. This uses no hereditary monotonicity of a.

The shift is essential: the unshifted quantity c-4a is the sum of the
factor quantities PLUS ONE under a splice, so an ordinary unshifted
factor induction is invalid. Finally, a(F)>=Delta(F)/4 implies q<=4a-1
when q<=Delta(F)-1. There is still no mean lower bound or adaptive
critical successor for irreducible critical cores with q>=Delta(F).

All identities and the two-state criticality argument were checked
independently. No complete argument for the irreducible case was found,
and neither theorem in Spec has been proved.
