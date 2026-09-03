# Global absorption: a terminal-cut obstruction to a rank-only retirement lemma

## Status

**No universal constant C and no complete Erdős–Gallai proof have been obtained.** This investigation tests one proposed universal absorption lemma, proves that it is false, and stops that route. It does not change `Spec.lean` or any pre-existing file.

The result is stronger than a failure to route one prescribed matching: it is an **unbounded difference between the actual minimum simple-cycle partition numbers** of an even graph and its smaller cap graph. The reservoir can be fixed while the outside graph grows. It is connected, has normalized edge conductance exactly `1/4`, has uniformly positive relative degrees on both sides, and has the correct parity. The external terminal average degree is exactly one.

For integers `k,h >= 1`, the construction below gives

```
c(G_(k,h)) = 8k + kh,            c(J_(k,h)) = 8k,
r(G_(k,h)) - r(J_(k,h)) = 2,
W_G(R_k) = 9k + 3.                                      (0.1)
```

Thus neither the removed rank nor the original degree share of this reservoir can pay the absorption surcharge, even up to an arbitrarily large fixed constant. A general terminal-cut amplification lemma explains the obstruction. An explicit partition attaining (0.1) accounts for every edge using vertex-simple cycles.

This is **not** a counterexample to Erdős–Gallai, nor a refutation of unrestricted nested open packets. In fact, the displayed partitions have fewer than `|V(G)|/2` cycles. A scheme allowed to reopen and charge the outside graph may avoid the obstruction; no universal once-only account for such reopening is proved here.

## 1. The one attempted universal lemma

All graphs are finite, simple, and undirected. A cycle is vertex-simple and has length at least three. Every partition is an exact edge partition. For an even graph, write

```
c(G) = minimum number of simple cycles partitioning E(G),
r(G) = |V(G)| - kappa(G),
W_G(F) = sum_v d_F(v)/d_G(v),
```

omitting zero original degrees in the last sum. Cycle removal guarantees that `c(G)` is defined; no linear bound is assumed.

The starting point is the context-uniform odd-twin retirement theorem in `ResearchReservoirExtension.md`, Section 8. It replaces an independent odd set `U` complete to its terminal set `W` by one root, and pays at most `(3/2)(|U|-1)` under the external-average-three condition. Removed graphic rank telescopes exactly. The question tested here is whether fixed positive relative density and expansion can replace identical neighborhoods.

For a connected bipartite reservoir `R` with sides `U,W`, define

```
vol_R(X) = sum_(v in X) d_R(v),
Phi(R) = min_(empty != X != V(R))
          |delta_R(X)| / min(vol_R(X),vol_R(V(R)\X)).     (1.1)
```

This is normalized **edge conductance**, not vertex expansion or a prescribed-demand routing hypothesis.

### Proposed global rank-absorption step GA — false

There is an absolute `K` with the following property. Suppose:

* `|U| >= 3` is odd, `W` is nonempty, and `R` is connected and bipartite on `U,W`;
* every `d_R(u)` is positive even and every `d_R(w)` is odd;
* `d_R(u) >= |W|/4`, `d_R(w) >= |U|/4`, and `Phi(R) >= 1/4`;
* `H` is disjoint from `U`, contains `W`, has odd vertices exactly `W`, and satisfies `sum_W d_H(w) <= 3|W|`.

Let `rho` be new and set

```
G = H union R,                 J = H + {rho w : w in W}.
```

Then the proposed conclusion is

```
c(G) <= c(J) + K (|U|-1).                               (GA)
```

Both graphs are simple and even. Connectedness of `R` implies that `R` and the new root join exactly the same components of `H` meeting `W`; other components are untouched. Therefore

```
kappa(G)=kappa(J),       r(G)-r(J)=|U|-1.                (1.2)
```

Had (GA) held, any sequence of eligible replacements, with its hypotheses checked in the current graphs, would have satisfied

```
c(G_0) <= c(G_t) + K sum_i (r(G_i)-r(G_(i+1)))
       = c(G_t) + K (r(G_0)-r(G_t)).                    (1.3)
```

This would be a genuinely single global rank ledger, with no new `n` at each level. A universal supply theorem would still be needed. Here the proposed **lifting step itself** fails, even for a one-step sequence and even when the best cap partition can be selected freely.

The constants `1/4` in GA are explicit test thresholds. The result below does not refute every possible stronger expansion or minimum-degree hypothesis.

## 2. The general obstruction: terminal-cut deficit amplifies through the exterior

### Lemma 2.1 — balanced terminal-cut amplification

Let `R` be a connected simple bipartite graph on `U,W`, with even degrees on `U` and odd degrees on `W`. Suppose `|W|=2b`, and there is a set `S subseteq U union W` such that

```
|S intersect W| = b,       tau = |delta_R(S)| < b.        (2.1)
```

For every integer `h >= 1`, there is an external graph `H_h` with odd vertices exactly `W` and `d_H(w)=1` at every terminal, such that, for `G_h=R union H_h` and `J_h=H_h+rho W`,

```
c(J_h) = b,
r(G_h)-r(J_h) = |U|-1,
c(G_h) >= b + h(b-tau)/2.                              (2.2)
```

In particular, no finite surcharge depending only on this fixed reservoir can make `c(G_h) <= c(J_h) + surcharge(R)` hold for every exterior.

**Construction.** Put `W_L=S intersect W` and `W_R=W\W_L`. Add new junctions `x_0,...,x_h`. For each segment `j=1,...,h`, join `x_(j-1)` to `x_j` by `b` internally disjoint paths of length two. All their internal vertices are private. Call each such length-two path a strand. Add one edge from every terminal in `W_L` to `x_0`, and one from every terminal in `W_R` to `x_h`. These strands and terminal arms are exactly `H_h`.

Each terminal has degree one in `H_h`; each junction has degree `2b`; each strand interior has degree two. Thus both `G_h` and `J_h` are even, simple, and connected, and the external average is one. Their orders differ by `|U|-1`, proving the rank identity.

The root has degree `2b`, so every simple-cycle partition of `J_h` has at least `b` cycles. Label the strands in each segment by `i=1,...,b`, and label the terminals on each side similarly. For each `i`, take

```
rho, w_(L,i), x_0, strand 1 of label i, x_1, ...,
      strand h of label i, x_h, w_(R,i), rho.
```

Here the strand notation means inserting its private interior vertex. These are `b` simple cycles. Each arm, strand edge, and root edge occurs exactly once. Hence `c(J_h)=b`.

**Lower bound for every partition of G_h.** Let `O` consist of `R` and the terminal arms, so `G_h` is the disjoint edge union of `O` and all the strands. In `O`, the cut `S union {x_0}` has exactly `tau` edges: none of the arms crosses it.

In any simple-cycle partition, a strand belongs entirely to one cycle, because its private vertex has degree two. A cycle using strands is of exactly one of the following two types:

1. A **local four-cycle**, consisting of two strands of one segment.
2. A **long cycle**, consisting of one strand in every segment and a simple `x_0-x_h` path in `O`.

Indeed, using two strands of the same segment already closes a four-cycle at its two junctions. Otherwise simplicity forces a cycle to continue through each intermediate junction to the next segment, all the way to both ends; its other part lies in `O`. This classification uses vertex simplicity and would not be valid for arbitrary closed trails.

Let `ell` be the number of long cycles. Every segment then has exactly `(b-ell)/2` local cycles. Let `t` be the number of cycles lying wholly in `O` and containing both end junctions. A long cycle uses at least one edge of the displayed cut in `O`; an `O`-only cycle through both ends uses at least two. Edge-disjointness gives

```
ell + 2t <= tau.                                      (2.3)
```

Of the `b` arm edges at `x_0`, exactly `ell` are used by long cycles. Each remaining cycle through `x_0` uses two arms. Thus exactly `(b-ell)/2` `O`-only cycles contain `x_0`, and the same count holds at `x_h`. Consequently there are at least `b-ell-t` `O`-only cycles in total, including any additional cycles containing neither end only as an extra nonnegative contribution. Therefore every partition has at least

```
ell + h(b-ell)/2 + b-ell-t
 >= b + [h(b-ell)-(tau-ell)]/2
  = b + h(b-tau)/2 + (h-1)(tau-ell)/2
 >= b + h(b-tau)/2                                    (2.4)
```

cycles. This proves (2.2). Finally, the parity identity

```
tau = sum_(v in S) d_R(v)  (mod 2) = b  (mod 2)
```

shows that a positive deficit `b-tau` is at least two. Letting `h` grow proves the unbounded-surcharge assertion. ∎

### A direct signed-edge certificate for the same lower bound

The lower bound also has a short independently checkable certificate. Assign weight `1/4` to each strand edge, `1/2` to each terminal arm, `-h/2` to each edge of `delta_R(S)`, and zero to all other reservoir edges. Every simple cycle has weight at most one:

* a local four-cycle has weight exactly one;
* a long cycle has weight at most `h/2 + 1 - h/2 = 1`;
* an `O`-only cycle meeting neither end has weight at most zero;
* one meeting exactly one end has weight at most one;
* one meeting both ends uses four arms and at least two cut edges, so its weight is at most `2-h <= 1`.

The total edge weight is `hb/2 + b - h*tau/2`. Summing the weights over any exact cycle partition proves the same lower bound `b+h(b-tau)/2`. This is a direct lower-bound argument with signed weights, not a fractional-to-integral rounding assertion. The attaining partition in Section 4 has weight exactly one on every output cycle.

This is a **necessary condition** for context-uniform retirement: every balanced terminal cut of such a reservoir must have capacity at least the number of terminals on one side. Positive normalized conductance alone is not that condition. No sufficiency claim for this cut condition is made.

## 3. One connected, expanding, parity-correct reservoir family

For `k >= 1`, let

```
U = {u_L,u_R,u_0},
W_L = A_L disjoint_union B_L,     |A_L|=6k, |B_L|=2k,
W_R = A_R disjoint_union B_R,     |A_R|=6k, |B_R|=2k.
```

The four terminal sets are disjoint. Define `R_k` by:

* each vertex of `A_L` is adjacent only to `u_L`;
* each vertex of `A_R` is adjacent only to `u_R`;
* every vertex of `B_L union B_R` is adjacent to all three vertices of `U`.

There are no other reservoir edges. Direct counts give

```
|U|=3,  |W|=16k,  |V(R_k)|=16k+3,  |E(R_k)|=24k,
d_R(u_L)=d_R(u_R)=10k,             d_R(u_0)=4k,
d_R(w)=1 on A_L union A_R,         d_R(w)=3 on B_L union B_R.
                                                               (3.1)
```

The reservoir is connected. Its rows are even and its columns odd. Its bipartite density is `1/2`, and

```
min_(u in U) d_R(u)/|W| = 1/4,
min_(w in W) d_R(w)/|U| = 1/3.                         (3.2)
```

### Proposition 3.1 — exact conductance

`Phi(R_k)=1/4` for every `k >= 1`.

**Proof.** For any cut, choose the side `X` containing at most one of the three vertices of `U`. It suffices to prove `|delta(X)| >= vol(X)/4`, whether or not this is the smaller-volume side.

If `X` contains no vertex of `U`, every incident edge leaves it, so `|delta(X)|=vol(X)`.

If its sole such vertex is `u_0`, let `x` be the number of included `B` terminals and `a` the number of included `A` terminals. Then

```
vol(X)=4k+3x+a,          |delta(X)|=4k+x+a,
4|delta(X)|-vol(X)=12k+x+3a >= 0.
```

If its sole such vertex is `u_L`, let `l` be the number of excluded `A_L` terminals, `y` the number of included `A_R` terminals, and `x` the number of included `B` terminals. Then

```
vol(X)=16k-l+y+3x,       |delta(X)|=4k+l+y+x,
4|delta(X)|-vol(X)=5l+3y+x >= 0.
```

The `u_R` case is symmetric. This proves the lower bound. For `X={u_L} union A_L`, the boundary has size `4k`, the volume is `16k`, and the complementary volume is `32k`. Its conductance is `1/4`, proving equality. ∎

On the other hand, take

```
S = {u_L} union W_L.
```

It contains exactly `b=8k` terminals. Its crossing edges are the `4k` edges from `B_L` to `u_R,u_0` and the `2k` edges from `B_R` to `u_L`. Hence

```
tau=6k,                b-tau=2k.                       (3.3)
```

This is precisely the terminal-cut deficit in Lemma 2.1. Notice that the obstruction is not disconnectedness, a wrong parity, or a fixed bad route choice.

## 4. Exact optimal partitions: reconstruction and every-edge account

Apply Lemma 2.1 to `R_k`, with `b=8k`, and write the resulting graphs as `G_(k,h)` and `J_(k,h)`. The lemma already proves

```
c(G_(k,h)) >= 8k+kh,       c(J_(k,h))=8k.               (4.1)
```

Here is a partition attaining the first bound.

Index `A_L,A_R` by `0,...,6k-1` and `B_L,B_R` by `0,...,2k-1`. The outside graph `O=R_k + terminal arms` has the following `6k` edge-disjoint simple `x_0-x_h` paths: for `i=0,...,2k-1`, take

```
Q_(1,i) = (x_0, A_(L,i), u_L, B_(R,i), x_h),
Q_(2,i) = (x_0, B_(L,i), u_R, A_(R,i), x_h),
Q_(3,i) = (x_0, A_(L,2k+i), u_L, B_(L,i), u_0,
                  B_(R,i), u_R, A_(R,2k+i), x_h).       (4.2)
```

All three hubs appearing in `Q_(3,i)` are distinct, and all displayed terminal classes are disjoint, so these are vertex-simple paths. Their edge sets are disjoint even though different paths share hubs and some terminals. Each path crosses the cut in (3.3) exactly once; together they exhaust that cut.

At each `B_L` terminal, its arm and `u_R` edge are used by `Q_2`, and its `u_L,u_0` edges by `Q_3`. At each `B_R` terminal, its arm and `u_L` edge are used by `Q_1`, and its `u_0,u_R` edges by `Q_3`. All `u_0` edges are thus used. Exactly the first `4k` terminals in each `A` class have both their edges used. The remaining edges of `O` are exactly two copies of `K_(2,2k)`, with poles `x_0,u_L` and `x_h,u_R`, respectively. They partition into the following `2k` four-cycles, for `j=0,...,k-1`:

```
(x_0, A_(L,4k+2j), u_L, A_(L,4k+2j+1)),
(x_h, A_(R,4k+2j), u_R, A_(R,4k+2j+1)).                 (4.3)
```

Now use `6k` of the `8k` strands in each segment to form `6k` simple `x_0-x_h` chain paths, one fixed strand label per path. Pair them bijectively with (4.2). A chain path and its own `Q` have exactly their two endpoints in common and have disjoint edges. Their union is therefore an actual simple cycle, not merely an Eulerian trail. Different resulting cycles can share vertices, but not edges.

In each segment, pair the remaining `2k` strands into `k` local four-cycles. Retain all cycles in (4.3). Thus the output consists of

```
6k long cycles + kh local four-cycles + 2k outside four-cycles
= 8k+kh cycles.                                        (4.4)
```

The three edge accounts exhaust `O` and all strands without overlap. As a further numerical check, the long cycles have lengths `2h+4` (there are `4k`) and `2h+8` (there are `2k`). The edge total is

```
4k(2h+4) + 2k(2h+8) + 4kh + 8k
= 16kh+40k = |E(G_(k,h))|.                             (4.5)
```

Together with the lower bound, this proves the exact values in (0.1). The complete order and edge counts are

```
|V(G)|=(8k+1)h+16k+4,       |E(G)|=16kh+40k,
|V(J)|=(8k+1)h+16k+2,       |E(J)|=16kh+32k.            (4.6)
```

Both graphs are connected, so their graphic ranks differ by two.

Finally, the original degree share of the reservoir is independent of `h`. Each of its three hubs contributes one. The `12k` terminals in the `A` classes have reservoir/ambient degree ratio `1/2`; the `4k` terminals in the `B` classes have ratio `3/4`. Hence

```
W_G(R_k)=3+12k/2+3(4k)/4=9k+3.                         (4.7)
```

## 5. Consequences and limits of the obstruction

Fix `k=1`. The reservoir now has just 19 vertices and 24 edges and is unchanged as `h` grows. All hypotheses of GA hold, with external average one, but

```
c(G_(1,h))-c(J_(1,h))=h,
r(G_(1,h))-r(J_(1,h))=2,        W_G(R_1)=12.             (5.1)
```

Choosing an integer `h>2K` disproves GA for any proposed finite `K`. More generally, no finite function of this fixed reservoir's order, size, rank deletion, degree share, or conductance can bound its surcharge independently of the exterior. Allowing an additive constant depending on the reservoir does not repair the statement.

For this fixed 19-vertex reservoir, even the ordinary local-order inequality `delta(R_1) >= |V(R_1)|/19` holds. Thus adding that particular fixed dense-minimum-degree hypothesis would not rescue GA. The CFS dense theorem is not misapplied here: its `O(alpha^-12 |V(R)|)` cycle/singleton-edge partition of `R` does **not** supply a compatible absorption into arbitrary cap paths. Nor does it apply to all of `G_(1,h)` at a fixed positive minimum-degree/order ratio as `h` grows.

The obstruction survives optimizing over **all** cap and output partitions. It is not an assertion that one prescribed reservoir routing is expensive: (2.4) bounds every simple-cycle partition of the full graph. In particular a matching-preserving randomization cannot repair the missing cut capacity.

The rank identity (1.3) remains valid accounting, but cannot manufacture a valid local price. A single defective retirement already has unbounded surcharge; nesting these same steps does not repair it. Similarly, charging only the edges of `R_k` on the once-only original-degree ledger cannot pay (5.1). One must either avoid this retirement or permit an outside-spanning open packet and justify its additional charge globally.

These conclusions have deliberately limited scope:

* They do not exclude stronger terminal-routing hypotheses or specially chosen reservoirs.
* They do not refute a supply theorem restricted to suitably reduced minimum counterexamples. This family contains many degree-two vertices and is not alleged to be such a counterexample.
* They do not refute arbitrary simultaneous reopening that charges outside edges or vertices exactly once.
* They do not supply that reopening theorem or a universal eligible-module theorem.

Indeed, `c(G_(k,h)) < |V(G_(k,h))|/2` follows directly from (4.4) and (4.6). No assertion about arbitrary graphs follows from this family's inexpensive partitions.

The investigation stops at this precise failure, rather than changing to a different unproved universal claim. **We still have no universal C and no complete paper proof of Erdős–Gallai.**

## 6. Verification and protected files

Run the self-contained, standard-library checker with

```
PYTHONDONTWRITEBYTECODE=1 python3 Submission/ResearchGlobalAbsorptionCheck.py
```

It writes no files. It verifies simplicity, parity, connectivity, the external degrees, both exact edge partitions, the path and cut certificates, ranks, original degree shares, and the counting-ledger algebra. It also exhausts every nontrivial cut of `R_1` to check its conductance independently, and checks the signed lower certificate's total and tightness on every output cycle.

Executed successfully:

* **53** parameter pairs, with exact partitions of both `G` and `J` and all the stated structural and numerical certificates;
* all **524286** nontrivial cuts of `R_1`, confirming conductance exactly `1/4`;
* among them, all **102960** balanced-terminal cuts, whose minimum size is six;
* **55488** feasible integer-ledger cases checking the lower-bound arithmetic;
* preservation of all **46** pre-existing `Submission` files, including the specification.

For example, the fixed-reservoir stress check `k=1,h=1000` has `9020` vertices and `16040` edges, with certified counts `1008` and `8`, removed rank two, and reservoir share twelve. These finite checks audit the constructions and formulas; the proofs above, for arbitrary `h`, establish the obstruction. The checker does not claim that finite testing proves an optimality theorem or settles Erdős–Gallai.

The only newly written files are this note and `Submission/ResearchGlobalAbsorptionCheck.py`. The checker verifies the original 46-file `Submission` baseline, excluding these two additions:

```
aggregate SHA-256: 2533c9865919368f7c1601baab8a11a9e77ea5bdee6b9b1c86f6e97b7e014c4d
Spec.lean SHA-256: 429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

Inputs read were the concise statements in `ResearchPackets.md`, `ResearchRetirement.md`, `ResearchInterfaces.md`, `ResearchReservoirExtension.md`, and `ResearchFactors.md`. In particular the actual-simple-cycle requirement from the interface ledger and the precise average-three rank hypothesis from the odd-twin extension are preserved. No ordinary cover, fractional partition, trail partition, or 2-factor count is substituted for a simple-cycle edge partition. The results here are paper proofs, not Lean formalizations or claims of literature priority.
