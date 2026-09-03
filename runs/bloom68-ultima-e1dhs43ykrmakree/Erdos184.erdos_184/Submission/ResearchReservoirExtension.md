# Integral reservoir expansion with terminal collisions

## Status and results

**The proposed concrete integral lemma is valid. This note does not prove Erdős–Gallai, a universal linear cycle bound, or a universal odd-cover rounding bound.** The arguments are paper proofs, not Lean formalizations. The accompanying `ResearchReservoirExtension.py` checks constructions and finite cases using exact arithmetic.

The main conclusions are:

1. If `b` edge-disjoint simple real paths have endpoint pairs partitioning `W`, `|W|=2b`, and avoid a new independent reservoir `U` of odd size `s=2a+1`, then their exact union with `K_(U,W)` has a simple-cycle edge partition of size at most

   ```
   b + delta + floor(t L/(2b-2)),             b>=2,            (A)
   delta=max(0,a+1-b),   t=min(s-1,2b-2),
   L=sum_i |int(P_i) intersect W|.
   ```

   For `b=1` the answer is exactly `1+delta=1+a`. Arbitrary internal sharing between different real paths, including visits to other paths' endpoints, is permitted. The randomization is **one global matching-preserving relabeling**, not independent routing.

2. For an arbitrary finite simple `H` with odd degrees on `W` and even degrees elsewhere, put

   ```
   J=H+rho W,                  R_s=H+K_(U,W),
   h_w=(d_H(w)-1)/2,
   D_b(H)=sum_(w in W) min(h_w,b-1),
   q=s-1=2a.
   ```

   A useful general, degree-profile-dependent price is

   ```
   c(R_s) <= c(J)+B_s(H),
   B_s(H) = a,                                                   b=1,
   B_s(H) = min{ max(a,b),
                  delta + floor(t D_b(H)/(2b-2)) },              b>=2.   (B)
   ```

   The first term in the minimum comes from retaining one twin as the old root and factoring the remaining complete even bipartite graph. The second is the collision bound. A partition-specific version replaces `D_b(H)` by its actual `L`.

3. Under the **average**, not maximum, condition `sum_W d_H(w)<=3|W|`,

   ```
   B_s(H) <= q + 1_{b=s and D_b(H)=2b} <= q+1=s <= (3/2)q.       (C)
   ```

   Thus the requested surcharge `2(s-1)` is valid and can be strengthened to `(3/2)(s-1)`. The surcharge is at most `s-1` whenever `b!=s`; in particular the requested improvement for `b>=s+1` holds. At `b=s` it is also at most `s-1` if `D_b(H)<=2b-1`, or if the chosen cap partition has `L<=2b-1`.

4. Eligible odd-twin contractions decrease graphic rank by exactly `s-1`. Repetition pays at most `(3/2)` times the **total deleted rank**, under the average-three condition. A minimum-rank counterexample to `c(G)<=C r(G)` for any `C>=3/2`, and hence any `C>=2`, cannot contain such a reservoir. This statement concerns the **pure rank bound**; it does not preserve a supplied odd cover, an odd-cover minimum, or a fractional gap.

5. There is an unconditional near-twin extension for a complete common neighborhood plus an **even surplus-edge graph** with an explicit cheap cycle partition. There is no general missing-edge or density-only extension here. In fact, deleting one four-cycle from a complete reservoir can increase the minimum cycle-partition number without bound. Near-complete density alone also does not guarantee routing a prescribed terminal matching.

Only `Submission/ResearchReservoirExtension.md` and `Submission/ResearchReservoirExtension.py` are written. `Spec.lean` and all pre-existing files are left unchanged.

---

## 1. Conventions and hypotheses

All graphs are finite, simple, and undirected. A cycle is vertex-simple and has length at least three. A path is vertex-simple with two distinct endpoints. An exact partition uses every edge once; sharing vertices between different pieces is unrestricted. Write

```
c(G) = minimum number of simple cycles in an exact edge partition of an even G,
r(G) = |V(G)|-kappa(G).
```

Here `kappa` counts all connected components, including isolated vertices. Every even graph has a simple-cycle partition: remove a simple cycle repeatedly. No bound of the form `c(G)=O(r(G))` is assumed.

For (A), there are exactly `b>=1` real paths `P_1,...,P_b`. They are edge-disjoint, their endpoint pairs partition `W`, and `U` is disjoint from **every** real-path vertex. The graph being partitioned is exactly

```
F = (disjoint edge union of the P_i) union K_(U,W).
```

There are no implicit extra edges to be covered. The endpoints of one path may be internal vertices of another. Different real paths may share arbitrarily many other internal vertices. The word “path” cannot be weakened to a trail without an additional debt term.

The stated task assumes `s=2a+1>=3`. The construction also works for `s=1`, but the contraction then deletes no rank. An empty terminal set `b=0` is excluded: isolated twins do not yield the claimed strict rank reduction.

## 2. The uniform-length complete bipartite factorization

This is the construction in `ResearchOddCancellation.md`, Lemmas 2.1–2.2, with its length information made explicit.

### Lemma 2.1

For positive integers `p,z`, `K_(2p,2z)` has an exact partition into `max(p,z)` simple cycles, all of length `4 min(p,z)`.

**Proof.** Interchange the sides if necessary so that `p<=z`. Split the smaller side into `X_0,X_1`, each indexed by `j=0,...,p-1`, and the larger into `Y_0,Y_1`, indexed by `Z_z`. For each `i in Z_z`, concatenate and close

```
X_(0,j), Y_(0,i+j), X_(1,j), Y_(1,i+j),     j=0,...,p-1.       (2.1)
```

The indices within either `Y` class are distinct, and every `X` vertex is used once. At `X_(1,j)`, the two neighbors are `Y_(0,i+j)` and `Y_(1,i+j)`. At `X_(0,j)`, the successor is `Y_(0,i+j)` and the predecessor is `Y_(1,i+j-1)` for `j>0`, or `Y_(1,i+p-1)` for `j=0`. As `i` varies, each of these neighbor lists runs through its entire class exactly once. Thus every bipartite edge occurs once. ∎

### Lemma 2.2 — matching routes with a uniform number of internal terminals

For any perfect matching `M` on `W`, the reservoir has an exact partition into `b` simple paths `Q_i` with endpoint matching `M` and `delta` simple cycles. Each route has exactly

```
t = 2 min(a+1,b)-2 = min(s-1,2b-2)
```

internal `W` vertices and `t+1` internal `U` vertices.

**Proof.** Apply Lemma 2.1 to `K_({rho} union U,W)`. Exactly `b` cycles use `rho`, because its degree is `2b` and each simple cycle uses two root edges. Each such cycle contains `2 min(a+1,b)` vertices of `W`. Deleting the root opens it into a simple route with two endpoints in `W`, hence `t` internal `W` vertices. The remaining

```
max(a+1,b)-b = delta
```

cycles avoid the root. Every `W` vertex is an endpoint exactly once because its root edge was used once. Relabel all of `W` by a bijection sending this endpoint matching to `M`, including in every remaining cycle. Completeness of the reservoir preserves the entire exact edge partition. ∎

Also, every terminal occurs internally in exactly `t/2=min(a,b-1)` routes. If `delta=0`, its degree equation is `s=1+2*(internal route occurrences)`. If `delta>0`, every route visits all nonendpoint terminals, so the number is `b-1`. This observation is not needed for the expectation but illustrates why independent route choices would be unjustified.

## 3. One global randomization and the exact collision budget

Fix the endpoint matching, with ordered pairs `M_i=(x_i,y_i)`, and fix the partition from Lemma 2.2. Let `Gamma` be the group of all permutations of the `b` pairs and all independent flips **within those pairs**. Its order is `b! 2^b`.

Choose one `g` uniformly in `Gamma`, relabel the **whole reservoir partition** by `g`, and then reindex its paths by their new endpoint pair. Reverse a route if necessary to align its orientation with `P_i`. Call the resulting path paired with `P_i` again `Q_i`. Every outcome is a valid exact reservoir partition with the required matching.

For fixed `i`, the subgroup stabilizing the pair `M_i` is transitive on `W\M_i`: it can permute all other pairs and flip their endpoints. The law of the reindexed `Q_i` is invariant under this subgroup. Its internal-terminal set has size exactly `t`. Consequently, for every `w notin M_i`,

```
Pr(w in int(Q_i)) = t/(2b-2),                 b>=2.           (3.1)
```

The reindexing is essential. Keeping the old route indices after permuting pairs would not produce the paths that close the fixed real paths.

Set

```
I_i = |int(P_i) intersect int(Q_i)|
    = |int(P_i) intersect W intersect int(Q_i)|,
I   = sum_i I_i.
```

Since a real path cannot contain either of its own endpoints internally, linearity of expectation gives

```
E[I] = t L/(2b-2).                                           (3.2)
```

No joint probability or independent-routing assertion occurs. The nonnegative integer `I` therefore has an outcome with

```
I <= floor(t L/(2b-2)).                                      (3.3)
```

For example, if `s=3,b=3`, each terminal occurs internally in exactly one of the two routes for which it is not an endpoint. Those two events are mutually exclusive, not independent.

## 4. Repairing each real path plus its own route

### Lemma 4.1 — the correct nullity bound

`P_i union Q_i` is a connected even simple graph, and its cycle-space dimension is exactly `1+I_i`.

**Proof.** The real and reservoir edge sets are disjoint because every reservoir edge has an endpoint in the new set `U`. The common vertices of the two paths are exactly their two endpoints and the `I_i` internal intersections. Thus

```
|E(P_i union Q_i)| = (|V(P_i)|-1)+(|V(Q_i)|-1),
|V(P_i union Q_i)| = |V(P_i)|+|V(Q_i)|-2-I_i,
beta(P_i union Q_i) = |E|-|V|+1 = 1+I_i.                     (4.1)
```

The endpoints have degree two, internal common vertices have degree four, and all other vertices have degree two. This proves connectedness and evenness as well. ∎

Every simple-cycle edge partition of a graph has at most its cycle-space dimension: the incidence vectors over `F_2` of edge-disjoint nonempty cycles are linearly independent. In particular a greedy cycle-removal partition of this piece has at most `1+I_i` cycles. This proves an **upper**, not a lower, bound on the required repair. The cycle-space formula is elementary and does not assume a universal cycle-decomposition conjecture.

Different pieces `P_i union Q_i` can share vertices, but never edges. They can therefore be repaired separately after the global routing has been selected. Retain the `delta` reservoir-only cycles. Their exact combined partition has at most

```
sum_i(1+I_i)+delta <= b+delta+floor(t L/(2b-2)),
```

proving (A).

If `b=1`, there are no nonendpoint terminals. The sole route has length two and has no internal vertex on the real path. Their union is one simple cycle. There are `a=delta` further reservoir cycles. Both terminals have degree `s+1=2a+2` in this exact union, so every partition needs at least `a+1` cycles. This proves the separate exact value, with no division by zero.

## 5. Constructive derandomization

Exhaustive search of the finite group is already a constructive existence proof. There is also a polynomial-time conditional-expectation implementation, used by the checker.

Use the ordered matching pairs as coordinates. Define two `b by b` matrices with zero diagonal:

```
A[i,k] = number of endpoints of M_k in int(P_i),
T[j,k] = number of endpoints of M_k in the fixed int(Q_j).
```

Their entries are in `{0,1,2}`, `sum A=L`, and each row of `T` has sum `t`. If `pi` is the permutation of pairs, then, averaging over all endpoint flips,

```
E_flips[I | pi] = (1/2) sum_(j!=k) T[j,k] A[pi(j),pi(k)].    (5.1)
```

For a partially assigned permutation, let `R` be the unused target pairs and `m=|R|`. Each matrix entry on the right is replaced by:

* `A[pi(j),pi(k)]` if both images are fixed;
* `sum_(v in R) A[pi(j),v]/m` if only the first is fixed;
* `sum_(u in R) A[u,pi(k)]/m` if only the second is fixed;
* `sum_(u!=v in R) A[u,v]/(m(m-1))` if neither is fixed.

The last case only occurs when `m>=2`. At each step choose the next image minimizing this exact conditional expectation. The average of the available choices is the current expectation, so this never increases it. Initially (5.1) averages to `tL/(2b-2)`.

After fixing `pi`, the score is a sum of separate **decision costs** for the endpoint flips, one for each source pair: a flip only changes the labels of that pair's terminals, not the route-to-real-path assignment. Choose the cheaper of its two values. This reduces or preserves the expectation over flips. The final integer score satisfies (3.3). This is an optimization over globally valid partitions, not independent sampling of routes. All calculations in the implementation use `Fraction` or integers.

## 6. Opening a cap partition and the terminal degree profile

Let `H` be as in (B), and let a partition of `J` have `N` cycles. Exactly `b` use the root. Delete the root from those cycles to obtain the `P_i`; retain the other `N-b` cycles of `H`.

For each terminal `w`, let

```
ell_w = number of opened paths containing w internally,
z_w   = number of retained root-free cycles containing w.
```

Exactly one opened path has `w` as an endpoint. Degree counting gives the exact identity

```
d_H(w) = 1+2 ell_w+2 z_w,
ell_w  = h_w-z_w <= min(h_w,b-1).                            (6.1)
```

The second bound uses simplicity of each of the other `b-1` paths, not a maximum-degree assumption. Hence

```
L=sum_w ell_w <= D_b(H) <= sum_w h_w
                       = (sum_w d_H(w)-2b)/2.                (6.2)
```

Apply (A) to the opened paths and then restore the root-free cycles. For `b>=2` this gives, for **every** initial partition,

```
output count <= N+delta+floor(t L/(2b-2))
             <= N+delta+floor(t D_b(H)/(2b-2)).                (6.3)
```

Taking a minimum initial partition proves the collision part of (B). A minimum is not needed to bound `L`: (6.1) holds for every partition.

There is a second unconditional expansion. Identify `rho` with one chosen `u_0 in U` and keep the entire original partition of `J`. The unused edges form exactly

```
K_(U\{u_0},W) = K_(2a,2b).
```

Lemma 2.1 partitions them into `max(a,b)` cycles. Thus

```
c(R_s) <= c(J)+max(a,b),                                    (6.4)
```

without **any** restriction on terminal degrees. Taking the cheaper of (6.3) and (6.4) proves (B). The checker implements both actual edge partitions and chooses the cheaper certified construction.

No reverse equality is asserted for general nonleaf terminals. Indeed Section 9 below has `b=1` examples with `c(J)-c(R_3)` arbitrarily large.

### 6.1 Useful general prices and sufficient degree conditions

For `b>=2`, put `alpha=D_b(H)/(2b-2)`. Since

```
delta=(q-t)/2,
```

the collision price is at most

```
q/2 + t(alpha-1/2) <= q max(1/2,alpha).                      (6.5)
```

Consequently, for any `C>=1/2`, either of the following is a sufficient certificate for a surcharge at most `Cq`:

```
D_b(H) <= C(2b-2),                 or                 b<=Cq. (6.6)
```

The second uses (6.4). The exact floor in (B) can certify further cases. For `b=1` the surcharge is always `q/2`.

In particular, `D_b(H)<=2b-2` guarantees surcharge at most `s-1` for **all** `s`. This capped profile can be much smaller than total terminal excess when the degree distribution is unbalanced.

For another coarse general form, set `hbar=D_b(H)/(2b)`. Combining the two constructions gives

```
B_s(H) <= max{a, floor(q hbar)+1}.                           (6.7)
```

To check it, if `b<=a` use (6.4). Otherwise `delta=0,t=q`, and the two prices are `b` and `floor(x b/(b-1))`, where `x=q hbar`. If `b<=floor(x)+1`, use the first; otherwise `x/(b-1)<1`, and the second is at most `floor(x)+1`. The `b=1` case also satisfies (6.7). If the external average degree is at most a real `d>=1`, then `hbar<=(d-1)/2`, so

```
B_s(H) <= max{a, floor(q(d-1)/2)+1} <= (d/2)q.                (6.8)
```

The last inequality uses `q>=2`, so the additive one is at most `q/2`. These are proven general bounded-average-degree prices; their sharpness for minimum cycle counts is not claimed.

### 6.2 An explicitly unbalanced example

Start `H` with a matching on `W`. At one terminal `w_*`, attach `2b` edge-disjoint triangles, with all their other vertices new and private. Then

```
d_H(w_*)=4b+1,    d_H(w)=1 for w!=w_*,
sum_W d_H(w)=6b=3|W|,
D_b(H)=b-1  (b>=2).
```

The maximum degree is unbounded. Nevertheless this satisfies the requested average-three condition and the stronger `C=1/2` profile certificate in (6.6). In its natural minimum cap partition the attached triangles are root-free, so `L=0`, and the actual collision price is just `delta`. This also illustrates why root-free terminal passages must not be counted in `L`.

## 7. The average-three condition: checking every parameter range

Suppose `sum_W d_H(w)<=6b`. Equation (6.2) gives `D_b(H)<=2b`. Let `q=s-1>=2`.

* If `b<=q`, the root-retaining price is `max(q/2,b)<=q`. This includes `b=1` and every very large-reservoir regime.
* If `b>=q+2=s+1`, then `delta=0,t=q`, and

  ```
  floor(q D_b(H)/(2b-2)) <= floor(q b/(b-1))
                         = q+floor(q/(b-1)) = q.             (7.1)
  ```

* The only remaining case is `b=q+1=s`. Here the root-retaining price is `b=q+1`, and the collision price is `floor(D_b(H)/2)<=b`. If `D_b(H)<=2b-1`, that price is at most `b-1=q`. The same improvement holds using the actual `L<=2b-1` of a chosen partition.

This proves (C), including all small and boundary cases. Since `q>=2`,

```
q+1 <= (3/2)q <= 2q.                                       (7.2)
```

Even the collision construction alone proves the user's `2q` claim: for `b>=2` its price is at most `s+1=q+2<=2q`. Indeed in the unsaturated regime it is `<=q+floor(q/(b-1))<=q+2`, and in the saturated regime it is `<=a+1+b<=2a+2=q+2`. The `b=1` price is `a`. Combining with (6.4) is the genuine improvement.

The exceptional `q+1` in (C) is a bound on these constructions, **not** a proved necessary increase of `c`. One cannot simply turn the expectation into a strict inequality. For the displayed four-layer factorization when `b=s` is odd, every route contains exactly one endpoint from each other matching pair. This follows by writing its endpoint pair as `(Y_(0,i),Y_(1,i+a))`: its internal terminal pair indices are `i+1,...,i+a` and `i-a,...,i-1`, which exhaust all other pairs when `b=2a+1`.

Choose real `P_i` to visit both endpoints of pair `i+1` internally and no other internal terminals; use private subdivisions to ensure all real edges are distinct. Then `L=2b`, all terminals have external degree three, and **every global pair permutation and flip of this template** has `I_i=1`, hence `I=b`. The nullity repair of each such piece is exactly two cycles. This is an obstruction to a strict-averaging shortcut within this template, not to alternative factorizations or globally better partitions of `R_s`.

For clarity, at `b=s=3` this very graph has a different three-cycle partition, not six. With indices modulo three, matching pairs `(x_i,y_i)`, and reservoir vertices `u_0,u_1,u_2`, use routes

```
x_i, u_0, y_(i-1), u_1, x_(i-1), u_2, y_i.                 (7.3)
```

At `x_i`, the endpoint route uses `u_0`, and its internal occurrence in route `i+1` uses `u_1,u_2`; at `y_i` the roles are `u_2` and `u_0,u_1`. Thus these three paths partition every reservoir edge. Their internal terminal pair `i-1` is disjoint from the real path's internal pair `i+1`. All three unions are simple cycles, and the degree-six root and degree-six reservoir vertices prove `c(J)=c(R_3)=3`. This explicit comparison prevents interpreting the certified `3/2` coefficient as a sharp obstruction for the underlying graphs.

## 8. Odd twins and one telescoping rank ledger

An eligible average-three odd reservoir in a finite simple even graph `G` is an independent set `U` of odd size `s>=3`, whose vertices have the same nonempty neighborhood `W`, such that

```
sum_(w in W) d_(G-U)(w) <= 3|W|.                            (8.1)
```

Each twin has even degree, so `|W|=2b`. Each terminal has odd external degree because `G` is even and `s` is odd. Every other external vertex has even degree. Thus `H=G-U` satisfies exactly the hypotheses above.

Delete `U` and add one new root adjacent to `W`, obtaining `J`. It is simple and even. In both graphs all `H`-components meeting `W` are joined into one component, and all other components, including isolates, are untouched. Therefore

```
kappa(G)=kappa(J),       r(G)-r(J)=s-1=q>0.                  (8.2)
```

Apply (B) or (C), and repeat any such contractions until no eligible set remains. If the final graph is `K`, then

```
c(G) <= c(K)+sum_i B_i
     <= c(K)+(3/2) sum_i(s_i-1)
      = c(K)+(3/2)(r(G)-r(K)).                              (8.3)
```

Every partition of `K` lifts; each step's average condition concerns its **current** graph. The account is deleted rank, not a refreshed original-order budget at each step. For sequences satisfying the stronger certificates in (6.6), replace `3/2` by their common coefficient `C>=1/2`.

If there is a counterexample to `c(G)<=C r(G)` for a fixed `C>=3/2`, select one of minimum rank. An eligible contraction gives a smaller-rank `J`, which by minimality satisfies `c(J)<=C r(J)`. Equations (8.2)–(8.3) then imply `c(G)<=C r(G)`, a contradiction. Thus such a minimum-rank counterexample contains no eligible reservoir. In particular the user's statement for `C>=2` is valid **with this pure rank interpretation**.

This inference must not be applied unchanged to `c(G)<=k+C r(G)` for a supplied odd cover, or to `c(G)-o(G)<=C r(G)`: contraction need not preserve or cheaply transport `k` or `o`. `ResearchOddCancellation.md`, Section 5, has leaf-port examples with odd-cover minimum increasing by `(b-1)^2` while only `2b-2` rank is removed. They are a subclass of the reservoirs here. No fractional equality or fractional-gap monotonicity is claimed in the present nonleaf setting either.

## 9. A rigorous near-twin extension, and two limitations

### 9.1 Even surplus edges: an unconditional certificate

Suppose `G` is simple and even on the vertex set of a spanning subgraph `R_s` of the form above, and

```
E(G)=E(R_s) disjoint-union E(F),
```

where `F` is even and a partition of `F` into `f` simple cycles is given or constructed. Then

```
c(G) <= c(J)+B_s(H)+f.                                     (9.1)
```

This follows by taking the disjoint edge union of the two actual partitions; it assumes no conjectural bound for `F`.

A concrete near-twin case has `U` still independent, complete to a common even nonempty neighborhood `W`, and all its additional edges going to `Z=V(H)\W`. Let `F` consist of these surplus `U-Z` edges, and require **even degree at every vertex of F**. This is a checkable parity hypothesis, not a consequence of closeness of the neighborhoods. Removing `F` leaves exactly the even complete-reservoir graph. A greedy partition of the simple bipartite even `F` gives

```
f <= min{ floor(|E(F)|/4), beta(F) },                         (9.2)
```

where `beta(F)=|E(F)|-|V(F)|+kappa(F)`; isolates cancel in this formula. Both inequalities hold for any simple-cycle partition of `F`.

The added error edges may merge components. With `J` built from the spanning `R_s`,

```
r(G)-r(J) = q+kappa(J)-kappa(G) >= q.                        (9.3)
```

Consequently the precise retirement test is

```
B_s(H)+f <= C [q+kappa(J)-kappa(G)].                         (9.4)
```

Such steps telescope in deleted rank just like (8.3). For a particularly simple numerical sufficient condition, if the external average on `W` is at most three and

```
|E(F)| <= 2q,
```

then (C) and (9.2) give `B_s(H)+f<=(3/2)q+q/2=2q`. Hence these parity-preserving surplus near-twins are also excluded from minimum-rank counterexamples to the pure bound with `C>=2`. If `b!=s`, the improved base price `q` permits up to `4q` surplus edges by the same argument. More generally an explicitly known partition of `F` can be much cheaper than (9.2).

This is a sufficient local theorem, not a claim that arbitrary near-twins admit the required even error split. For nonbipartite even errors one may use `floor(|E(F)|/3)` instead, but must first exhibit an exact complete-reservoir spanning subgraph and the even edge complement.

### 9.2 Completing missing edges and deleting them is not a cheap repair rule

For any `h>=1`, take junctions `v_0,...,v_h`. Between `v_(j-1)` and `v_j` put three internally disjoint length-two paths, with all branch interiors private. Call the resulting chain `H_h`; its two end terminals `W={v_0,v_h}` have degree three, its intermediate junctions degree six, and other vertices degree two.

Let `J_h` add one root adjacent to both end terminals. Every partition has exactly one cycle through this degree-two root. That cycle uses one branch in every segment. The remaining two branches in each segment form one four-cycle, and the junction cuts prevent a cycle of `H_h` from spanning multiple segments. Thus

```
c(J_h)=h+1.                                                (9.5)
```

Let `R_h` replace the root by three independent twins complete to `W`. There is a partition into three long simple cycles, one for each branch choice and one twin. Terminal degree six gives the matching lower bound:

```
c(R_h)=3.                                                  (9.6)
```

The four edges on the two twins other than the retained root form a single four-cycle `F_h`. Deleting them leaves `J_h` and two isolated vertices. Therefore

```
|E(F_h)|=4,       c(R_h-F_h)-c(R_h)=h-2.                    (9.7)
```

The increase is unbounded although the deleted graph is even and lies entirely in a complete reservoir satisfying the average-three hypothesis. Hence there is no universal repair estimate `c(X-F)<=c(X)+f(|E(F)|)` with finite `f(4)` even in these instances. This rules out a naive “complete, decompose, then delete the holes” proof. It does **not** refute an independently constructed near-twin theorem relative to the right smaller graph; here that graph is already `J_h`.

### 9.3 Density alone does not furnish prescribed routes or eligible retirements

For odd `s>=5` and `b>=3`, split the reservoir side into sizes `s-2,1,1` and the terminal side into sizes `2b-4,2,2`. Take only the three corresponding complete bipartite blocks. All reservoir degrees are positive even, and all terminal degrees are odd. Its density inside `K_(s,2b)` is

```
[(s-2)(2b-4)+4]/(2bs) = 1-(4s+4b-12)/(2bs),                (9.8)
```

which tends to one as `s,b` grow. But any matching with a pair in different components cannot be routed at all. Thus total near-completeness and the correct parity do not supply the arbitrary-matching routing used in Section 3. This example does not impose a large minimum relative degree on every row and column, nor does it refute a stronger theorem with such hypotheses.

Even a dense even graph need not contain an independent triple: `K_(2m+1)` has none. So density does not imply the exact or even-surplus independent-twin certificate. This is not a cycle-decomposition obstruction for complete graphs; it is just a failure of the proposed local extraction implication. The more general overlap/density-retirement issue in `ResearchRetirement.md` is not resolved by adding these local certificates.

A missing-edge extension would need a new exact routing/repair theorem respecting the prescribed endpoint matching, parity, terminal intersections, and one global cost account. A density retirement extension would need a proved supply of suitably priced pieces, or a separate theorem for the remaining core. Neither is assumed here.

## 10. Verification and reproducibility

Run from the project root:

```
PYTHONDONTWRITEBYTECODE=1 PYTHONHASHSEED=0 \
  python3 Submission/ResearchReservoirExtension.py
```

The script uses Python 3, NetworkX, integer edge multiplicities, and `fractions.Fraction`; no optimizer, floating-point tolerance, or random experiment is used. It writes only a JSON summary to stdout. It independently validates simplicity and exact edge exhaustion of all produced partitions, including alternative root-retaining partitions. Its tests cover:

* both orientations and the equality case of the complete bipartite factorization;
* prescribed matching routes, including `b=1` and both reservoir-size regimes;
* exhaustive matching-preserving global relabelings in small cases, checking exact marginals and nonindependence;
* conditional-expectation derandomization, with arbitrary internal terminal visits and shared nonterminal vertices;
* opening and lifting partitions of even atlas graphs, with disconnected and isolated-vertex cases included;
* degree-profile and floor inequalities across broad integer ranges;
* very unbalanced terminal degrees satisfying the average-three hypothesis;
* a repeated contraction/lifting ledger and the even-surplus extension;
* exact constructions and lower-bound certificates for the four-edge deletion obstruction;
* the density-only routing obstruction and the constant-intersection template example.

The all-parameter assertions rest on the proofs above, not on these finite tests. The completed run (Python 3.11.2, NetworkX 2.8.8; about 14 seconds here) returned `all exact checks passed; no universal EG claim`, with the following scope:

| Exact check | Completed scope |
|---|---:|
| Complete even bipartite factorization | 144 parameter pairs, `1<=p,z<=12` |
| Uniform-length matching routes | 256 cases, `1<=b<=16`, odd `1<=s<=31` |
| All perfect matchings on up to eight terminals | 620 cases, at `s=1,3,5,9,13` |
| Full global matching-group actions | 12,840 exact reservoir partitions; 240 exact marginal equalities, `2<=b<=5`, `s=3,5,9` |
| Real-path lifts, shared nonterminals, terminal revisits, direct terminal edges | 294 cases; 45 degree-certified minimum caps; up to `b=16,L=480` |
| All even atlas graphs with an edge, through order seven | 77 graphs; minimum cap partitions found by exact search over 3,779 simple cycles in total |
| All marked nonisolated roots of those atlas graphs | 465 roots; 1,860 lifts at `s=3,5,7,11`, including 1,548 satisfying the average-three test |
| Average-three floor inequalities | 1,019,800 integer cases, `1<=b,a<=100` |
| General capped-profile price inequalities | 88,700 further parameter cases; all 66,282 capped profiles for `1<=b<=4` |
| Unbalanced-degree family | 40 lifts; external maximum degree up to 41 while the average is exactly three |
| Constant-intersection template | Odd `b=s=3,...,17`; 3,888 exhaustive group outcomes at `b=s=3,5`; at size three, six template cycles versus three explicitly optimal alternative cycles |
| Repeated contractions and reverse lifting | Six steps; 18 rank removed; sum of profile prices 9; three core cycles lift to twelve; four components throughout |
| Even-surplus near twins | 120 cases, with zero, one, or two component mergers (40 each); up to 32 surplus edges |
| Four-edge deletion family | 33 sizes, `h=1,...,32,64`; at `h=64`, the minimum rises from 3 to 65 |
| Density-only prescribed-routing obstruction | Six sizes through `s=b=101`; final density `9803/10201` with an unroutable matching pair |

Every produced cycle is checked for vertex simplicity, and every complete output is checked for exact edge multiplicities. The script separately verifies the relevant degree/block lower-bound certificates for the explicit optimal examples; it does not claim to compute the optimum of every expanded graph.

All **33 pre-existing `Submission` files** were compared against hashes taken before this work and remained byte-for-byte unchanged. The checker also snapshots them before its own run and verifies that they remain unchanged afterward. The protected specification hash is

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

No pre-existing research file, checker, or Lean file is imported as executable code or modified by the checker.

## 11. What remains open in this investigation

The result is a concrete integral expansion and a strictly smaller-graph reduction with an explicit rank price. It tolerates nonleaf terminals by paying their own-route intersection debt, and the capped profile and root-retaining alternative substantially improve that price.

There is no bound here on arbitrary irreducible cores, no universal supply of eligible exact or near reservoirs, no cheap transport of an odd cover, and no arbitrary missing-edge repair theorem. Therefore neither the pure universal rank bound nor the specified Erdős–Gallai cycle/edge theorem is settled by this work.
