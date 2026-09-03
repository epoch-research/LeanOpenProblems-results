# Dense-core retirement: a same-scale obstruction and a globally paid reopening rule

## Status and main conclusions

**The proposed universal normal form is false.** There are no fixed positive constants `alpha, eta, gamma, epsilon` such that every graph can be edge-partitioned into original-degree-share-paid `eta`-dense cores and one `(epsilon,gamma)` hereditary power-sparse remainder. This failure occurs **in the original graph, before any deletion**.

More strongly, replacing the original-degree-share test by *any* account guaranteeing `sum |V(core)| <= C n` does not repair that normal form. Even arbitrary boundary-share transfers, arbitrary overlap of core vertex sets, and `B n` exceptional edges do not suffice, for fixed `C,B`.

The obstruction is the elementary, even, vertex-transitive graph

```
H(t,m) = K_m square ... square K_m       (t Cartesian factors; m odd),
n = m^t,                 d_H(v) = t(m-1).
```

For fixed `eta,gamma,epsilon,B`, every edge partition

```
E(H) = E(R) disjoint-union F disjoint-union (disjoint-union_j E(K_j)),
```

with `delta(K_j) >= eta |V(K_j)|`, `R` hereditary `(epsilon,gamma)`-sparse, and `|F| <= B n`, satisfies

```
sum_j |V(K_j)| >= (1-o_m(1)) t n.                         (A)
```

The error tends to zero as `m -> infinity`, uniformly for integers `t >= 1`. The coordinate-clique partition has total core order exactly `t n`, so this obstruction is asymptotically sharp. It is **not a density-scale example**: all coordinate cliques have the same order and the ambient graph is regular.

This is not a counterexample to Erdős–Gallai. In fact, for odd `m`, these same graphs have an explicit simple-cycle edge partition of size

```
(m^(t-1) + m - 2)/2 <= n/2.                              (B)
```

The construction reopens coordinate-local cycles in coherent Cartesian packets. Its entire cost is paid by a **single original-degree-share ledger**, not by a fresh `n` at each coordinate or scale. The Cartesian cycle construction itself is already proved in `ResearchAmplification.md`, Section 2A; it is reproved below for completeness. Its application to this obstruction, the quantitative share account, and the obstruction (A) are the results of this investigation, not claims of literature priority.

An explicit amended *sufficient certificate* is also proved: allow certain recognizable Cartesian cycle packets, with a stated ambient-degree ceiling, in addition to share-paid dense cores and one sparse remainder. No assertion that every graph admits this amended certificate is made. **The unrestricted Erdős–Gallai problem remains unresolved here.**

Only the new files `ResearchRetirement.md` and `ResearchRetirementCheck.py` were created. All 24 preexisting files in `Submission` were preserved. No informal dense-vertex-cover result is used.

---

## 1. Precise normal form and the single ledger

All graphs are finite, simple, and undirected. All cycles below are simple cycles of length at least three. Every decomposition is an **edge partition**, not a cover. Write `v(K)=|V(K)|` for the support order of an edge subgraph, omitting isolated vertices. Dense cores need not be induced or vertex-disjoint.

Fix constants

```
0 < eta < 1,   alpha > 0,   0 < epsilon < 1,   gamma >= 1,
C >= 0,        B >= 0,
```

independent of the graph. A graph `R` is hereditary `(epsilon,gamma)`-sparse when

```
e_R(X) <= gamma |X|^(2-epsilon)        for every vertex set X.       (1.1)
```

The two imported CFS results are:

* `delta(K) >= eta v(K)` implies a partition into at most `D_eta v(K)` cycles/singleton edges;
* (1.1) implies such a partition into at most `C_(epsilon,gamma) |V(R)|` pieces.

The definition and the second result are exactly Definition `defsparse1` and Corollary `bcor` in `/corpus/src/1310.0632/1310.0632.tex`. The minimum-degree result is its Theorem `EGlargemin`. No assertion about the minimum length of every output cycle is imported.

For the *original graph* `G`, put

```
W_G(P) = sum_v d_P(v)/d_G(v)
       = sum_(uv in E(P)) (1/d_G(u) + 1/d_G(v)),                    (1.2)
```

where only nonzero original degrees contribute. For edge-disjoint packets,

```
sum_P W_G(P) <= n.                                                (1.3)
```

This is the valid ledger from `ResearchPackets.md`, Section 7.4. Consequently, `W_G(K_j) >= alpha v(K_j)` would give `sum_j v(K_j) <= n/alpha`.

We will rule out the much weaker requirement

```
sum_j v(K_j) <= C n,                                             (1.4)
```

in an edge partition into dense cores, one remainder satisfying (1.1), and at most `B n` arbitrary exceptional edges. This has important scope:

* The cores may be chosen simultaneously, optimally, or after any preprocessing order.
* Their supports can overlap without restriction.
* Noncore boundary edges can be assigned to the one sparse bucket or to the exceptional edges in any way.
* Even if an entire packet `P` pays for several cores using its **whole** share, the rule

  ```
  W_G(P) >= alpha sum_(cores charged to P) v(K)
  ```

  still implies (1.4), by (1.3), if each core is charged and the packets are edge-disjoint. Thus arbitrary redistribution of available original shares within such packets is covered by the obstruction.

A packet with an additional, genuinely different cycle-recombination theorem is not ruled out merely because it contains cores. That distinction will be essential in Sections 7–8.

---

## 2. The graph: many directions, all at the same clique scale

The vertices of `H(t,m)` are tuples in `[m]^t`. Two vertices are adjacent exactly when they differ in one coordinate. Thus

```
n = m^t,          D = t(m-1),          e(H) = t n(m-1)/2.           (2.1)
```

It is connected and vertex-transitive. Choosing `m` odd makes `D` even, so no parity reduction or singleton correction is needed for the counterexample.

Fix a coordinate and fix the other `t-1` entries. The resulting `m` vertices induce a coordinate clique `Q=K_m`. There are

```
t m^(t-1) = t n/m                                                (2.2)
```

such cliques. **Every edge belongs to exactly one of them**, and every vertex belongs to exactly `t` of them. Hence their total order is `t n`.

Each coordinate clique has the exact original share

```
W_H(Q) = m/t,          W_H(Q)/v(Q) = 1/t.                         (2.3)
```

Furthermore, every vertex of `Q` has exactly `(t-1)(m-1)` ambient edges leaving `Q`. At the start of the process all these boundary edges are unused. Therefore the obstruction is not caused by confusing processed degree with unused degree: even genuinely available boundary degree need not lead to a larger share-paid dense core.

---

## 3. The hereditary edge bound

### Lemma 3.1 — dimension-independent Hamming edge isoperimetry

For every nonempty `X subseteq V(H(t,m))`, with `s=|X|`,

```
2 e_H(X) <= (m-1) s log_m s.                                     (3.1)
```

This bound is tight when `X` is a coordinate subcube of order `m^k`.

**Proof.** Let `Z=(Z_1,...,Z_t)` be uniform on `X`. For coordinate `i`, partition `X` into fibres by fixing all other coordinates. If a fibre has size `a`, then `1 <= a <= m`, and it contributes `binom(a,2)` edges in direction `i`.

Concavity of the logarithm on `[1,m]` gives

```
a-1 <= (m-1) log_m a.
```

Consequently,

```
2 e_H(X)
 = sum_i sum_(i-fibres) a(a-1)
 <= (m-1) sum_i sum_(i-fibres) a log_m a
 = (m-1) s sum_i H(Z_i | Z_(-i))/log m.                           (3.2)
```

Here conditional distributions on fibres are uniform. By the entropy chain rule and the fact that conditioning cannot increase entropy,

```
sum_i H(Z_i | Z_(-i))
 <= sum_i H(Z_i | Z_1,...,Z_(i-1))
 = H(Z) = log s.
```

Substitution proves (3.1). For a coordinate subcube there are `k` complete directions, and both sides equal `k(m-1)s`. ∎

### Corollary 3.2 — absorbing enough original share forces a large support

For any nonempty edge subgraph `P` of `H`, dense or not,

```
W_H(P)/v(P) <= log_m v(P)/t.                                    (3.3)
```

Indeed, `H` is `D`-regular, so `W_H(P)=2e(P)/D`, and (3.1) applies to its support. Thus

```
W_H(P) >= alpha v(P)   implies   v(P) >= m^(alpha t) = n^alpha.   (3.4)
```

This is a quantitative boundary-absorption barrier. To acquire a constant average fraction of the original degree, a packet must spread over an exponentially large support in the number of directions. The next lemma says that a fixed-density core cannot do this.

---

## 4. No original-share-paid dense core, even before processing

Assume from now on

```
m >= max(3, 2/eta),
A = 2m/eta,
lambda = log_m A = 1 + log_m(2/eta) <= 2.                         (4.1)
```

### Lemma 4.1 — every dense core has bounded support and tiny average share

If an edge subgraph `K` satisfies `delta(K) >= eta s`, where `s=v(K)>0`, then

```
s < 2m/eta,                                                     (4.2)
2e(K)/s <= (m-1) lambda,                                        (4.3)
W_H(K)/s <= lambda/t <= 2/t.                                   (4.4)
```

The support bound is independent of the dimension `t`.

**Proof.** The minimum-degree condition and (3.1) imply

```
eta s <= 2e(K)/s <= (m-1) log_m s.                              (4.5)
```

The function `log_m x / x` is decreasing for `x >= e`. If `s >= A`, then `A>=6`, and `m>=2/eta` gives `log_m A<=2`. Hence

```
(m-1) log_m s / s
 <= (m-1) log_m A / A
 <= 2(m-1)/A
 = eta (m-1)/m < eta,
```

contradicting (4.5). This proves (4.2); (4.3) follows from (3.1), and division by `D=t(m-1)` gives (4.4). ∎

The same argument actually applies if the core is only required to have **average degree** at least `eta s`. Thus weakening minimum density to average density does not rescue the proposed normal form.

In particular, choose `t > 2/alpha`. Then **no** nonempty edge subgraph of `H(t,m)` simultaneously satisfies

```
delta(K) >= eta v(K),       W_H(K) >= alpha v(K).                (4.6)
```

This quantifies over every possible edge subgraph, not just coordinate cliques, induced subgraphs, or cores found by a particular algorithm. Deletion cannot create an eligible core: a subgraph of a residual graph is still an edge subgraph of the original `H`, with the same original-degree weights.

If `m^epsilon > 4 gamma`, a coordinate clique already violates (1.1), since

```
binom(m,2) >= m^2/4 > gamma m^(2-epsilon).                       (4.7)
```

Thus a graph can have **no eligible dense core at all**, while failing the desired remainder condition. The following theorem also excludes arbitrary global core-order accounts and boundary-share transfers.

---

## 5. An asymptotically sharp lower bound on every dense-core normal form

### Theorem 5.1 — the `t n` obstruction

Let `m,t,eta` satisfy (4.1). Suppose that

```
E(H(t,m)) = E(R) disjoint-union F disjoint-union (disjoint-union_j E(K_j)),
```

where

* `delta(K_j) >= eta v(K_j)` for every core;
* `e_R(X) <= gamma |X|^(2-epsilon)` for every vertex set `X`;
* `|F| <= B n`.

Then, with `lambda` from (4.1),

```
L := sum_j v(K_j)
 >= (t n/lambda)
    [1 - 2 gamma m^(1-epsilon)/(m-1) - 2B/(t(m-1))].              (5.1)
```

**Proof.** Apply the hereditary remainder inequality to each coordinate clique. Since these cliques edge-partition `H`,

```
e(R) = sum_Q e_R(Q)
     <= (t n/m) gamma m^(2-epsilon)
     = gamma t n m^(1-epsilon).                                (5.2)
```

There is no union or bounded-overlap assumption here: every edge is counted exactly once. By (4.3),

```
sum_j e(K_j) <= ((m-1)lambda/2) L.                              (5.3)
```

The edge partition gives

```
sum_j e(K_j)
 = e(H)-e(R)-|F|
 >= t n(m-1)/2 - gamma t n m^(1-epsilon) - B n.
```

Combine this with (5.3) and divide by `(m-1)lambda/2`. ∎

### 5.1 Sharpness and uniform asymptotics

For fixed `eta,gamma,epsilon,B`,

```
lambda = 1 + O_eta(1/log m),
2 gamma m^(1-epsilon)/(m-1) = O_gamma(m^(-epsilon)),
2B/(t(m-1)) = O_B(1/(tm)).
```

Therefore (5.1) gives (A), uniformly for `t>=1`. Conversely, for sufficiently large `m`, every coordinate clique satisfies `m-1 >= eta m`. Taking all coordinate cliques as cores, and `R=F=empty`, gives `L=t n`. Thus the smallest possible total dense-core order in this normal form is between `(1-o_m(1))t n` and `t n`.

For the single even family `t=m -> infinity` through odd integers,

```
L >= (1-o(1)) m n,
W_H(K)/v(K) <= (1+o(1))/m      for every eta-dense K,
m ~ log n / log log n.                                         (5.4)
```

Alternatively, after fixing the target constants, one may fix one sufficiently large odd `m` and let `t -> infinity`. Then (5.1) forces `L=Omega(t n)=Omega(n log n)`, with constants depending on that fixed `m`. This is a lower bound on the **normal form**, not on unrestricted cycle partitions. For fixed `m`, the whole family is power-sparse with a larger constant depending on `m`; this does not satisfy the prescribed universal `gamma`. The diagonal family (5.4) avoids relying on a single fixed alphabet.

### 5.2 Exact universal nonexistence, including exceptional edges

Given any fixed `C,B,eta,gamma,epsilon`, choose an integer `t>4C` and an odd integer `m` so large that

```
m >= max(3, 2/eta),        m-1 >= 8B,        m^epsilon >= 16 gamma.
```

Then

```
lambda <= 2,
2 gamma m^(1-epsilon)/(m-1) <= 4 gamma m^(-epsilon) <= 1/4,
2B/(t(m-1)) <= 1/4.
```

Formula (5.1) yields

```
L >= t n/4 > C n.                                               (5.5)
```

Hence no universal `C`-bounded core-order decomposition exists. Taking `C=1/alpha` disproves any globally original-share-paid version, including payment by whole packets with flexible boundary-share absorption. One can additionally choose `t>2/alpha` to have the stronger no-individually-eligible-core property (4.6).

A fixed number of hereditary sparse buckets also does not fix the statement: their union satisfies (1.1) with the sum of their constants. A bounded number of forests or other `O(n)` edge exceptions is already covered by `F`.

### 5.3 This is not merely a pessimistic dense-theorem price

If a core `K` is finalized **separately**, any partition of it into cycles and singleton edges uses at least

```
Delta(K)/2 >= delta(K)/2 >= eta v(K)/2                           (5.6)
```

pieces: at a fixed vertex each piece contributes at most two incident edges. Thus any procedure that decomposes each dense core independently and never rejoins their edges uses at least `eta L/2` pieces in the cores alone. The example (5.5) forces at least `eta t n/8` such pieces.

So merely replacing `D_eta v(K)` by the *optimal* decomposition cost of each dense core does not remove the loss. This assertion is intentionally scoped to separate core finalization. A cycle that is allowed to combine edges from many cores can avoid it; Section 7 explicitly does so.

### 5.4 A fully specified numerical witness

Take

```
m=81,  t=65,  n=81^65,
eta=1/4,  alpha=1/8,  epsilon=1/2,  gamma=1,  B=5.
```

Every `eta`-dense core satisfies `W_H(K)/v(K) <= 2/65 < 1/8`. Moreover,

```
e(H) = 2600 n,
e(R) <= 585 n,
|F| <= 5 n,
e(K) <= 80 v(K)       for every eta-dense K.
```

Consequently every dense-core normal form, even without individual share tests, has

```
L >= (2600-585-5)n/80 = (201/8)n > 10n.                          (5.7)
```

This is an exact finite graph specification and exact rational arithmetic. The exponentially large graph is not claimed to have been materialized by the checker.

---

## 6. What this says about preprocessing, reservoirs, and retirement

### Preprocessing cannot repair this particular normal form

The core obstruction holds for **all** edge subgraphs of the original graph. It is not a statement about a bad greedy choice. Reordering dense cores, postponing some of them, or certifying them simultaneously cannot invalidate (5.1). For `t>2/alpha`, there is no eligible core to select even at time zero.

In particular, the degree-surplus certificate from `ResearchPackets.md`, (7.9), cannot by itself be upgraded to an eligible-dense-core extraction lemma. On a coordinate clique, all of the surplus is genuinely unused boundary degree, but absorbing a constant fraction of it demands large support as in (3.4), incompatible with fixed density as in (4.2).

### A single fixed sparse reservoir cannot hold the missing mass

Equation (5.2) says that any allowed reservoir retains at most the fraction

```
e(R)/e(H) <= 2 gamma m^(1-epsilon)/(m-1) = O(m^(-epsilon))        (6.1)
```

of the edges. Thus it cannot hide most coordinate directions. Nearly all of them must still be processed outside the reservoir, where dense-core order is approximately `t n`.

Allowing `gamma` or `1/epsilon` to grow with the graph changes the target: the constant in the CFS theorem is then not a universal linear bound. Likewise, taking a new sparse-bucket budget at each direction is precisely the repeated-`n` expenditure the question excludes.

### Permanent local retirement forces large-scale reopening later

A cycle entirely within one coordinate clique has length at most `m`. In any final partition with at most `C n` pieces, the total number of edges in such local cycles and in singleton pieces is at most `C n m`. Therefore at least the fraction

```
1 - 2Cm/[t(m-1)]                                               (6.2)
```

of all edges must lie in cycles not confined to one coordinate clique, whenever this lower bound is positive.

For odd `m`, separately Hamilton-decomposing every coordinate clique produces exactly

```
N_local = (t n/m)(m-1)/2                                       (6.3)
```

cycles. A final partition of at most `C n` pieces can retain at most `C n` of these cycles unchanged. Hence at least `N_local-Cn` old cycles must be reopened, if this number is positive. As `t` grows, the fraction that must be reopened tends to one.

This is a statement about the specified coordinate-local initial partition, not a lower bound against all initial choices. It quantifies the total amount of reopening that a method must budget; it does not rule out a long sequence of small exchanges. Section 7 supplies a whole-packet implementation.

### What has not been refuted

The original graph does have heavy cycles: the construction below includes Hamilton cycles of original weight `n/[t(m-1)]>1`. Thus this example does not refute a carefully ordered heavy-cycle algorithm, nor a more general scheme with independently justified non-dense closure packets. In particular, adding an allowance of `O(n)` arbitrary prepaid cycles changes the normal form: on this family such cycles can already contain all edges. The theorem refutes the static dense-core-plus-one-fixed-sparse-remainder target and any method whose final certificates have that form. Reopening can help only by going beyond separate dense-core finalization or beyond that static certificate.

---

## 7. A constructive escape with one original-degree budget

The following repair uses actual edges of already selected cycles. They are **reopened**, not treated as unused. Within each packet the old partition is replaced, and only the new partition remains in the output.

### 7.1 Two Hamilton cycles in the required torus

Let `m>=3`, let `M` be a multiple of `m`, and suppose `gcd(M,m-1)=1`. Then `C_M square C_m` has an edge partition into two Hamilton cycles.

**Construction and proof.** On `Z_M x Z_m`, orient horizontal edges by `x -> x+1` and vertical edges by `y -> y+1`. The phase `x+y (mod m)` is well-defined because `m` divides `M`.

In colour 0 choose the horizontal outgoing edge at phases `0,...,m-2`, and the vertical outgoing edge at phase `m-1`. Colour 1 takes the other outgoing edge. Each colour has outdegree one. Both possible predecessors of `(x,y)` have phase `x+y-1`, so exactly one is a predecessor of each colour: each colour also has indegree one. The factors partition all edges.

Every step raises the phase by one. After `m` steps, colour 0 translates by `(m-1,1)`, and colour 1 translates by `(1,m-1)`. Each translation has order exactly `M`; here both the divisibility and the stated gcd condition are used. A return must use a multiple of `m` steps by phase, then a multiple of `M` such blocks by translation. Each colour therefore has a single orbit of length `Mm`, so both are simple Hamilton cycles. ∎

In particular the hypotheses hold for `M=m^r`, for every integer `r>=1`.

### 7.2 A retained-Hamilton-cycle rule for a whole Cartesian packet

For every `m>=3` and `t>=1`, the torus packet

```
T(t,m) = C_m square ... square C_m
```

has a cycle partition containing a distinguished Hamilton cycle and having exactly

```
q_t(m) = (m^(t-1)+m-2)/(m-1)                                  (7.1)
```

cycles.

**Proof.** For `t=1`, use the single cycle. Suppose a partition at dimension `j-1` has a distinguished Hamilton cycle `H`, of length `M=m^(j-1)`. In dimension `j`, copy every old cycle into each of the `m` new-coordinate layers. Reopen precisely the `m` copies of `H`, and include **all** new-coordinate edges. Their union is exactly `C_M square C_m`, because `H` spans the preceding product.

Replace this union by the two Hamilton cycles from Section 7.1. Retain one as distinguished, and retain the other and all untouched copied cycles in the partition. The two groups of edges are disjoint and exhaust the product. Thus

```
q_1=1,                   q_j=m(q_(j-1)-1)+2,
```

which solves to (7.1). Every output piece is simple by construction. ∎

Two useful bounds are

```
q_t(m) <= m^(t-1) = |V(T)|/m                  (all t>=1),
q_t(m) <= 2 m^(t-2) = 2|V(T)|/m^2            (all t>=2).          (7.2)
```

The first also follows from the normalized recurrence

```
q_j/m^j = q_(j-1)/m^(j-1) - (m-2)/m^j.                          (7.3)
```

The second follows directly from (7.1), with equality at `t=2`. These bounds, rather than an `O(|V(T)|)` charge for each new dimension, are the quantitative retirement resource.

This construction is the one in `ResearchAmplification.md`, Lemmas 2.2–2.3, not a new assertion of a Hamilton-decomposition theorem for arbitrary Cartesian products.

### 7.3 Each torus packet is itself uniformly hereditary power-sparse

For any `X subseteq V(T(t,m))`,

```
e_T(X) <= |X| log_2 |X| <= 2 |X|^(3/2).                         (7.4)
```

Indeed, an `i`-fibre with `a` vertices spans at most `a log_2 a` cycle edges: this is zero at `a=1`, and at `a>=2` follows from the maximum-degree-two bound `e<=a`. Sum this bound over fibres and use the conditional entropy argument of Lemma 3.1. The last elementary inequality follows, for example, by maximizing `log x / sqrt(x)`.

Thus one such packet can genuinely be retained as a single sparse reservoir with fixed parameters, independent of `m,t`. But paying `C_(1/2,2)n` for each of an unbounded number of overlapping packets would again be wasteful. The sharper count (7.2) is what allows all packets to be retired on the original share ledger.

### 7.4 Partition the clique graph into coherent Cartesian cycle packets

Let `m=2r+1`. The complete graph `K_m` has an edge partition into `r` Hamilton cycles `B_1,...,B_r`; a self-contained Walecki formula is given in Section 9.

For each `a`, let `T_a` contain the Cartesian edges whose changing-coordinate edge belongs to `B_a`. Then

```
E(H(t,m)) = disjoint-union_(a=1)^r E(T_a),
T_a is isomorphic to C_m^(square t),
d_(T_a)(v) = 2t       at every one of the n vertices.             (7.5)
```

The edge identity is exact because a Cartesian edge has a unique changing coordinate, and its base edge belongs to a unique `B_a`.

For a literal whole-cycle reopening implementation, start with coordinate-clique Hamilton decompositions using the **same labelled Walecki family** in every coordinate fibre. Each `T_a` is then a union of whole old cycles of type `a`, namely `t m^(t-1)` of them. No partial old cycle is silently discarded. Arbitrary independently chosen local decompositions need not have this coherence; no universal coherence or ordering lemma is being assumed.

Apply Section 7.2 to each packet. The resulting partition has exactly

```
r q_t(m) = (m^(t-1)+m-2)/2                                   (7.6)
```

simple cycles. In particular it has at most `n/2` cycles for all `t>=1`, and at most `n/m` for `t>=2`.

### 7.5 The single original-share account

Use the degrees of the original `H(t,m)`, never residual degrees. By (7.5),

```
W_H(T_a) = sum_v 2t/[t(m-1)] = 2n/(m-1),
sum_a W_H(T_a) = n.                                           (7.7)
```

From (7.2),

```
q_t(m) <= n/m <= W_H(T_a)/2.                                  (7.8)
```

Consequently the entire final partition costs at most

```
(1/2) sum_a W_H(T_a) = n/2.                                   (7.9)
```

There is no separate `n` allocation for a direction, a stage, or a packet. The packets have unbounded vertex overlap, but their edges and original shares partition the one ambient account. Notice also that

```
W_H(T_a)/v(T_a) = 2/(m-1) -> 0.
```

Such a packet need not pass a fixed original-share-per-vertex test. It is nevertheless share-paid because its **actual cycle cost is much smaller than its order**. This is the substantive amendment to the dense-core rule.

Viewed as a fixed-final-vertex-set retirement process, at each intermediate dimension `j=2,...,t-1` there are `m^(t-j)` copies of one permanently retired cycle per type, and at the last dimension there are two. The total charge per final vertex per type is

```
sum_(j=2)^(t-1) m^(-j) + 2m^(-t) = q_t(m)/n        (t>=2).      (7.10)
```

This is a geometric, globally summable account. It is not `O(n)` charged separately at `t` stages. One may equivalently reopen each whole packet `T_a` once and output its recursively constructed partition; then each old edge is assigned to exactly one reopened packet.

---

## 8. A precise amended sufficient certificate

The torus repair gives the following non-tautological extension of the dense-core ledger to arbitrary ambient graphs.

### Theorem 8.1 — dense cores plus degree-paid Cartesian packets

Let `G` have an edge partition into:

1. `eta`-dense cores `K_j` with `W_G(K_j) >= alpha v(K_j)`;
2. packets `T_a` isomorphic to `C_(m_a)^(square t_a)`, where `m_a>=3`, `t_a>=2`, and, for a fixed constant `Lambda>0`,

   ```
   d_G(v) <= Lambda t_a m_a^2        for every v in V(T_a);       (8.1)
   ```

3. one hereditary `(epsilon,gamma)`-sparse remainder `R`;
4. a set `F` of at most `B n` exceptional edges.

No vertex-overlap bound is imposed. Then `G` has a cycle/singleton edge partition with at most

```
[max(D_eta/alpha, Lambda) + C_(epsilon,gamma) + B] n             (8.2)
```

pieces.

**Proof.** The CFS dense theorem handles each core at cost at most `(D_eta/alpha) W_G(K_j)`. A torus packet of order `N=m_a^(t_a)` has internal degree `2t_a`, so (8.1) gives

```
W_G(T_a) >= 2N/(Lambda m_a^2).
```

The explicit construction (7.2), not an assumed cycle bound, gives cost at most `2N/m_a^2 <= Lambda W_G(T_a)`. Sum these charges using the **one** ledger (1.3). Apply the hereditary sparse theorem once to `R`, and pay `|F|` singleton pieces. Edge-disjointness of the input parts and the actual partitions inside them prove edge-disjointness and exhaustion of the final output. ∎

The numerical ceiling (8.1) and the explicitly recognizable Cartesian structure are sufficient hypotheses, not the desired cycle-decomposition conclusion in disguise. For `H(t,m)` with `t>=2`, the packets (7.5) satisfy (8.1) with `Lambda=1`; for `t=1`, the whole clique is already a share-paid dense core. Thus this amended certificate covers the obstruction family with constants independent of both parameters, while the dense-core-only certificate does not.

This remains a *restricted* structural theorem. There is no proof that a general graph supplies such coordinate packets, or a suitable replacement for their coherent Hamilton reservoir. In particular, a large degree surplus outside a small core does not imply a Cartesian product structure.

---

## 9. Self-contained clique ingredient

For completeness, here is the exact Hamilton edge partition used in Section 7.4. Let `m=2r+1`, with vertices `infinity` and `Z_(2r)`. For each `a=0,...,r-1`, take the cyclic ordering

```
infinity, a, a-1, a+1, a-2, a+2, ...,
a-(r-1), a+(r-1), a-r, infinity,                              (9.1)
```

with finite entries taken modulo `2r`.

The finite entries are all distinct, so each is a Hamilton cycle. The edges at infinity across all cycles are precisely its `2r` incident edges. In the cycle indexed by `a`, the finite edges alternate between:

* the `r` distinct unordered pairs with endpoint sum `2a-1` modulo `2r`;
* the `r-1` distinct unordered pairs with endpoint sum `2a` modulo `2r`.

For an odd sum there are exactly `r` unordered distinct-endpoint pairs. For an even sum there are `r-1`, since the two solutions of `2x=2a` would give loops and are excluded. As `a` ranges over `0,...,r-1`, these sums cover all residues exactly once in their respective parity classes. Thus (9.1) partitions every finite edge exactly once as well. This verifies the Hamilton partition as an edge partition, not a double cover.

---

## 10. Verification and reproducibility

Run

```
python3 Submission/ResearchRetirementCheck.py
```

The checker uses only the Python standard library and does not import or edit an older checker. It verifies the following independently of the written proofs.

### 10.1 Exact finite subset checks

For the Hamming inequality it uses the equivalent integer comparison

```
m^(2e_H(X)) <= |X|^((m-1)|X|),
```

so no floating-point logarithm is involved. For the torus inequality it uses

```
2^(e_T(X)) <= |X|^(|X|).
```

The dense-support and share bounds are checked with exact rational arithmetic whenever their numerical hypotheses hold. Every edge subgraph with a given support is dominated by the induced graph on that support, so checking the induced graph is the appropriate finite check of the upper edge/share bound.

Recorded subset counts:

| `m` | `t` | Order | Subsets checked | Scope |
|---:|---:|---:|---:|---|
| 2 | 4 | 16 | 65,535 | all nonempty subsets; Hamming entropy bound |
| 3 | 2 | 9 | 511 | all nonempty subsets |
| 4 | 2 | 16 | 65,535 | all nonempty subsets |
| 7 | 1 | 7 | 127 | all nonempty subsets |
| 3 | 3 | 27 | 10,028 | deterministic random sample plus coordinate cliques and the full set |
| 5 | 2 | 25 | 10,008 | deterministic random sample plus coordinate cliques and the full set |

The sample seed is fixed. These finite tests are not offered as proofs of the infinite-family theorem.

### 10.2 Exact edge-partition checks

The checker verifies:

* uniqueness of the coordinate clique containing each edge, and total clique order `t n`;
* the Walecki clique partition;
* both torus Hamilton cycles by full edge-set equality and vertex simplicity, not just orbit lengths;
* 19 Cartesian cycle-power partitions, including even cycle lengths;
* 19 odd-clique Hamming partitions, checking every final cycle is simple, every graph edge occurs once, every packet has degree `2t`, and the packet shares sum exactly to `n`;
* the exact rational witness (5.7), without constructing its exponential vertex set.

Representative complete partition checks:

| `m` | `t` | `n` | Separate coordinate-clique cycles | Reopened output cycles |
|---:|---:|---:|---:|---:|
| 3 | 7 | 2,187 | 5,103 | 365 |
| 5 | 4 | 625 | 1,000 | 64 |
| 7 | 3 | 343 | 441 | 27 |
| 9 | 3 | 729 | 972 | 44 |
| 11 | 2 | 121 | 110 | 10 |

All tests passed. The symbolic witness returned the dense-core average-share upper bound `2/65` and the total core-order lower bound `(201/8)n`.

### 10.3 Protected files and inputs

SHA-256 snapshots before and after the work agreed for all 24 preexisting `Submission` files. The checker additionally verifies no preexisting file changes during its run. The unchanged `Spec.lean` SHA-256 is

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

Inputs actually used were:

* `ResearchPackets.md`, especially the ledger and failure certificate in Section 7.4;
* `ResearchHeavy.md`, for the distinction between original and residual degree weights and for the location of the CFS source;
* the actual CFS source `1310.0632.tex` for the two imported decomposition theorems;
* `ResearchAmplification.md`, Section 2A, for the already established Cartesian cycle repair, reproved here and supplied with the new ambient-share account.

No Lean proof of `erdos_184` is claimed or attempted in this file.

---

## 11. Exact remaining issue

The false bridge is now narrower and more concrete:

> The available degree outside a small dense core cannot in general be organized into another fixed-density core paid by original degree share, even when that degree is unused and even if all cores are chosen simultaneously. Nor can all failures be assigned to one hereditary power-sparse bucket with fixed constants while maintaining linear total core order.

The obstruction already occurs among same-size, heavily overlapping coordinate cliques in a regular even graph. Thus a universal proof needs an additional mechanism beyond reordering and boundary charging within that normal form.

One valid mechanism is now explicit: reopen a coherent family of coordinate-local cycles, preserve a Hamilton reservoir while absorbing new directions, and pay the resulting Cartesian packet by its much smaller cycle cost rather than its vertex order. Equations (7.7)–(7.10) provide a genuine single global account, and Theorem 8.1 permits this mechanism inside a general ambient graph under a checkable degree ceiling.

What is still missing is a universal extraction/organization theorem producing such low-cost non-dense packets, or another comparably concrete globally amortized reopening rule, when dense cores fail. Neither an unrestricted Erdős–Gallai proof nor a disproof follows from the results here.
