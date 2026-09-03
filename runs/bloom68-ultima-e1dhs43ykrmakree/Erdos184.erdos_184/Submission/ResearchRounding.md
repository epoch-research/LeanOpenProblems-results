# Fractional cycle partitions: exact series-parallel rounding and global obstructions

## Status

**The unrestricted additive rounding inequality `c(G) <= c_f(G) + C |V(G)|` is not proved here. Neither the genuine Erdős–Gallai O(n) conclusion nor its negation is claimed.** `Submission/Spec.lean` has not been edited.

The supplied, newly audited fractional bound is used as an input:

```
c_f(G) <= r(G) := |V(G)| - number_of_components(G)         [G even, simple].
```

It is not re-derived from an odd cover, a nonnegative dual, or an integrality assertion about the cycle-incidence matrix.

There is a concrete positive theorem, and several exact tests that substantially narrow a rounding approach:

1. **Exact rounding on Eulerian series-parallel networks:** `c=c_f`. A path/cycle dynamic program proves this without TU or half-integrality. There is also a compact signed dual certificate with one scalar per node of a series-parallel expression. Its inequalities certify **all** simple cycles, not just the input partition or the LP support. For any global minimum partition, every cycle is tight in an optimal certificate.
2. **Exact gluing across an articulation or a two-edge splice.** Both integer and fractional costs obey the same formulas; hence the additive gap is additive. Signed duals can be glued explicitly.
3. **The odd-cover chain is completely resolved, with zero rounding gap.** A larger theta-chain family has exact integer and fractional values. In the original three-branch/one-return chain, an optimal dual must put weight `1-k/2` on its closing edge. All globally minimum partitions have uniform-on-old-cycle prices that violate another cycle by an unbounded amount. A four-branch/two-return variant forces a **negative-weight simple cycle** in every optimal dual and makes even a maximum packing from optimal fractional support overpay.
4. **A globally sharp Petersen-ring test:** for every `t>=2`, a connected simple 4-regular graph on `14t` vertices has

   ```
   c_f=2,                 c=t+2,                 c-c_f=t.
   ```

   Four Hamilton cycles, each of weight `1/2`, certify the fractional value. An explicit `t+2` partition is proved **globally minimum**. The lower bound is not a bounded-exchange or local-optimality argument. All local transition perfect-matching inequalities are already valid in this example.
5. **Local fractional transition data has no hidden blossom guarantee.** Any degree-feasible fractional matching on the neighbours of one vertex extends to an *optimal fractional Hamilton decomposition of a complete even graph*. At a single vertex this can require arbitrarily many new transitions when rounded to a perfect matching.
6. **Support-only residual claims need extra hypotheses.** K5 gives an optimal basic solution with six coefficients `1/3`, no two support cycles edge-disjoint, and no support-only partition, although `c=c_f=2`. An explicit prime-order family gives pairwise-intersecting **basic, +1/2 near-optimal** supports whose maximal packing leaves minimum degree `n-3`. The near-optimal qualification is important: this last family is not asserted to be optimal.

These are auxiliary research results, not a claim of novelty over all literature. The checker is `Submission/ResearchRoundingCheck.py`. The main unresolved step is stated in Section 9.

Protected specification SHA-256:

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

---

## 0. Definitions and why the additive statement is the whole remaining problem

Graphs are finite, simple and undirected. A cycle is simple, and a partition is an **edge partition**, not a cover or an odd cover. Isolated vertices are allowed. For an even graph let

```
c(G)   = min number of cycles in an edge partition;
c_f(G) = min sum_C x_C,
         subject to sum_{C containing e} x_C = 1 for every e, x_C >= 0.
```

The dual is

```
max y(E),       subject to y(C) <= 1 for EVERY simple cycle C,
                y_e in R, with no sign restriction.                     (0.1)
```

All these programs are finite. Feasibility follows from the elementary cycle partition of an even graph; an edgeless graph has both values zero. In particular,

```
y(E) <= c_f(G) <= c(G).                                                  (0.2)
```

If D is a global minimum partition, a feasible y with

```
sum_{C in D} (1-y(C)) <= C_0 n                                           (0.3)
```

is exactly the desired additive certificate. There is no license to check (0.1) only on D. Also, the existence of (0.3) cannot be deduced from local optimality: the high-Berge-girth examples in `ResearchHeavy.md` rule out that replacement.

Given the audited bound `c_f<=r`, additive O(n) rounding would yield `c=O(n)` for even graphs. For a general graph, choose a spanning-forest T-join for its odd-degree vertex set. It has at most `n-components` edges, and deleting it leaves an even graph. Put these deleted edges back as singleton pieces. This gives the actual Spec conclusion with a uniform linear function. Conversely, a linear cycle/singleton bound on an even graph can be made a pure-cycle bound: the singleton remainder is even and has only O(n) edges, so it too has an O(n) cycle partition. Thus the new fractional bound does not make the remaining assertion a routine LP rounding step.

Distinguish the graphic **rank** `r=n-components` from the **nullity**

```
beta(H) = |E(H)| - |V(H)| + components(H).
```

A basic solution can have rank determined by individual-edge constraints. Replacing that rank by r without proof is precisely the sort of unjustified dimensional reduction that must be avoided.

---

## 1. A concrete exact rounding theorem

### Theorem 1.1 — series-parallel path/cycle rounding

Let N be a simple two-terminal series-parallel network with terminals s,t, all of whose internal vertices have even degree. A supplied expression uses:

* a single edge;
* **series composition**, with the children sharing just the identified terminal;
* **parallel composition**, with edge-disjoint children sharing just s,t.

Let `F_N(p)` be the minimum fractional mass of cycles in an exact edge cover by simple cycles and simple s–t paths, when the total path mass is p. Let `delta_N` be the common parity of the two terminal degrees.

Whenever an integer p of parity `delta_N` is fractionally feasible, there is an **integral** partition into exactly p simple s–t paths and `F_N(p)` simple cycles. In particular, for an even N,

```
c(N) = c_f(N).                                                          (1.1)
```

The statement extends by additivity to graphs whose cycle blocks have such expressions; this is the usual Eulerian series-parallel class. The proof below uses the expression, not a minor-recognition theorem.

### 1.1 Fractional traffic intervals

For each expression node define integers `ell_N, lambda_N` recursively:

```
edge:      ell=lambda=1;
series:    ell=max(ell_1,ell_2),    lambda=min(lambda_1,lambda_2);
parallel:  ell=0,                  lambda=lambda_1+lambda_2.             (1.2)
```

The feasible fractional path masses are exactly `[ell_N,lambda_N]`. Always

```
ell_N in {0,1},   lambda_N>=1,   lambda_N = delta_N (mod 2),
delta_N=0 implies ell_N=0.                                              (1.3)
```

For a series composition the two path masses must agree. Internal evenness at the series junction forces the two terminal parities to agree as well.

For a parallel composition, write p_i for the child path masses and h for the mass paired into cross-cycles. The exact relations are

```
0 <= h <= min(p_1,p_2),       p=p_1+p_2-2h,
F_N(p) = min [ F_1(p_1)+F_2(p_2)+h ].                                   (1.4)
```

Every cross-cycle is one terminal path from each child. Conversely any two such paths form a simple cycle, because their interiors are disjoint. Fractional path masses can be coupled arbitrarily: couple submeasures of total mass h by a product coupling divided by h. At h=0 there is nothing to couple. The analogous coupling in series glues equal path masses. These observations prove the recurrences for the actual fractional programs, not just formal recurrences.

Both child intervals contain 1. For `0<=p<=lambda_1+lambda_2`, the pair

```
p_1^* = min(lambda_1, p+lambda_2),
p_2^* = min(lambda_2, p+lambda_1)                                      (1.5)
```

lies in the child intervals and satisfies `|p_1^*-p_2^*|<=p<=p_1^*+p_2^*`. Thus the parallel interval really is the whole claimed interval. This also verifies (1.2)–(1.3) inductively.

### 1.2 The monotone quantity that selects a global optimum

Put

```
K_N(p) = F_N(p)+p/2.
```

**Claim:** K_N is nonincreasing on its feasible interval, and (1.5) is an optimal choice in every parallel composition.

Proof by induction. For an edge the domain is a singleton. In series,

```
K_N(p) = K_1(p)+K_2(p)-p/2,
```

so it is nonincreasing. In parallel, (1.4) becomes

```
K_N(p) = min [K_1(p_1)+K_2(p_2)].                                       (1.6)
```

Every feasible pair obeys `p_1<=lambda_1` and `p_1<=p+p_2<=p+lambda_2`, and likewise for p_2. Hence (1.5) is a **componentwise maximum feasible pair**. By induction both summands in (1.6) are nonincreasing, so that pair minimizes their sum. Its coordinates are nondecreasing functions of p, proving monotonicity of K_N as well. Consequently the explicit recurrence is

```
F_N(p) = F_1(p_1^*) + F_2(p_2^*) + (p_1^*+p_2^*-p)/2.                  (1.7)
```

This optimizes over all fractional path/cycle covers of the network. It is not a local-exchange assertion about an existing cycle partition. □

### 1.3 Integral reconstruction

Induct on the expression, for integer p of the required terminal parity.

* In series, the children have the same required parity. Their integral partitions have exactly p paths each. Pair those paths and concatenate through the sole shared vertex. Every concatenated path is simple.
* In parallel, `lambda_i` has the child parity. Since p has parity `delta_1+delta_2`, both entries of (1.5) have their respective child parity. The integer

  ```
  h=(p_1^*+p_2^*-p)/2
  ```

  lies between zero and the smaller path count. Pair h paths from each child to obtain h simple cycles; retain all unpaired paths and all child cycles. The cost is exactly (1.7).
* The edge case is immediate.

No repeated-vertex trail is being declared simple. The disjoint-interior conditions in the expression are precisely what justify both gluing operations. At the even root, p=0 is feasible by (1.3), proving (1.1). □

### 1.4 A compact signed dual certifying ALL cycles

Give every expression node a free real variable `alpha_N`. For a leaf edge e set `y_e=alpha_e`. Impose

```
series:    alpha_1+alpha_2 <= alpha_N;
parallel:  alpha_1 <= alpha_N,  alpha_2 <= alpha_N,
           alpha_1+alpha_2 <= 1.                                      (1.8)
```

Induction proves simultaneously that every terminal path in N has weight at most alpha_N and that every cycle in N has weight at most one. In parallel, the extra inequality handles **every** cross-cycle; in series all cycles stay in a child.

Conversely, given edge weights satisfying all cycle inequalities, let alpha_N be the maximum weight of a terminal path in N. Path maxima add in series and take a maximum in parallel. The two maximizing child paths in parallel form a simple cycle, so their sum is at most one. Thus (1.8) is an exact extended formulation of the dual constraints.

Maximizing `sum_leaf alpha_e` gives `c_f(N)`. More generally, maximizing

```
sum_leaf alpha_e - p alpha_root
```

gives `F_N(p)` by finite LP duality. There are only O(expression size) inequalities. Signs of the alphas and of the edge weights are unrestricted. This is a compact structural certificate, **not** a TU claim.

Combined with Theorem 1.1, an optimal certificate has `y(E)=c(N)`. For **any global minimum partition D**, not merely the one reconstructed above, summing `y(C)<=1` over D now forces `y(C)=1` for every `C in D`. Thus the requested minimum-partition dual fitting is exact on this class.

The theorem asserts equality of optimal values, not integrality of every optimum basic solution. For example, in K_(2,6), view each of its six length-two terminal paths as an item. Give weight 1/2 to the three pair-cycles on items 1,2,3 and to the three pair-cycles on items 4,5,6. This is a fractional basic optimum of value 3, with no integral partition in its support. Pairing across the two odd triples produces an integral optimum.

---

## 2. Exact gluing and the rank ledger

### Lemma 2.1 — articulations and subdivisions

If two even graphs are joined at one vertex, every simple cycle lies in one side. Therefore both c and c_f add. The same is true over all articulation blocks. Each block of an even graph is even: take any elementary cycle partition; each of its cycles lies in one block. Their graphic ranks add as well. Subdivision of an edge leaves c and c_f unchanged: every cycle using any part of the subdivision uses the whole path.

### Lemma 2.2 — two-edge splice

Take disjoint connected even simple graphs G_1,G_2 with marked edges `u_i v_i`. Delete those two edges and add `u_1 u_2` and `v_1 v_2`, obtaining G. Then

```
c(G)   = c(G_1)+c(G_2)-1,
c_f(G) = c_f(G_1)+c_f(G_2)-1.                                          (2.1)
```

**Integer proof.** The new edges form a two-edge cut. Exactly one cycle of a partition uses them, and it uses both. Cap its path on each side with the old marked edge. This recovers partitions of the original graphs, with total count one larger. Conversely splice the marked cycles of minimum partitions. The resulting cycle is simple because the sides are vertex-disjoint. □

**Fractional proof.** The total mass of cross-cycles is exactly one. Restricting and capping them yields feasible fractional partitions on both sides, with total cost increased by one. Conversely couple the marked-cycle distributions, each of total mass one, and splice their paths. This preserves every individual edge constraint and decreases the total cost by one. □

There is an explicit dual version. Keep the old dual weights except on the deleted edges, and choose the two new weights to have sum

```
y_1(u_1v_1)+y_2(u_2v_2)-1.                                            (2.2)
```

A cross-cycle has weight equal to the sum of its two capped cycle weights minus one, hence at most one. Local cycles retain their inequalities. The total dual value is `y_1(E_1)+y_2(E_2)-1`. Negative new weights are allowed and sometimes necessary.

Consequently `c-c_f` adds under this operation. For connected inputs,

```
r(G)=r(G_1)+r(G_2)+1.
```

So an additive rank budget is not multiplied by these splices. A four-edge boundary is different: the path pairings and their simultaneous simplicity matter. Section 6 gives an exact obstruction invisible to the two-edge calculation.

---

## 3. The signed-price chain, with an exact generalization

### 3.1 The family T(k,a,b)

Let `k>=1`, `a,b>=1`, and `a=b (mod 2)`. Put vertices `u_0,...,u_k` in a chain. Between `u_(i-1),u_i` put a internally disjoint length-two paths, all with private internal vertices. Between `u_0,u_k` put b return paths, also internally disjoint and private. When b=1 use one direct closing edge; when b>=2 use length-two return paths. The graph is simple and even.

Every simple cycle is exactly one of:

1. two forward paths in a single segment;
2. two return paths;
3. one forward path in every segment and one return path.

For a cycle not using a return, an internal chain junction is an articulation of the forward network, so it stays in one segment. A cycle using a return either uses two returns or traverses the forward network as one terminal path. This proves the classification, including all mixed cycles.

### Theorem 3.1 — exact values

With `q=min(a,b)`,

```
c(T)=c_f(T)=q + k(a-q)/2 + (b-q)/2.                                    (3.1)
```

For an upper bound choose q edge-disjoint long cycles, then pair the remaining forward paths in each segment and the remaining return paths. The parity assumption makes all pair counts integral.

For a fractional lower bound let L be the total mass of long cycles. Summing path-edge equalities gives `0<=L<=q`, local cycle mass `(a-L)/2` in each segment, and return-local mass `(b-L)/2`. Hence the total cost is

```
ka/2+b/2-(k-1)L/2,
```

minimized at L=q. This proves (3.1), not just an integer upper bound. □

An explicit all-cycle dual is useful. When `a>=b`, give each forward path total weight 1/2 and each return path total weight `1-k/2`; split a path's weight arbitrarily over its edges. Local forward cycles and long cycles have weight one, while return-local cycles have weight `2-k<=1`. The objective is

```
ka/2+b(1-k/2)=k(a-b)/2+b.
```

When `b>=a`, give each forward path total weight `1/(2k)` and each return total weight 1/2. The three cycle types have weights `1/k, 1, 1`, and the objective is `(a+b)/2`. Thus every case has an explicit dual attaining (3.1).

### 3.2 The named odd-cover/negative-edge example: a=3, b=1

Here

```
n=4k+1,       c=c_f=k+1,       y(closing edge)=1-k/2.                    (3.2)
```

Three long cycles, using the three different forward branches in every segment, form an **odd cover**: every forward edge occurs once and the closing edge occurs three times. All three cycles have dual weight one, but

```
y(E)=k+1,       sum of the three cycle weights=3.
```

The difference is exactly the two extra copies of the negative closing edge. This is why an odd cover cannot be substituted into the equality-constrained dual argument.

For `k>=2`, the optimum with the **additional restriction `y_e>=0`** is exactly 3. The odd cover gives the upper bound. Giving every forward path total weight `1/k` and the closing edge weight zero attains it. Thus the discrepancy is unbounded, even though the genuine integer rounding gap is zero.

The negative closing weight is forced in **every** optimal dual when k>2. To see this, assign weight `3^(-k)` to every long cycle and weight 1/3 to each of the three local cycles in every segment. This is a feasible optimum with all cycle types positive. Complementary slackness makes every local cycle tight, forcing all three branch sums to be 1/2, and then every long-cycle equality forces the closing-edge weight `1-k/2`.

Every integer partition uses one long cycle and one local cycle in each segment, hence is globally minimum. Give each edge of an old cycle D_j the natural weight `1/|D_j|`. The alternative long cycle using a branch from each old local cycle has weight

```
k/2 + 1/(2k+1).                                                       (3.3)
```

For k>=2 this exceeds one and grows without bound. Thus the uniform-on-D proposal fails even for **every global minimum D in a zero-gap family**. Signed redistribution, rather than an appeal to local exchange, solves this family exactly.

### 3.3 A refinement: even nonnegative CYCLE weights are too restrictive

Take a=4,b=2. Now

```
c=c_f=k+2.
```

The return paths form a simple four-cycle R. The dual above has

```
y(R)=2-k.                                                             (3.4)
```

For k>2 this negative cycle weight is forced in every optimal dual. More generally, for `a>b`, give every long cycle weight `a^(-k)` for each return choice and every local forward pair-cycle weight

```
(a-b)/(a(a-1)).
```

This is an optimum with every forward-local and every long cycle positive. For a>=3, tightness of all pair-cycles forces forward path sums 1/2, then tightness of all long cycles forces each return sum `1-k/2`.

If one additionally imposed `y(C)>=0` for all simple cycles, the optimum in the (4,2) family would be only 4 for k>=2. Indeed four long cycles can cover every forward edge once and each return edge twice, so

```
sum_{j=1}^4 chi_(long_j) = 1_E + chi_R.
```

Nonnegative y(R) gives `y(E)<=4`. Forward path sums `1/k` and zero return sums attain 4. A dual-fitting proof therefore cannot silently require nonnegative cycle sums either.

### 3.4 Maximum support packing can itself overpay

Use the optimum fractional support just described for (4,2): all forward-local cycles and all long cycles, but no return-local cycle. Select two disjoint local cycles per segment. This packing P has

```
|P|=2k,        residual=R,        |P|-c_f=k-2.                          (3.5)
```

It is maximal in the fractional support. For k>=2 it is even **maximum-cardinality** there: a packing with 0,1,2 long cycles has at most `2k, k+1, k+2` cycles respectively. The completion `P union {R}` costs `2k+1`, compared with the global optimum `k+2`.

This is not an integrality gap of the whole LP. It is a failure of maximizing the number of support cycles. New cycles outside the support are necessary to complete this packing, and a correct ledger must pay for the packing's excess count as well as its residual. The series-parallel DP repairs it globally by keeping two terminal paths through every segment, closing them with the returns, and using only one local cycle per segment.

---

## 4. Basic solutions and transition perfect matchings

### 4.1 K5: a basic optimal one-third solution

The following six Hamilton cycles of K5, each with coefficient 1/3, cover every edge exactly once:

```
01234,   01342,   01423,   02143,   02314,   03124.
```

Each edge occurs three times; every pair of listed cycles shares exactly two edges. If B is their edge-incidence matrix, then

```
B^T B = 3 I_6 + 2 J_6.
```

It is positive definite, so the six columns are independent. Setting all other variables to zero gives a **basic feasible solution of the full cycle LP**. Its value is 2, optimal by `y_e=1/5`. Two complementary Hamilton cycles give an integral optimum 2, but no two cycles of the displayed support are edge-disjoint, so no support-only partition exists.

This explicitly rules out invoking TU, or half-integrality of all optimum basic solutions. Denominators and the integer objective gap are different phenomena.

### Theorem 4.2 — arbitrary local fractional matching data extends optimally

Let N>=4 be even, and let `M_ab>=0` for unordered pairs of `{1,...,N}` satisfy only

```
sum_{b != a} M_ab = 1   for each a.                                    (4.1)
```

There is an optimal fractional Hamilton decomposition of `K_(N+1)` whose transition weights at vertex 0 are exactly M.

**Construction.** For each unordered pair a<b and each of the `(N-2)!` orders of the other vertices, give the cycle

```
0, a, [the other N-2 vertices in that order], b, 0
```

weight `M_ab/(N-2)!`.

The spokes at 0 have load one by (4.1). For a nonspoke edge ij, conditioned on the two path endpoints a,b, its probability of appearing in the uniformly ordered Hamilton path is respectively

```
0, 1/(N-2), 2/(N-2)
```

when both, exactly one, or neither of i,j is an endpoint. Its total fractional load is therefore

```
[ 2 sum_ab M_ab - sum_{ab containing i} M_ab
                   - sum_{ab containing j} M_ab ] / (N-2)
= [N-1-1]/(N-2) = 1.
```

The total mass is N/2. Uniform edge weights `1/(N+1)` are feasible and have objective N/2, proving optimality. The transition at 0 of each constructed cycle is precisely ab. □

Take N=6r and partition its neighbours into 2r triples. Put weight 1/2 on each of the three pairs inside every triple and zero elsewhere. Each odd triple has transition cut weight zero, violating the perfect-matching blossom inequality requiring at least one. Any integral perfect matching uses at least r pairs outside this support: each triple needs an outgoing pair, and one such pair serves at most two triples. The bound is attained by pairing one vertex from each of two triples and matching the remaining pairs internally.

This failure can occur at an optimal **basic** solution too. Take an extreme point of the nonempty optimal face that sets all outside-triple transition columns to zero. The three degree equations within each triple force its three transition weights to be 1/2 in every point of this face. A face's extreme point is an extreme point of the original feasible polytope, so choosing a basic optimum does not supply the missing blossom inequalities.

Thus exact unit edge constraints, evenness, and **global fractional optimality** do not supply local blossom inequalities. Nor is there a universal “one new transition per eliminated vertex” rule. These are bad *optimal solutions*, not graphs in which every optimal solution violates blossoms: the complete graph also has an integral Hamilton partition. The theorem blocks an automatic inference from optimality, not the possibility of selecting a better optimum. It does not refute an O(n) global budget: here r itself is O(n), and how charges can be shared across different vertices remains the issue.

At degree four the contrast is instructive. A degree-feasible fractional matching on four incident edges automatically satisfies every odd-cut inequality: an odd subset has size one or three, and its cut has weight one. Nevertheless the next section has a linear global gap. Adding all local blossom inequalities does not solve the global coupling problem.

---

## 5. The Petersen line graph: a fully specified base gadget

Let P be the standard Petersen graph: outer 5-cycle 0,...,4, spokes `i(i+5)`, and inner edges `(5+i)(5+(i+2 mod 5))`. Label the vertices of `L(P)` by the following ordered list of Petersen edges:

```
0:01  1:04  2:05  3:12  4:16  5:23  6:27  7:34
8:38  9:49  10:57  11:58  12:68  13:69  14:79.
```

The root is 0, with left ports 1,2 and right ports 3,4. The four cycles below are Hamilton, and every edge of L(P) occurs in exactly two of them:

```
H00 = (0,1,2,10,14,9,13,4,12,11,8,7,5,6,3)
H01 = (0,1,9,7,5,3,6,14,10,2,11,8,12,13,4)
H11 = (0,2,1,7,9,13,14,6,10,11,12,8,5,3,4)
H10 = (0,2,11,10,6,5,8,7,1,9,14,13,12,4,3).                           (5.1)
```

This is a direct 30-edge identity, checked exactly by the script. It proves `c_f(L(P))=2`, with lower certificate `y_e=1/15`.

The complement of H00 is the disjoint union of

```
B = (0,2,11,10,6,14,13,12,8,5,3,4),       T = (1,7,9).                 (5.2)
```

Thus `{H00,B,T}` is a partition of size 3.

### 5.1 Why size 3 is a GLOBAL minimum

First, P has no Hamilton cycle. A perfect matching has an odd number of spokes. Five spokes give one matching. Three spokes are impossible, since the two unmatched outer indices would need difference both +/-1 and +/-2 modulo 5. One spoke forces the matchings on the remaining outer and inner paths, giving five more possibilities. The complement of each of these six matchings is two 5-cycles. A Hamilton cycle's complement would be a perfect matching, so none exists.

We use the following elementary direction of the Kotzig line-graph argument. If a cubic graph X has a decomposition of L(X) into two Hamilton cycles, each vertex triangle of L(X) is split 2+1 between their two colours. Select the X-edge corresponding to the middle vertex of its two-edge path. At its other endpoint it must also be a middle vertex, in the other colour, since each colour has degree two at that line-graph vertex. These selected X-edges form a perfect matching M.

After deleting M, the remaining 2-factor has the same component structure as either coloured Hamilton cycle after suppressing the matching-edge detours. Inserting a detour at one endpoint of a matching edge does not join different components of that 2-factor. Hence the 2-factor is connected, giving a Hamilton cycle of X.

Apply this to P. A two-cycle partition of a 4-regular graph would consist of two Hamilton cycles, because every vertex must belong to both. It is impossible here. Thus

```
c(L(P))=3,       c_f(L(P))=2.                                         (5.3)
```

This argument is also recorded in the local source `/corpus/src/2106.10368/2106.10368.tex`, especially its cubic reconstruction near lines 89–94; the needed direction has been proved above rather than merely imported.

For the **global minimum** partition in (5.2), uniform-on-old-cycle prices give H11 weight

```
3/15 + 10/12 + 2/3 = 17/10.
```

So even this minimum partition does not produce a feasible dual by uniform pricing.

---

## 6. A sharp global Petersen-ring calculation

### Theorem 6.1

For every t>=2 there is a connected simple 4-regular graph R_t with

```
|V|=14t,   |E|=28t,   c_f(R_t)=2,   c(R_t)=t+2.                       (6.1)
```

In particular `c-c_f=t=n/14`. A universal constant-factor comparison to c_f is false; a linear additive error is genuinely necessary. Any universal bound `c<=c_f+C n` must have `C>=1/14`.

### 6.1 Construction, integer upper bound, and fractional Hamilton cover

Let H=L(P)-0. Take t disjoint copies H_i, cyclically indexed, and add edges

```
(i,3)--(i+1,1),         (i,4)--(i+1,2).                                (6.2)
```

All vertices have degree four and all edges are distinct. Let `P_ab=H_ab-0`, oriented from left port `1+a` to right port `3+b`. Each P_ab is a spanning path of H. Also let Q=B-0, from port 2 to port 4.

Concatenate P00 in every block using the first connector of (6.2); concatenate Q using the second connector. Keep the triangle T in every block. This is an exact partition

```
D_t = {one cycle of length 14t, one of length 11t, t triangles},        (6.3)
```

so `c<=t+2`.

For a fractional cover, choose a proper colouring of the cycle of t positions by the three nonzero linear forms on F_2^2. For even t, alternate the two coordinate forms. For odd t, alternate them on the first t-1 positions and use their sum on the last. The t=2 case uses the two different coordinate forms.

For each of the four seeds z in F_2^2, let s_i be the value of the form at position i. Traverse P_(s_(i-1),s_i) in block i, and use connector s_i to the next block. This is a Hamilton cycle. At each block, the two adjacent, distinct forms are independent, so over the four seeds each of the four paths P_ab occurs exactly once. By (5.1), every internal edge is therefore used twice. Each connector is used twice as well. Give these four global Hamilton cycles weight 1/2 each.

The uniform dual `y_e=1/(14t)` is feasible for **every** simple cycle, by its length bound, and has value two. This proves `c_f=2` exactly.

### 6.2 Each block forces an internal cycle

In any global partition, suppose no whole cycle lies in H_i. Restrict all cycles to H_i. Its four boundary edges yield exactly two simple paths with the four distinct ports as endpoints.

Every nonport vertex has internal degree four, so both paths must pass through it. Each port has internal degree three: it is an endpoint of one path and internal to the other. Consequently both paths are Hamilton paths of H_i. Add back the root and its four spokes. The two paths become a Hamilton decomposition of L(P), contradicting Section 5.

Thus there are at least t cycles wholly inside blocks, and at least one cycle using connectors. This gives `c>=t+1`, but one more argument is needed for the exact global minimum.

### 6.3 The cap lemma

**Lemma.** Suppose H has a Hamilton cycle J and its remaining edges are exactly two vertex-disjoint paths with endpoints the four ports. Then those paths pair the ports as

```
{1,2}, {3,4},                                                         (6.4)
```

not in either left-to-right pairing.

**Proof.** Regard H as `L(X)` for `X=P-01`. Its two degree-two vertices are the old Petersen vertices 0 and 1; their vertex cliques in L(X) are the single edges 12 and 34 on the respective port pairs.

If the residual paths paired left-to-right, neither of these single edges could be residual: it would itself be a whole same-side residual path, since each port has residual degree one. Thus both belong to J.

At each of the other, cubic X-vertices, the vertex triangle is mixed between J and the residual paths. It cannot be all J (J is a 14-cycle), nor all residual (the residual is acyclic). Apply the middle-edge argument from Section 5. No selected middle edge can be incident with a degree-two X-vertex: at that port, J already uses its same-side port edge and hence uses exactly one edge in the cubic vertex triangle, as does the residual.

The selected middle edges therefore form a matching covering the eight cubic X-vertices and avoiding the two degree-two vertices. Delete this matching. The resulting graph is 2-regular on all ten X-vertices, and suppressing the detours of the connected cycle J shows that it is connected. It would be a Hamilton cycle of P-01, hence of P, a contradiction. □

### 6.4 Exact global lower bound

If a partition had exactly t+1 cycles, it would have exactly one cycle J_i inside each H_i and a single connector-using cycle Z. At every nonport, degree four forces both J_i and Z to pass through it. At a port, Z uses its external edge and exactly one internal edge; J_i uses the other two internal edges. Thus J_i is Hamilton on H_i.

The remaining H_i edges are the two vertex-disjoint restrictions of the one simple cycle Z, with no additional closed components. The cap lemma gives (6.4) in every block. But these same-side caps and (6.2) make **t distinct connector-using cycles**, one between each neighbouring pair of blocks. They cannot form the single Z when t>=2. This contradiction proves `c>=t+2`, completing (6.1). □

This proof concerns the **actual global minimum**, with unrestricted replacement cycles. It does not rely on any bounded batch of old cycles, local rigidity, or local factor optimality.

### 6.5 What this test demands of a rounding proof

* In the optimum fractional support, every cycle is Hamilton. No two can be edge-disjoint: in a 4-regular graph they would constitute a two-cycle partition. Every maximal support packing therefore has size one.
* For each of the four displayed support Hamilton cycles, the residual consists of t triangles and one cycle of length 11t. Thus

  ```
  c_f(R_t - C)=t+1,       c_f(R_t)=2.                                  (6.5)
  ```

  A single support-cycle deletion can increase the residual fractional optimum by Theta(n). The false induction `c_f(G-C)<=c_f(G)-1+O(1)` fails even on this very explicit optimum support.
* All degree-four transition marginals satisfy the perfect-matching blossom inequalities. The global gap survives imposing all such local constraints.
* For the global minimum D_t in (6.3), concatenate P11 in every block to get another Hamilton cycle C'. It uses 3t edges of the old 14t-cycle, 9t of the old 11t-cycle, and 2t triangle edges. Its uniform-on-D_t weight is

  ```
  3/14 + 9/11 + 2t/3 = 159/154 + 2t/3.                                (6.6)
  ```

  This violates the dual inequality by Theta(n), despite global minimality. The correct uniform-on-the-WHOLE-GRAPH dual has value two and total slack t on D_t; it charges one unit per gadget.

The last distinction is central: a legitimate linear loss can be structural and global even when every vertex-level matching is perfectly feasible.

---

## 7. A dense residual obstruction for near-optimal basic supports

The following does **not** assert optimality of its fractional point. Its exact excess above optimum is 1/2, and that qualification must not be dropped.

### Proposition 7.1

For every odd prime p>=5 there is a basic fractional cycle partition of K_p of cost p/2, with p support cycles, such that:

* every support cycle has length p-1;
* every two support cycles share exactly one edge;
* every maximal integral packing from the support has size one;
* its residual has minimum degree p-3.

**Construction and proof.** Work in F_p and choose a primitive element beta. For each c put

```
C_c = (c+1, c+beta, ..., c+beta^(p-2)).                                (7.1)
```

This is a cycle through every vertex except c. For distinct c,d the unique common edge has endpoints

```
u=(d+beta c)/(1+beta),       v=(c+beta d)/(1+beta).                     (7.2)
```

The denominators are nonzero because a primitive element at p>=5 is not -1. At centre c, `(v-c)/(u-c)=beta`, and at centre d the reverse ratio is beta. Conversely the two possible centres of any edge are obtained by solving these two linear equations, so (7.2) is unique. Every edge is in exactly two cycles. Coefficients 1/2 therefore give the stated fractional cover.

The support columns are independent. After identifying each edge with its pair of centres, a linear dependence would say `z_c+z_d=0` for every distinct c,d, which forces all z_c=0. Thus this point is basic in the full equality-constrained cycle LP.

Every support packing has at most one cycle. Deleting C_c leaves degree p-1 at c and degree p-3 elsewhere. This residual is even and has quadratic edge count and nullity.

Finally `c_f(K_p)=c(K_p)=(p-1)/2`: uniform edge weights 1/p give the lower bound, and the usual Walecki Hamilton partition attains it. Thus the point in (7.1) is exactly +1/2 near-optimal. □

This disproves claims that maximal packing from a **basic**, O(n)-mass, or even +1/2 near-optimal fractional support automatically leaves bounded degree or O(n) nullity. It does not disprove such a statement with a carefully chosen *exactly optimal* support and additional hypotheses. K5 and the theta chain separately show why support-only exact partitioning and the inequality `|packing|<=c_f` are false even for exactly optimal supports.

---

## 8. A useful correction to the proposed ledgers

For any edge-disjoint cycle packing P in an even graph, the remainder H is even and

```
c(G) <= |P| + beta(H).                                                 (8.1)
```

Indeed the cycles of any edge partition of H are linearly independent in its binary cycle space, since they have disjoint nonempty edge sets. Their number is at most beta(H). Thus a sufficient, directly checkable packing certificate is

```
(|P|-c_f(G)) + beta(H) <= C r(G).                                      (8.2)
```

No universal existence assertion for such a packing is made. Equation (8.2) is a diagnostic account, not a new proof of the target:

* the (4,2) chain shows that its first term can be positive even for a maximum packing from optimal support;
* the dense prime-order family shows that the residual term can be quadratic for near-optimal basic support;
* the Petersen ring shows that an optimal support can leave a real linear residual cost, while a per-deletion bound on c_f fails.

There is a second tempting fix that also needs qualification. Let

```
b_D(e)=1/|D_j| when e belongs to D_j,
a_G(uv)=(1/d_G(u)+1/d_G(v))/2.
```

A universal prescription `y=b_D-K a_G` cannot work on all global minimum partitions. Start with the minimum Petersen partition from (5.2), where H11 has b-weight 17/10. Attach s private triangles at each core vertex. Articulation additivity keeps the enlarged partition globally minimum, but every core degree becomes `4+2s`. On H11 the proposed weight is

```
17/10 - K * 15/(4+2s) > 1
```

for sufficiently large s. This only refutes the **frozen ambient-degree prescription** on unrestricted graphs; a block-aware or laminar charge might avoid it. It does not refute the desired existence of some signed certificate.

The positive series-parallel argument uses a different mechanism: retain terminal paths, optimize their simultaneous traffic, then close them. Its signed path prices can be very negative on a bottleneck return. That is exactly what a blanket nonnegative correction or independent local rounding would miss.

---

## 9. Exact remaining gap and a refined target

The proved results do not justify any of the following universal implications:

* degree-feasible fractional transitions => convex combinations of perfect matchings;
* local matching/blossom feasibility => a globally compatible partition into simple cycles;
* a maximum or maximal support packing => a cheap residual, or even `|P|<=c_f`;
* deleting an optimal-support cycle => only O(1) increase in the residual fractional objective;
* a global minimum D => feasibility of uniform-on-D prices;
* a basic solution => TU, half-integrality, or only O(n) individual-edge constraints.

What succeeds in Theorem 1.1 is very specific. A one- or two-terminal interface permits a scalar **amount of path traffic** to summarize all relevant compatibility information; the children have disjoint interiors, so the reconstructed cycles are genuinely simple. Monotonicity of `F+p/2` then selects a componentwise maximum feasible traffic pair, with the correct parity, and gives an exact global optimum.

At a four-port interface, the Petersen example shows why a scalar traffic count, or even each vertex's perfect-matching polytope, loses essential information. A valid extension must retain enough pairing and connectivity information to pay for the forced internal cycles. It must also prove that the total cost of repairing these global incompatibilities, over all eliminations/separations, is bounded by a **single** O(r(G)) ledger, not O(n) afresh at each density or elimination scale. The examples here do not provide that global ledger.

In dual language, the unresolved assertion remains: from an actual global minimum D in an arbitrary even simple graph, construct unrestricted signed edge weights satisfying every simple-cycle inequality and losing at most Cn in total value. On the series-parallel class the loss is zero, on the Petersen rings the exact necessary loss is n/14, and on the odd-cover chain negative edge (even negative cycle) prices are indispensable despite zero loss.

**No unrestricted additive-O(n) rounding theorem, and hence no solution of the unchanged Spec, has been obtained in this work.**

---

## 10. Reproducible verification

Run from the project root:

```
OPENBLAS_NUM_THREADS=1 PYTHONHASHSEED=0 python3 Submission/ResearchRoundingCheck.py
```

The checker requires only the installed NetworkX, NumPy and SciPy packages. General proofs above do not depend on numerical optimization. Where a solver is used, its proposed partition and signed dual are converted to exact rational witnesses and checked against every enumerated cycle.

Checks include:

* 200 generated simple series-parallel networks, all with even internal degrees, of which 62 are even at both terminals. There were **391 parity-eligible integral state checks** and **600 fractional traffic state checks**. The dynamic-program partition, compact dual inequalities, **all** simple-cycle inequalities, **all** terminal-path inequalities, and exact objective equality are checked independently.
* 35 theta-chain parameter choices, with independent all-cycle enumeration for 21 smaller instances; the odd cover, signed objectives, uniform-price violations, negative return-cycle weight, and maximum-support-packing count identities. The positive-support fractional optima used in the forced-sign arguments are also checked edge by edge with exact rational coefficients.
* The K5 one-third basic point, its exact Gram matrix, optimal integral partition, and all cycle inequalities for the lower certificate. The K_(2,6) half-integral basic example from Section 1 is checked separately, including its full-rank Gram matrix and an integral/dual optimum of value 3.
* The universal transition extension at complete graph orders 5,7,9; exact unit edge coverage and prescribed transition weights, including the violated odd-cut constraint. Explicit minimum-new-transition matchings for eight values of r.
* All 7,514 cycles and 160 Hamilton cycles in L(P); its six Petersen perfect matchings; the four-cycle fractional certificate; the exact three-cycle partition; all 52 Hamilton cycles of the punctured gadget. Exactly 32 leave just two paths, always with the same-side cap pairing.
* Petersen rings at `t=2,3,4,5,8,12,20,40`, up to **560 vertices and 1,120 edges**: simplicity, 4-regularity, exact integer and fractional edge coverage, all four residual 2-factors, and (6.6). Global minimality is proved in Section 6, not inferred from a heuristic solver on the large rings.
* The intersecting-support family at 15 primes through 101, including the exact common-edge formula, fractional coverage, high residual minimum degree, and a separate Walecki optimum.
* A signed two-edge-splice certificate on 18 vertices, checked against all **436** simple cycles of the result; both optima are 5.
* All 84 nonzero-order even graphs in the NetworkX atlas through order 7: 7 edgeless, 45 nonempty series-parallel and 32 other graphs. Each nonempty instance has an exact partition and dual with the same value. This finite agreement is not extrapolated to arbitrary graphs.

**All checks passed.** The checker verified the Spec hash before and after its tests. A separate SHA-256 comparison confirmed that all 13 pre-existing Submission files, including the Spec and prior research/Lean files, were unchanged. Only this research note and its targeted checker are new.
