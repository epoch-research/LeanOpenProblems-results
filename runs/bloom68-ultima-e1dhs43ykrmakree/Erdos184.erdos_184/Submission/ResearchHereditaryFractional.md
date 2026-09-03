# Hereditary fractional circuit partitions: a factor-two lower bound and a global-optimum sampling obstruction

## Status

**The existence of a finite universal `K` with `c(M) <= K Fmax(M)` is NOT resolved here.** In particular, this note does not prove `K=2`, does not construct a family with `c/Fmax` unbounded, and does not prove the graphic Erdős–Gallai assertion. The distinction between the hereditary maximum and the fractional value of the whole ground set is retained throughout.

There are nevertheless several rigorous new conclusions about this proposed route:

1. **No `K<2` works for general binary matroids.** An explicit connected, simple binary family `M_n`, `n>=5`, has

   ```
   c(M_n)=2,       cf(M_n)=Fmax(M_n)=n/(n-2),
   c(M_n)/Fmax(M_n)=2-4/n.
   ```

   Every proper nonzero binary cycle is a circuit, so **all** Eulerian restrictions are accounted for. `M_5` is the stated `R10` example. The members with `n>=6` are nonregular; explicit forbidden-minor certificates are given below. Thus the lower threshold 2 is genuinely binary, not an asymptotic regular or graphic counterexample.

2. **A connected counterexample to `c<=ceil(Fmax)`.** A related simple connected binary matroid on 20 elements, of rank 11, has

   ```
   c=3,       cf=5/3,       Fmax=2.
   ```

   Its 512 binary cycle vectors and 255 circuits are completely classified. This is not just a direct sum of `R10`s. Explicit binary columns are supplied in Section 3.5. It is nonregular.

3. **The proposed whole-circuit sampling proof has a stronger barrier than the `R10` test.** A family `M_(n,t)` has **every** ground-set circuit partition globally minimum, of size `q=t+1`. Nonetheless, for every exchangeable law on subfamilies of any such partition—this includes independent common-probability retention and uniformly choosing a fixed number of circuits—

   ```
   sup E[cf(union of retained circuits)] / q  ->  1/4
   ```

   along `t->infinity`, `n=t^2+5`. Consequently **no such sampling proof with denominator `K<4` can be valid**, even if the retention probability or retained cardinality is optimized separately for every instance. This does **not** refute the desired inequality with `K=2`: in this family `Fmax=t` and `c=t+1`. It also does not rule out nonexchangeable, structurally chosen subfamilies, or an exchangeable proof with a larger constant.

4. **An exact positive hereditary calculation in a regular class.** For `a,b>=3`,

   ```
   Fmax(M*(K_(a,b)))=max(a-1,b-1),       c(M*(K_(a,b)))=2.
   ```

   Thus the small full-ground-set fractional value of these cographic examples does not survive hereditary maximization.

5. The abstract signed-dual formulation, a useful condition on a minimal maximizing restriction, and the elementary logarithmic bound are recorded in Section 1. None is silently promoted to constant-factor rounding.

All results are at paper level, not Lean formalizations or literature-priority claims. The checker is the new file `ResearchHereditaryFractionalCheck.py`; it uses **only the Python standard library and exact arithmetic**. No existing research file or specification was edited.

---

## 1. The actual invariant and the remaining abstract problem

Let `Z(M) <= F_2^E` be the binary cycle space of a finite binary matroid. Its nonzero support-minimal words are the circuits. A binary cycle is a disjoint union of circuits. Assume `1_E in Z(M)`.

For every `F in Z(M)`, including the empty set, define

```
c(F)  = minimum number of circuits in an edge/element partition of F;
cf(F) = min sum_C x_C,
        sum_{C containing e} x_C = 1 for e in F,  x_C>=0,
        with C a circuit contained in F;
p(M)  = Fmax(M) = max_{F in Z(M)} cf(F).
```

Empty restrictions have both costs zero. These are **exact partitions**, not covers or odd covers.

### 1.1 A single gauge, evaluated on every binary cycle

Put

```
Y(M) = { y in R^E : y(C)<=1 for every circuit C of M }.
```

Zeros in the right-hand side force every circuit leaving `F` to have primal coefficient zero. Finite-dimensional LP duality therefore gives

```
cf(F) = max_{y in Y(M)} y(F),
p(M)  = max_{F in Z(M)} max_{y in Y(M)} y(F).                (1.1)
```

The variables `y_e` are unrestricted in sign. Equivalently, a dual on `M|F` can be extended to the whole matroid by putting sufficiently large negative prices outside `F`; finiteness controls all the additional inequalities.

A useful convex-geometric formulation is

```
P = conv{1_F : F in Z(M)},
B = conv({0} union {1_C : C a circuit}),
p(M) = min{lambda>=0 : P subseteq lambda B}.                (1.2)
```

Here `P` is centrally symmetric about `1_E/2`. Formula (1.2) does not give a monotone integral path or a disjoint circuit partition. Treating that missing implication as a general integrality property would beg the question.

### 1.2 Heredity and direct sums

If `D` is a globally minimum partition and `A subseteq D`, then

```
c(union A)=|A|.                                             (1.3)
```

Otherwise replace `A` by a smaller partition. This does not imply `cf(union A)=|A|`.

Also, `p(M|F)<=p(M)` for an Eulerian restriction. For a direct sum,

```
c(M1 direct_sum M2)=c(M1)+c(M2),
p(M1 direct_sum M2)=p(M1)+p(M2).                            (1.4)
```

Circuits stay in one summand, and the maximum over Eulerian restrictions separates. Consequently direct sums amplify an additive or ceiling failure, but not its ratio.

### 1.3 A genuine critical-restriction consequence

Suppose `E` is nonempty. Choose, among restrictions attaining `p(M)`, one `F` with minimum cardinality, and let `y` be any optimal dual on `M|F`. Then

```
0 < y(C) <= 1     for every circuit C contained in F.        (1.5)
```

Indeed, if `y(C)<=0`, deleting `C` preserves Eulerianity and gives

```
cf(F\C) >= y(F)-y(C) >= p(M).
```

A strict inequality contradicts maximality; equality contradicts the choice of `F`. This uses the **actual hereditary maximum** and the signed dual, not clipping negative edge prices. It does not imply edgewise nonnegativity or an integral optimum. The family in Section 2 satisfies the conclusion with a positive uniform dual while its ratio approaches 2.

### 1.4 An unconditional, but only logarithmic, bound

For `m=|E|`,

```
c(M) <= p(M) H_m <= p(M)(1+log m)       (m>=1).             (1.6)
```

To see this, in any nonempty Eulerian residual `F`, an optimal fractional partition shows that some circuit has at least `|F|/p(M)` elements. Delete a longest circuit. If this changes the residual size from `s` to `s-l`, then

```
1 <= p(M) l/s <= p(M) sum_{j=s-l+1}^s 1/j.
```

Summing proves (1.6). This is the ordinary greedy hereditary argument. Removing its logarithm is not accomplished here.

For simple graphic matroids, the audited input in `ResearchFractional.md` gives

```
p(M(G)) <= r(G)
```

because it applies to **every even restriction**. Thus a finite universal graphic or binary `K` really would imply the desired linear cycle count. No graphic theorem is assumed in the arguments below.

---

## 2. A connected binary family proving that `K` must be at least 2

### 2.1 Explicit cycle-space presentation

Let `E_n` be the edge set of the bookkeeping complete graph `K_n`. Write

```
Z_n = Cut(K_n) + <1_(E_n)>                 over F_2.         (2.1)
```

Define `M_n` to be the binary matroid with cycle space `Z_n`. This is a constructive binary representation: form a matrix `B_n` with `n-1` independent vertex-incidence rows of `K_n` and one all-ones row. Then `M_n` is dual to the column matroid of `B_n`; alternatively, take as a representing matrix for `M_n` any row basis of the orthogonal complement of the row space of `B_n`.

Since `K_n` is nonbipartite, its full edge set is not a cut. Consequently

```
dim Z_n = n,
m_n = |E_n| = n(n-1)/2,
r(M_n) = m_n-n,
1_(E_n) in Z_n.                                             (2.2)
```

In particular, the columns of a representing matrix for `M_n` xor to zero.

**These are not the graphic matroids of `K_n`.** Their binary cycles are cuts and complements of cuts of the bookkeeping graph.

### 2.2 Complete circuit classification

For `n>=5`, **every proper nonempty word of `Z_n` is a circuit**. Thus there are exactly `2^n-2` circuits.

Here is a proof of all the necessary noncontainments.

* Every nontrivial cut of `K_n` is a bond, so no such cut properly contains another nontrivial cut. The same statement, with inclusions reversed, applies to their complements.
* Two nontrivial cuts of `K_n` cannot be disjoint. A nontrivial cut, viewed as a spanning complete bipartite graph, is connected; a cut disjoint from all its edges would have to be trivial.
* If the complement of one cut were contained in another cut, those two cuts would cover `E_n`. The pair of side-membership bits would then properly color `K_n` with at most four colors. This is impossible for `n>=5`.

These exhaust inclusions between cuts and complements of cuts. All the proper nonzero words are therefore minimal. Conversely the full word is not minimal, since a proper circuit and its complement partition it.

In fact **every partition of `E_n` has exactly two circuits**. Three or more pieces would have a proper union of two pieces, contradicting the just-proved minimality of every proper nonzero cycle.

The matroid is simple: the smallest circuit has size at least four. It is connected: for any two bookkeeping edges, choose a vertex incident with neither (there is one when `n>=5`). The complement of that vertex's star is a circuit containing both edges.

### 2.3 Exact fractional value and the hereditary maximum

Set

```
L_n = (n-1)(n-2)/2 = m_n-(n-1),
U_n = floor(n^2/4).
```

For `n>=5`, `U_n<=L_n`. A cut has size at most `U_n`; a proper complement of a cut has size at most `L_n`. Hence every circuit has length at most `L_n`.

There is an exact primal certificate: use each of the `n` circuits

```
E_n \ delta(v),        v in V(K_n),
```

with coefficient `1/(n-2)`. An edge belongs to exactly `n-2` of them. The cost is `n/(n-2)`.

There is an exact dual certificate: put `y_e=1/L_n` on every element. Its inequality holds for **every** circuit by the length bound, and its value is

```
m_n/L_n = n/(n-2).
```

Every proper nonempty Eulerian restriction is itself a circuit, so its fractional value is exactly one. We obtain

```
c(M_n)=2,
cf(M_n)=Fmax(M_n)=n/(n-2),
c(M_n)/Fmax(M_n)=2-4/n.                                   (2.3)
```

For any proposed `K<2`, choosing `n>4/(2-K)` disproves that value of `K` on a connected simple binary matroid. This proves a lower threshold of 2, **not a failure of every finite constant**.

### 2.4 Regularity scope and exact minors

`M_5` is `R10`. With lexicographically ordered `K_5` edges, the coordinate permutation

```
[0,1,4,5,2,9,8,7,3,6]
```

identifies its cycle code with the kernel of the binary reduction of the `R10` matrix `[I_5 | B]` in `ResearchRegular.md`, where each column of `B mod 2` has ones in three consecutive cyclic positions. The checker verifies the whole-code equality; the prior note supplies its TU representation.

For `n>=6`, `M_n` is nonregular. It suffices to give an `F7*` minor in the dual of `M_6`. Label the vertices `0,...,5`. In the column matroid of `B_6`, contract

```
01, 23
```

and retain only

```
04, 14, 05, 15, 24, 34, 25.
```

The contracted columns have rank two. The seven remaining quotient columns have rank four, and their binary dependence space consists of zero and seven words of weight four. Explicitly, in the displayed seven-coordinate order the dependence masks are

```
0, 15, 51, 60, 85, 90, 102, 105.
```

The dependency basis with masks `15,51,85` has columns `[7,3,5,1,6,2,4]`, exactly the seven nonzero vectors of `F_2^3`. The quotient is therefore `F7*`. Dualizing gives an `F7` minor in `M_6`. Restricting the dual presentation for any larger `n` to a `K_6` gives the same dual matroid, so this proves nonregularity for all `n>=6`.

A second, redundant exact check finds an `F7` minor in the dual of `M_7`: contract `01,12,34,56` and retain `02,03,04,05,06,35,36`. The quotient is simple rank three on seven elements.

Thus (2.3) supplies **no asymptotic lower threshold 2 for the regular or graphic classes**. On regular matroids it recovers the known `R10` ratio `6/5`.

---

## 3. Synchronizing the coset bit: all restrictions and all integral optima

This construction provides the sampling obstruction without using a bad partition.

### 3.1 Definition

Take `t>=1` disjoint copies `E_1,...,E_t` of `E_n`, `n>=5`, and define

```
Z_(n,t) = (direct_sum_i Cut(K_n on E_i)) + <1_E>,
E = disjoint_union_i E_i.                                  (3.1)
```

Let `M_(n,t)` have this binary cycle space. The cut choices in different blocks are independent, but the cut-versus-complement bit is **one shared bit**. The representation has the independent incidence rows in each block and a single global all-ones row; dualizing gives an explicit original binary matrix.

```
|E|=t m_n,       dim Z_(n,t)=t(n-1)+1,
r(M_(n,t))=t L_n-1.                                        (3.2)
```

Every binary cycle is exactly one of the following:

* **even-coset type:** in each block, a cut, possibly empty;
* **odd-coset type:** in each block, the complement of a cut, possibly the full block.

The words “even/odd coset” here refer to the shared bit, not to the number of elements of a set.

The complete circuit list is:

* one nontrivial cut in one block, empty in all other blocks (**local circuits**);
* a proper complement of a nontrivial cut in **every** block (**global circuits**).

Indeed, the noncontainments in Section 2 rule out a local cut inside a proper complementary trace. In an odd-coset word with no full block, every trace is already a proper circuit of `M_n`, so no smaller odd-coset word fits. A full block or more than one nonzero cut immediately supplies a proper local circuit.

The matroid is simple and connected. In particular any two elements can be placed in a single global star-complement circuit, choosing an unused star center in each relevant block.

### 3.2 Every integral partition has the same size

For an even-coset restriction, let `k` be the number of nonzero block cuts. Its only contained circuits are precisely those `k` cuts. Its partition is forced.

For an odd-coset restriction, let `k` be the number of **full** blocks. Every partition has exactly one global circuit:

* it needs an odd number of global circuits to give the odd shared bit;
* it cannot contain two disjoint global circuits, since their two complementary-cut traces in any block would be disjoint, contradicting the four-color argument from Section 2.

On a nonfull block the global trace is forced to be the whole restriction there, and no local circuit fits. On each full block, the complement of the chosen global trace is one nontrivial cut, hence exactly one local circuit. Therefore **every** partition has `k+1` pieces.

In particular,

```
every circuit partition of E has t+1 pieces;
c(M_(n,t))=t+1.                                             (3.3)
```

This is a global structural lower bound, not a local-exchange test or a solver-reported optimum.

### 3.3 Exact fractional values for EVERY Eulerian restriction

Write

```
alpha = m_n/L_n = n/(n-2),
beta  = (n-1)/U_n.                                         (3.4)
```

The complete table is

| Restriction type | Parameter | Integer cost | Exact fractional cost |
|---|---:|---:|---:|
| even coset | `k` nonzero block cuts | `k` | `k` |
| odd coset, not all blocks full | `k<t` full blocks | `k+1` | `1+k beta` |
| full ground set | `k=t` | `t+1` | `alpha` |

Here are exact certificates, including the signed one needed in the middle row.

**Even row.** Only the `k` local circuits are present. Use each with weight one. For a dual, put price one on one chosen element of each of these circuits, and zero elsewhere.

**Full ground set.** Independently choose a star center in every block and take the union of their star complements. Give the resulting `n^t` global circuits total mass `alpha`, uniformly. Every edge has load `alpha(n-2)/n=1`. For the dual, give every edge price `1/(t L_n)`. Every global circuit has at most `t L_n` edges and a local cut has at most `U_n<=L_n` edges. The objective is `alpha`.

**Odd row with `k<t`.** In every nonfull block, keep the complementary-cut trace fixed. On each of the `k` full blocks, use a uniform star complement. These choices give a distribution on global circuits of total mass **one**, covering each frozen block exactly and loading each full-block edge `(n-2)/n`.

On each full block, distribute local mass `beta` uniformly over balanced cuts. Such a cut has `U_n` edges and its uniform distribution has edge inclusion probability `U_n/m_n`. Its load is

```
beta U_n/m_n = 2/n,
```

exactly the missing amount. This is an exact fractional partition of cost `1+k beta`.

For a dual, put `1/U_n` on every edge of every full block. Choose one edge in any one frozen block and put on it the additional price

```
gamma = 1-k L_n/U_n,                                       (3.5)
```

putting zero on all other frozen-block edges. This price may be negative. Every permitted global circuit uses the chosen edge and has at most `L_n` edges in each full block, so its weight is at most `gamma+k L_n/U_n=1`. The only other permitted circuits are local cuts in full blocks, each of weight at most one. The dual objective is

```
gamma+k m_n/U_n = 1+k(n-1)/U_n = 1+k beta.
```

This certifies every circuit in the restriction, not merely the primal support.

### 3.4 The hereditary maximum and why this is not an unbounded-ratio construction

For `n>=5`, `alpha<=5/3` and `0<beta<1`. Thus

```
Fmax(M_(n,1)) = alpha,
Fmax(M_(n,t)) = t                    for t>=2.              (3.6)
```

For `t>=2`, the middle row is at most `1+(t-1)beta<=t`, the full row is less than two, and the even row attains `t` by choosing a nontrivial cut in every block.

Consequently

```
c/Fmax = (t+1)/t     for t>=2.                              (3.7)
```

The family has an arbitrarily large full-ground-set integrality gap, but the **actual hereditary maximum dominates it up to a constant**. This is exactly why a low `cf(E)` alone is not a counterexample to the question.

### 3.5 A compact connected ceiling counterexample

Take `n=5,t=2`. One original binary representation, giving each rank-11 column as an integer bit mask, is

```
[2044,2035,21,26,2047,1,2,4,8,16,
 224,800,1344,1664,32,64,128,256,512,1024].                    (3.8)
```

The columns are distinct and nonzero, have rank 11, and xor to zero. The ground set consists of two lexicographically ordered ten-edge blocks. A minimum partition, as 20-bit support masks, is

```
15, 15360, 1033200.
```

The first two are four-element local circuits; their union is the Eulerian restriction with fractional value two. The third is a twelve-element global circuit. Formula (3.6), not just this witness, proves the upper bound over all 512 Eulerian restrictions:

```
c=3 > ceil(Fmax)=2,       cf(E)=5/3.
```

There are `2*15+15^2=255` circuits. Every partition of the whole ground set has three pieces.

This example is nonregular. In its dual presentation, contract `01,23` in block one and the star `01,02,03,04` in block two. Retain the following seven columns:

```
block two: 12;
block one: 02,03,04,14,24,34.
```

The contracted rank is six and the retained quotient is simple rank three on seven elements: `F7`. The original matroid therefore has an `F7*` minor. For all `t>=2,n>=5`, restricting the dual to two `K_5` blocks yields this obstruction. Together with Section 2.4, the only regular member of the displayed `M_(n,t)` family is `M_(5,1)=R10`.

---

## 4. Why unbiased whole-circuit sampling cannot prove the desired factor 2

Fix **any** partition `D` of `M_(n,t)`. By Section 3.2 it is globally minimum and consists of one global circuit `B` and one local cut `A_i` in each block. Put `q=t+1`.

For every subfamily of `D`:

* if `B` is absent and `k` local circuits are retained, its fractional value is `k`;
* if `B` is present and `k<t` local circuits are retained, it has `k` full blocks and fractional value `1+k beta`;
* if all of `D` is retained, its fractional value is `alpha`, not `1+t beta`.

These values do not depend on which globally minimum partition was chosen.

### 4.1 Independent retention with common probability `p`

The exact expectation is

```
E cf = t p(1-p) + p + beta t p^2
       - p^(t+1) (1+beta t-alpha).                         (4.1)
```

The final correction is essential: it accounts for retaining the entire partition, whose fractional value drops to `alpha`.

For the one-block family alone, fair-coin retention gives `1/2+alpha/4`, which tends to `3/4` while `|D|=2`. Thus even that globally optimal test already invalidates a fair-coin expectation lower bound `|D|/2`.

The synchronized family is stronger. Since `1+beta t-alpha>=0`, uniformly in `p in [0,1]`,

```
E cf <= t/4 + 1 + beta t.                                  (4.2)
```

Taking `n=t^2+5` makes `beta<4/n`, so the right-hand side is `(1/4+o(1))q`. The common probability may vary with the instance; this upper bound still applies.

### 4.2 All exchangeable laws, including fixed-size retention

Call a distribution on subfamilies exchangeable if it is invariant under every permutation of the `q` members of `D`. Conditional on a retained cardinality `s`, it is uniform among the `s`-subfamilies.

For `0<=s<=q-1`,

```
E[cf | size=s]
   = s(q+1-s)/q + beta s(s-1)/q.                           (4.3)
```

Indeed, the global circuit is present with probability `s/q`; the two costs are then `1+(s-1)beta` and `s`. For `s=q`, the expectation is `alpha` instead.

For `s<q`, (4.3) is at most

```
(q+1)^2/(4q) + beta q.
```

Every exchangeable law is a mixture of these laws. Along `n=t^2+5`,

```
sup_exchangeable E[cf]/q
   <= max(alpha/q, 1/4 + 1/(2q) + 1/(4q^2) + beta) -> 1/4.
```

Choosing `s` close to `q/2` supplies the matching limit inferior. Thus the limit of this supremum is exactly `1/4`.

### 4.3 What is refuted, and what is not

This disproves any proposed theorem of the form

> For every globally minimum partition, some exchangeable retention rule has expected hereditary fractional cost at least `|D|/K`,

when `K<4`. It refutes the `K=2` implementation of that probabilistic route even under **full global optimality**, and is not an arbitrary-bad-partition example.

It does **not** refute any of the following:

* `c(M)<=2 Fmax(M)`;
* an exchangeable-retention theorem with `K>=4`;
* a suitably nonexchangeable or structurally adaptive selection theorem;
* an existence theorem choosing an Eulerian restriction not drawn from this sampling law.

Indeed, simply omit the distinguished global circuit and retain all `A_i`: the value is `t`, close to the entire optimum `t+1`. In this family the maximizing restriction is even a subunion of the given partition. The proof of its being the **global** hereditary maximum nevertheless required the classification of all cycle words in Section 3.

---

## 5. A regular positive test: complete bipartite cographic matroids

Let `H=K_(a,b)`, `a,b>=3`, and `N=M*(H)`. It is simple and Eulerian. Its circuits are bonds and its binary cycles are cuts of `H`.

The earlier regular note proves, with exact certificates,

```
c(N)=2,
cf(N)=ab/((a-1)(b-1)+1).                                   (5.1)
```

The hereditary extension is

```
Fmax(N)=max(a-1,b-1).                                      (5.2)
```

For completeness, write a cut as `delta(S)`, with `s` vertices from the first part and `u` from the second in `S`.

* If all four cells `s,a-s,u,b-u` are positive, both induced sides are connected, so `delta(S)` is one bond, with cost one.
* If the restriction is neither empty nor the full edge set, and one side is independent, its only contained bonds are the individual vertex-stars of that side. Its fractional and integral values equal the size of that side, at most `a-1` or `b-1`.
* The remaining cases are the empty cut and the full edge set. In particular, taking an entire bipartition class gives the full edge set and is excluded from the preceding bullet.

The bounds `a-1` and `b-1` are attained by taking all but one vertex in the corresponding part. The full fractional value in (5.1) is less than two, so it cannot exceed these proper-restriction values.

One can also recheck (5.1) directly. Let `L=(a-1)(b-1)+1`. Every bond is a vertex-star or a cut with `1<=s<=a-1`, `1<=u<=b-1`. The latter has size `sb+au-2su`, whose maximum on that rectangle is `L`, attained at opposite corners; the vertex-stars are no larger. For every pair `(u,v)` of opposite-part vertices, the cut of `(A\{u}) union {v}` is a bond with `L` edges. Each edge is in exactly `L` of these `ab` labelled bonds; coefficient `1/L` gives a primal, and uniform price `1/L` gives an all-bond dual. A two-bond partition is `delta({u,v})` and its complement.

This calculation is a positive result for this family only. It does not prove `c<=Fmax` for all cographic matroids, or any uniform theorem for all regular matroids.

---

## 6. Verification and files

Run

```
PYTHONHASHSEED=0 python3 Submission/ResearchHereditaryFractionalCheck.py
```

The checker uses Python's `Fraction`, exact binary row reduction, and complete cycle-space enumeration. It does not require SciPy, SymPy, NetworkX, or an LP/MILP solver.

Its independent checks include:

* constructing an actual original column representation from each dual/cycle-code presentation and checking its rank and zero total xor;
* enumerating **all** binary cycle words and finding circuits by support minimality, without assuming the stated circuit classification;
* exact dynamic programs for both the **minimum and maximum** number of pieces in a partition of every enumerated cycle word; the first used element specifies the recursion, so every partition is covered;
* exact fractional primal coverage and signed dual inequalities against every contained circuit, not only support circuits or old partition circuits;
* explicit common-circuit witnesses for every pair of elements in the constructed families, proving connectedness in the matroid sense;
* the whole-code identification of `M_5` with `R10` and explicit `F7/F7*` minors establishing the nonregularity claims;
* the common-probability and fixed-size sampling formulas checked against every retained subfamily of the small actual minimum partitions;
* all Eulerian restrictions of the nine cographic examples `3<=a,b<=5`.

The full checker passed. Main finite totals:

| Class | Parameters | Eulerian restrictions checked |
|---|---|---:|
| critical family | `n=5,6,7,8,9,10,12` | 6,112 |
| synchronized family | `(n,t)=(5,2),(6,2),(5,3)` | 10,752 |
| cographic complete bipartite | `3<=a,b<=5` | 1,568 |

For the critical family, the full fractional primal/dual is checked at every parameter; every proper nonzero restriction is independently verified to be a single circuit. At `n<=8` separate primal/dual objects for every restriction are also checked. **Every restriction** in the synchronized and cographic rows has an explicit exact primal/dual check.

Formula-only large-parameter checks, not enumeration of huge matroids, give:

| `t` | `n=t^2+5` | `q / (best exchangeable expected cf)` |
|---:|---:|---:|
| 10 | 105 | about 3.25864 |
| 100 | 10005 | about 3.92042 |
| 1000 | 1000005 | about 3.99200 |

The limit 4 is proved by (4.3), not inferred from this table. Likewise the asymptotic ratio 2 in (2.3) is an exact formula, not a numerical conjecture.

The specification hash before and after the work is

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

A separate pre-work SHA-256 manifest comparison checks that all 37 pre-existing files in `Submission/` and `newSubmission/` remain unchanged. Only this report and `ResearchHereditaryFractionalCheck.py` are new deliverables.

---

## 7. Precise remaining gap

The original abstract question survives all the constructions here:

```
Does there exist K<infinity such that
c(M) <= K max_{F in Z(M)} cf(M|F)
for every finite Eulerian binary matroid?
```

A positive answer with `K=2` would therefore be **best possible for binary matroids**, but has not been established. A genuine negative answer must produce unbounded `c/Fmax`, with an upper bound on the fractional cost of **every** Eulerian restriction; neither a low `cf(E)` nor a low value on sampled old subunions is enough.

The newly proved sampling obstruction rules out a particularly natural `K=2` proof, not the inequality. Even for the globally optimal family in Section 3, the information identifying which circuit to omit is essential if one wants more than the exchangeable quarter-of-optimum guarantee. Whether a different use of integer optimality or critical restrictions always locates a sufficiently valuable Eulerian restriction remains the missing theorem.

For regular and graphic matroids the general hereditary bound is also unresolved here. The nonregularity certificates prevent the asymptotic binary lower-bound and sampling constructions from being misapplied to those classes. The audited graphic `cf<=rank` theorem and the previously known failures of full-ground-set constant-factor rounding are unchanged.
