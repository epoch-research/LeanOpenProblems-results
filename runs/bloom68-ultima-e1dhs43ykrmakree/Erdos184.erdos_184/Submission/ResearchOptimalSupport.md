# Exact optimal fractional cycle supports can leave a quadratic packing residual

## Status and answer

**The assertion for every optimum is false, even for a basic optimum, even with all positive-support cycles Hamilton, and even on complete graphs.** The earlier `+1/2` near-optimality qualification is removed here.

There is an unconditional infinite family with the following stronger properties.

* A simple `(p+1)`-regular graph `G_p` on `n=3p` vertices has an **exactly optimal basic fractional cycle partition whose support is pairwise edge-intersecting**. Its value is `(p+1)/2`. Every nonempty support packing has size **one**, and leaves exactly

  ```
  3p(p-1)/2 = n(n-3)/6
  ```

  edges. The residual is `(p-1)`-regular.
* The construction extends, by adding an edge-disjoint Hamilton decomposition of the complement, to an **exactly optimal basic point on `K_(3p)`**. Every maximum, and indeed every maximal, packing from this support has exactly `p` cycles and leaves the same quadratic number of edges.
* On that **same complete graph**, a different optimum is an integral Walecki Hamilton decomposition and leaves **zero** edges. In particular,

  ```
  c(K_(3p)) = c_f(K_(3p)) = (3p-1)/2,
  ```

  not the packing number of the bad support.

The construction works for every prime `p>=11` for which there are primitive elements

```
beta,                 gamma = beta/(beta-1)                 in F_p.
```

Section 8 proves that such a pair exists for **every sufficiently large prime**. This is an elementary character-sum argument, not an assumption that `2` is primitive for infinitely many primes. All arithmetic in the construction is explicit once a pair is chosen; one can choose the least suitable `beta` by a finite search.

**The global assertion that one can always choose a good optimum is not proved or refuted here.** It is a genuinely different quantifier statement. For the complete graphs constructed here it is true with zero residual. Section 9 gives a precise optimal-face reformulation and explains the remaining scope.

The proposed `K_p -> K_(p+2)` two-vertex extension is not asserted. Instead, the three-copy path construction below resolves the more general exact-optimal-support obstruction, with pairwise intersection and basicness as additional conclusions. No claim about novelty over the literature is needed.

Only this new research file has been added. `Spec.lean` and the old research files have not been edited. These are ordinary mathematical proofs and exact finite checks, not a Lean formalization.

---

## 1. Definitions and the quantifiers

Graphs are finite, simple, and undirected. Cycles and paths are simple. For an even graph, write

```
c(G)   = minimum number of cycles in an edge partition;
c_f(G) = min sum_C x_C,
         subject to sum_(C containing e) x_C = 1 for each edge e,
                    x_C >= 0.
```

A **support packing of x** is a set of pairwise edge-disjoint cycles from

```
supp(x) = { C : x_C > 0 }.
```

Its residual is the graph with edge set `E(G) \ union_(C in P) E(C)`. Support packing does not allow new cycles outside `supp(x)`, and does not mean the graph's own minimum cycle partition.

Here are the statements to distinguish. In each, `K` is a universal constant independent of the graph and of its order.

* **Every-optimum statement:** for every even simple `G` and every optimal `x`, some support packing leaves at most `K |V(G)|` edges.
* **Good-optimum existence statement:** for every even simple `G`, there exist an optimal `x` and a support packing leaving at most `K |V(G)|` edges.

The first is false by the examples below: their least possible residual divided by `n` is `(p-1)/2`, which tends to infinity. Restricting the first statement to **basic** optima does not repair it. The second statement does not follow from, and is not contradicted by, this counterexample.

We will use the following elementary global optimality certificate. On an `n`-vertex graph, set `y_e=1/n`. For **every** simple cycle `C`,

```
y(C) = |C|/n <= 1.
```

Thus `c_f(G) >= |E(G)|/n`. An exact fractional partition consisting of Hamilton cycles attains this bound. In particular, on a `d`-regular graph such a partition is optimal with value `d/2`. This certificate checks all cycles, not merely the displayed support.

---

## 2. Turn the prime-field cycles into two balanced path families

Fix a prime `p>=11` and a primitive pair `beta, gamma=beta/(beta-1)`. Put

```
r = beta-1,             gamma-1 = 1/r.
```

All subscripts denoting field elements are interpreted in `F_p`.

### 2.1 The original orthogonal cycle double cover

For a primitive `rho` and a centre `c`, let

```
C_c^rho = (c+1, c+rho, ..., c+rho^(p-2)).                  (2.1)
```

It is a `(p-1)`-cycle missing only `c`. An unordered edge `{u,v}` belongs to this cycle exactly when one of

```
v-c = rho(u-c),             u-c = rho(v-c)
```

holds. Since `rho != 1,-1`, these give exactly two distinct centres for each edge. Conversely, the unique common edge of cycles with distinct centres `c,d` is

```
{ (d+rho*c)/(1+rho), (c+rho*d)/(1+rho) }.                  (2.2)
```

The two endpoints are distinct, and substituting them verifies membership in both cycles. The two centre equations also prove uniqueness. Consequently:

* every edge of `K_p` is in exactly two `C_c^rho`;
* every two different cycles in this family share exactly one edge.

This re-proves the required part of the old near-optimal construction rather than assuming an unverified intersection property.

### 2.2 Insert the missing vertex at a path endpoint

For `a!=0`, delete the edge `{c+a,c+rho*a}` of `C_c^rho` and add `{c,c+a}`. This produces the Hamilton path

```
P_c^(rho,a) = (c, c+a, c+rho^(-1)*a, ..., c+rho^(-(p-2))*a).
                                                               (2.3)
```

It begins at `c` and ends at `c+rho*a`. The powers after `c` enumerate all nonzero offsets exactly once, so the path is simple and spanning. The only deleted cycle edge is the edge between offsets `a` and `rho*a`.

For `d!=0`, write

```
L(d) = { {v,v+d} : v in F_p }.
```

Thus `L(d)=L(-d)`. Because `p` is odd, the `p` translates of a fixed edge of difference `d` enumerate `L(d)` exactly once. Summing incidence vectors over all centres in (2.3) gives the exact identity

```
sum_c 1_(P_c^(rho,a))
    = 2*1_(E(K_p)) - 1_(L((rho-1)*a)) + 1_(L(a)).        (2.4)
```

There is no asymptotic or approximate coverage in this equation.

Apply (2.4) to the two families

```
A_c^a = P_c^(beta,a),             B_c^a = P_c^(gamma,r*a).
```

Both paths have the same endpoints

```
c, c+beta*a.
```

Their edge-load discrepancies cancel, because `(gamma-1)*r*a=a`:

```
sum_c [1_(A_c^a) + 1_(B_c^a)] = 4*1_(E(K_p)).            (2.5)
```

If `beta=2`, then `gamma=2`, `r=1`, and the two families coincide. In that case a single family already double-covers `K_p` by Hamilton paths. We retain both labelled families in (2.5), and coalesce identical cycles when defining an LP support.

### 2.3 The very few lost within-family intersections

The edge deleted from `C_c^rho` in (2.3) is shared with exactly

```
C_(c+(rho+1)*a)^rho.
```

This follows either from (2.2) or by solving the second centre equation for the edge `{c+a,c+rho*a}`. Therefore, if two paths of the same family with centres `c!=d` are edge-disjoint, necessarily

```
d-c in { +(rho+1)*a, -(rho+1)*a }.                        (2.6)
```

Indeed, otherwise their unique old common edge was deleted by neither path. Added edges cannot invalidate an intersection that survives.

---

## 3. Cross-family intersections: at most one exceptional displacement

This small algebraic lemma lets a dilation in one layer restore **all** support intersections, not just bound the packing number by a constant.

### Lemma 3.1

Suppose `beta!=2`. There is a set `T_beta` of at most one **nonzero** field element such that, for `c!=d`,

```
A_c^1 and B_d^1 edge-disjoint  =>  d-c in T_beta.          (3.1)
```

Consequently, for any `a!=0`,

```
A_c^a and B_d^a edge-disjoint  =>  (d-c)/a in T_beta.      (3.2)
```

#### Proof

Translate so that `c=0` and put `z=d-c!=0`. Define

```
L = beta*(2-beta),             k = beta^2-beta+1.
```

Both are nonzero. For `L` this uses `beta!=0,2`. If `k=0`, then `beta^3=-1` and `beta` has order six: `beta!=-1` and the characteristic is not three. Primitivity would force `p=7`, contrary to `p>=11`.

The old cycles `C_0^beta` and `C_z^gamma` have exactly two common edges, one for each relative orientation. Write an edge of `C_0^beta` in its unique orientation as `{u,beta*u}`. The two possibilities are

```
parallel:      u = -z / [beta*(beta-2)],
antiparallel:  u =  z / k.                              (3.3)
```

For example, the parallel equation is

```
beta*u = gamma*u + (1-gamma)*z,
```

and the antiparallel equation reverses the gamma orientation. All denominators are nonzero. The two edges are distinct: otherwise the same edge would have both gamma orientations, forcing `gamma^2=1`, impossible for a primitive element at `p>=11`.

The A-path deletes `{1,beta}`, and the B-path deletes `{z+r,z+beta}`. Substitution in (3.3) gives this table:

| Old common edge | Deleted by the A-path precisely at | Deleted by the B-path precisely at |
|---|---:|---:|
| parallel | `z=L` | `z=L/r` |
| antiparallel | `z=k` | `z=-k/r` |

If the new paths are disjoint, both old common edges must have been removed. Each path deletes only one edge, so the two deletions must concern different common edges. Thus one of the following holds:

```
z=L=-k/r,       so F(beta):=L*r+k=0;
z=k= L/r,       so Q(beta):=k*r-L=0.                    (3.4)
```

In expanded form,

```
F(beta) = -beta^3+4beta^2-3beta+1,
Q(beta) =  beta^3-beta^2-1,
F(beta)+Q(beta) = 3beta(beta-1) != 0.                    (3.5)
```

Therefore at most one of the two cases in (3.4) is possible. Define

```
T_beta = ({L} if F(beta)=0 else empty)
         union ({k} if Q(beta)=0 else empty).
```

It has size at most one and excludes zero. New edges might restore some additional intersections; only the necessary condition is asserted. This proves (3.1).

Finally, the vertex map `v -> v/a` takes `A_c^a,B_d^a` to `A_(c/a)^1,B_(d/a)^1`, proving (3.2). ∎

---

## 4. A dense even graph with pairwise-intersecting optimal Hamilton support

### 4.1 The graph and its cycles

Use three vertex layers

```
V = Z_3 x F_p,                    n=3p.
```

Each layer induces `K_p`. Choose the three scales and endpoint increments

```
a_0=1,       a_1=1/2,       a_2=1;
t_i=beta*a_i.
```

Between layer `i` and layer `i+1` (indices modulo three), put the perfect matching

```
M_i = { {(i,v),(i+1,v-t_i)} : v in F_p }.                (4.1)
```

There is only one such matching on each of the three unordered pairs of layers. Thus the graph is simple. Every vertex has `p-1` internal neighbours and two neighbours in other layers, so

```
G_p is (p+1)-regular,         |E(G_p)|=3p(p+1)/2.         (4.2)
```

Let `D = M_0 union M_1 union M_2`. Following its layer-cyclic orientation for three steps changes the field coordinate by

```
-(t_0+t_1+t_2) = -5beta/2 != 0.                          (4.3)
```

Since `p` is prime and `p>=11`, this translation has order `p`. Hence `D` is one Hamilton cycle on all `3p` vertices, not a disconnected 2-factor.

For each centre `c`, form two more Hamilton cycles:

* `H_A,c` follows `A_c^(a_i)` in layer `i`, from `c` to `c+t_i`;
* `H_B,c` follows `B_c^(a_i)` in layer `i`, from `c` to `c+t_i`.

In either case join the endpoint `(i,c+t_i)` to `(i+1,c)` using `M_i`. Three spanning paths in disjoint layers, joined cyclically by three matching edges, form a simple Hamilton cycle. The paths have `3(p-1)` edges altogether, and the joins add three, for total length `3p`.

Assign coefficients

```
x_(H_A,c)=1/4,       x_(H_B,c)=1/4,       x_D=1/2.        (4.4)
```

When two displayed cycles coincide, their coefficients are added. In particular, for `beta=2` there are just `p+1` distinct support cycles, all with coefficient `1/2`.

### 4.2 Exact feasibility and exact optimality

In every layer, identity (2.5) says that its internal edges occur exactly four times among the two labelled Hamilton families. Their load under (4.4) is exactly one.

For each matching edge of `M_i`, there is a unique centre `c` such that the edge is `{(i,c+t_i),(i+1,c)}`. It occurs in `H_A,c`, `H_B,c`, and `D`, and nowhere else among the displayed cycles. Its load is

```
1/4 + 1/4 + 1/2 = 1.
```

Thus (4.4) is an **exact** fractional partition. Its objective is

```
2p*(1/4)+1/2 = (p+1)/2 = |E(G_p)|/(3p).                 (4.5)
```

The uniform dual from Section 1 certifies global optimality. Every positive-support cycle is Hamilton; there is no near-optimality error to absorb.

### 4.3 Every two support cycles intersect

First consider distinct centres in the same family, with parameters `(rho,a)=(beta,1)` or `(gamma,r)` at scale one. If their global Hamilton cycles were disjoint, then their paths in both layers 0 and 1 would be disjoint. By (2.6), with `s=(rho+1)*a!=0`, this would require

```
d-c in {s,-s} intersection {s/2,-s/2}.
```

That intersection is empty: equality of an element of each set would force `2=1` or `2=-1` in `F_p`. So every two distinct support cycles within a family intersect.

If `beta=2`, the two families coincide and this already handles them. Otherwise consider `H_A,c` and `H_B,d`.

* If `c=d`, they share all three matching edges used to join their layer paths.
* If `c!=d`, put `delta=d-c`. Disjointness in layers 0 and 1 would imply, by Lemma 3.1,

  ```
  delta in T_beta,                 2delta in T_beta.
  ```

  A set of at most one nonzero element cannot satisfy this for `delta!=0`.

Finally, `D` meets every `H_A,c` and `H_B,c` in their three matching edges. Therefore the entire support is **pairwise edge-intersecting**.

Every nonempty support packing has size one. Deleting any one support cycle removes two incident edges at every vertex, leaving a `(p-1)`-regular even graph and exactly

```
R_p = 3p(p-1)/2 = n(n-3)/6                              (4.6)
```

edges. This is the minimum possible residual over all support packings, and it is attained by every maximal packing.

---

## 5. The displayed optimum is itself basic

This is stronger than merely passing to a vertex with smaller support.

For a finite polyhedron `{x>=0 : A x=1}`, a feasible point is a vertex/basic feasible solution if its positive-support columns are linearly independent. Indeed, any convex decomposition of that point into feasible points has zero coordinates outside its support; independence then forces the two points to coincide.

### 5.1 The case `beta!=2`

Suppose a real linear dependence among the displayed incidence columns has coefficients

```
u_c on H_A,c,       v_c on H_B,c,       w on D.
```

A row for the matching edge with centre `c` gives

```
u_c+v_c+w=0.                                           (5.1)
```

Sum the dependence over all internal edges of layer 0. Each path contributes `p-1` edges and `D` contributes zero. Using (5.1) gives

```
0 = (p-1)*sum_c(u_c+v_c) = -p(p-1)w.
```

Thus `w=0` and `v_c=-u_c`. Restrict the remaining dependence to the `p` layer-0 edges

```
e_i = {i,i+1},                  i in F_p.
```

The resulting integer matrix is

```
M_(i,c) = 1_(e_i in A_c^1) - 1_(e_i in B_c^1).           (5.2)
```

It is circulant by translation of centres and vertices. Since `r!=1,-1`, equation (2.4) gives load three for the A-family and load one for the B-family on every edge of `L(1)`. Consequently **every row sum of M is two**.

An integer circulant matrix of prime size `p` whose row sum is nonzero modulo `p` is nonsingular over the reals. Here is a short proof. Over `F_p`, write it as `f(S)`, where `S` is the cyclic shift matrix and `f(1)` is the row sum. Then

```
(S-I)^p = S^p-I = 0,
f(S) = f(1)I + (S-I)g(S).
```

The second summand is nilpotent. If `f(1)!=0`, a finite geometric series gives an inverse. Hence the integer determinant is nonzero modulo `p`, and in particular is not zero as an integer.

Apply this with row sum `2`. Equation `M u=0` implies `u=0`, and hence `v=w=0`. All `2p+1` displayed columns are independent. This argument also excludes any unnoticed duplication among these columns.

### 5.2 The case `beta=2`

After coalescing the two identical families, the support is `H_c` and `D`. A dependence gives `u_c+w=0` on matching rows. Summing internal rows again gives `-p(p-1)w=0`. Thus every coefficient vanishes, and the `p+1` columns are independent.

Therefore (4.4), with duplicates coalesced, is an **exactly optimal basic point of the full all-simple-cycle LP**, not just of a restricted Hamilton-cycle LP.

---

## 6. Extend the bad basic optimum to a complete graph

Keep the same `3p` vertices and the three internal cliques. The complete tripartite graph between the layers has an explicit Hamilton decomposition extending `D`.

For every `j in F_p`, put matchings from layer `i` to `i+1` with coordinate shifts

```
s_0(j)= j-t_0,
s_1(j)= j-t_1,
s_2(j)=-2j-t_2.                                        (6.1)
```

Call their union `J_j`. Its three-step shift is always

```
s_0(j)+s_1(j)+s_2(j) = -5beta/2 != 0,
```

so each `J_j` is Hamilton, by the same orbit calculation as for `D`. For each fixed layer link, its shifts as `j` varies run through all of `F_p`: the coefficients are `1,1,-2`, all invertible. Thus the `p` cycles `J_j` partition **all** edges between the layers. Also `J_0=D`.

In particular,

```
E(K_(3p)) = E(G_p) disjoint_union (union_(j!=0) E(J_j)).  (6.2)
```

Extend (4.4) by setting `x_(J_j)=1` for each `j!=0`. This is an exact fractional Hamilton partition of `K_(3p)`, with objective

```
(p+1)/2 + (p-1) = (3p-1)/2.
```

It is optimal by the uniform dual. It is also basic: in a dependence among its support columns, any edge of `J_j`, `j!=0`, occurs in only that newly added column, since the new columns are mutually edge-disjoint and disjoint from `G_p`. Their coefficients vanish. Section 5 handles the remaining columns.

A support packing can use at most one cycle from the old `G_p` support and at most `p-1` new cycles. These choices are independent because of (6.2), so its maximum size is exactly

```
nu(supp(x)) = 1+(p-1) = p.                              (6.3)
```

Every maximal packing must contain every new `J_j` and exactly one old support cycle. Hence every maximal packing has `p` cycles and leaves exactly `R_p` edges from (4.6). In particular, choosing maximum covered edge count instead of maximum cardinality does not help: all support cycles are Hamilton and have the same length.

The support has `3p=n` distinct columns when `beta!=2`, and `2p` when `beta=2`. Thus small support size, basicness, simple rational coefficients, an all-Hamilton support, and a positive uniform dual do not make this residual shortcut valid.

---

## 7. Good optima and the graph's own cycle partition number

### 7.1 An explicit good optimum of the same complete graph

For completeness, here is the Walecki construction with its edge-partition proof. For `N=2h+1`, use vertices `infinity` and `Z_(2h)`. For each `j=0,...,h-1`, take

```
W_j = (infinity,
       j, j-1, j+1, j-2, j+2, ..., j-(h-1), j+(h-1), j-h).
                                                               (7.1)
```

All finite coordinates are modulo `2h`. The offsets list each finite vertex exactly once, so this is Hamilton. Its two infinity edges meet vertices `j` and `j-h`; over all `j` these partition the infinity edges.

Its finite edges are precisely

```
{j+k,j-k-1},       k=0,...,h-1,       with endpoint sum 2j-1;
{j-k,j+k},         k=1,...,h-1,       with endpoint sum 2j.
```

The first list consists of all `h` pairs of sum `2j-1` (there are no loops for an odd sum). The second consists of all `h-1` nonloop pairs of sum `2j` (the two loop solutions are at `j` and `j+h`). As `j` varies, `2j-1` and `2j` run through all odd and even residues respectively. Every finite edge therefore appears exactly once. This proves that the `W_j` partition `K_N`.

For `N=3p`, this is an integral optimal fractional point with `(3p-1)/2` support cycles, all mutually edge-disjoint. Its whole support is a packing with empty residual. Therefore

```
c(K_(3p)) = c_f(K_(3p)) = (3p-1)/2,
```

whereas the bad optimum from Section 6 has maximum support packing only `p`. These are two different optima of the **same** graph.

### 7.2 What is, and is not, claimed about `c(G_p)`

The pairwise-intersecting support in Section 4 is not a claim that every Hamilton cycle of `G_p` lies in that support. Nor does it compute `c(G_p)`.

In fact there is already a simple linear-size ordinary cycle partition: take a Walecki partition of each internal `K_p` and the cross-layer Hamilton cycle `D`. Its count is

```
3(p-1)/2+1 = (3p-1)/2 = (n-1)/2.
```

Together with the fractional lower bound, this gives

```
(p+1)/2 = c_f(G_p) <= c(G_p) <= (3p-1)/2.                (7.2)
```

No equality for `c(G_p)` beyond these bounds is asserted. In particular, the quadratic residual does not imply a superlinear minimum cycle partition, and is not an Erdős–Gallai counterexample.

---

## 8. Unconditional availability of the primitive pair

This section supplies the infinitude proof. Finite successful primes alone would not suffice, and using only `beta=2` would leave an unproved Artin-type infinitude assumption.

### Lemma 8.1

For every sufficiently large prime `p`, there exists `b` such that both `b` and `b/(b-1)` generate `F_p^*`.

#### Primitive-element indicator

Put `m=p-1`, `theta=phi(m)/m`, and let `omega(m)` count distinct prime divisors. Extend every multiplicative character, including the trivial character, by value zero at zero. For `x!=0`, the indicator of being primitive is

```
I(x) = theta * sum_(d|m) [mu(d)/phi(d)]
                    * sum_(ord chi=d) chi(x).            (8.1)
```

To verify this identity, write `x=g^k` for a generator `g`. For a prime `ell|m`, the sum of all characters of exact order `ell` at `g^k` is `ell-1` if `ell|k`, and `-1` otherwise. Expanding the product over `ell|m` of

```
1 - [1/(ell-1)] * sum_(ord chi=ell) chi(x)
```

gives the sum in (8.1). It vanishes if some `ell|k`, and otherwise equals `1/theta`. Thus (8.1) is exact.

#### A character-sum bound

For characters `chi,psi`, consider

```
S(chi,psi) = sum_(x!=0,1) chi(x) psi(x/(x-1)).
```

For both characters trivial this is `p-2`. Otherwise,

```
|S(chi,psi)| <= sqrt(p).                                 (8.2)
```

Here are details to avoid relying on an unproved specialized primitive-root theorem. With

```
J(A,B) = sum_x A(x)B(1-x),
```

one has

```
S(chi,psi) = psi^(-1)(-1) J(chi*psi,psi^(-1)).
```

If exactly one of `A,B` is trivial, or both are nontrivial with `AB` trivial, the Jacobi sum has absolute value one. The first case follows by subtracting the missing value at 0 or 1 from a nontrivial character sum. The second follows by the substitution `x/(1-x)`, giving `J(A,A^(-1))=-A(-1)`.

If `A,B,AB` are all nontrivial, define the Gauss sum

```
G(A) = sum_x A(x) exp(2*pi*i*x/p).
```

Character orthogonality gives `|G(A)|^2=p`: in the squared absolute value, substitute `x=t*y`; the inner sum over `y!=0` is `p-1` at `t=1` and `-1` otherwise. Grouping terms by `x+y` also gives

```
G(A)G(B)=J(A,B)G(AB).
```

The zero-sum terms vanish because `AB` is nontrivial. Hence `|J(A,B)|=sqrt(p)`. This proves (8.2) in every non-main case.

#### Count the simultaneous primitive elements

The required number is

```
N_p = sum_(x!=0,1) I(x) I(x/(x-1)).
```

Substitute (8.1). For a fixed order `d`, there are `phi(d)` characters, so the total absolute coefficient mass of the character sum in (8.1), before multiplying by `theta`, is

```
sum_(d|m) |mu(d)| = 2^omega(m).
```

Using the main term and (8.2) therefore gives the rigorous lower bound

```
N_p >= theta^2 * [ p-2 - (4^omega(p-1)-1)*sqrt(p) ].       (8.3)
```

For every fixed `epsilon>0`,

```
4^omega(m) <= C_epsilon * m^epsilon.                     (8.4)
```

Indeed, prime factors `q>4^(1/epsilon)` individually satisfy `4<=q^epsilon`; the finitely many smaller primes contribute a fixed constant. Taking `epsilon=1/4`, the bracket in (8.3) is `p-O(p^(3/4))`, which is positive for all sufficiently large `p`. Since `theta>0`, this proves `N_p>0`.

There are arbitrarily large primes, so Sections 2–7 yield an unconditional infinite family. ∎

The finite tests find pairs at every prime tested, but neither the construction nor its infinitude proof requires a claim about every small prime.

---

## 9. What remains for a carefully chosen optimum

The counterexample refutes the universal assertion about a supplied optimum. It also refutes variants assuming the supplied optimum is basic, has only `O(n)` positive variables, has small rational coefficients, has entirely Hamilton support, or admits the uniform positive dual certificate.

It does **not** refute the good-optimum existence statement. In particular:

1. Whenever `c(G)=c_f(G)`, a minimum integral partition itself is a good optimum, with zero residual. This applies to every complete graph above.
2. The canonical support relevant to an existential claim is the union of supports over the whole optimal face, not the support of one arbitrary vertex of that face.

More precisely, define

```
T(G) = { C : x_C>0 for at least one optimal exact fractional partition x }.
```

There exists an optimal point `x_max` whose support is exactly `T(G)`. To see this, for each cycle in `T(G)` choose one optimum where it has positive coefficient, and average these finitely many optima. The edgeless case is trivial. Feasibility and optimality are preserved, and the union of their supports is exactly `T(G)`.

Consequently, for any prescribed residual bound `B`, the following are equivalent:

* some optimal support admits a packing with residual at most `B`;
* `T(G)` admits such a packing;
* the maximal-support optimum `x_max` admits such a packing.

This is an exact reformulation, **not** a proof of a linear bound. In particular, selecting a basic optimum and selecting a maximal-support optimum are quite different operations.

There is also a useful specialization. If a `d`-regular graph on `n` vertices has a fractional Hamilton decomposition, then `c_f=d/2`. Every cycle with positive coefficient in **any** optimum must be Hamilton: equality in

```
|E| = sum_C x_C |C| <= n sum_C x_C
```

forces this term by term. Thus a good-optimum residual bound `Kn` on this class would require a packing of at least

```
d/2-K
```

Hamilton cycles from `T(G)`. This is a substantial near-decomposition assertion, not a consequence of LP optimality alone. It is not settled here.

Finally, outside the Hamilton setting, a small residual does not by itself control the number of packed cycles relative to `c_f`; a rounding ledger may also have to pay for the packing count. None of the calculations above identify a support-packing number with `c(G)`.

---

## 10. Exact finite verification

The standalone standard-library Python checker below was run with `python3`. It verifies graph and cycle edge sets independently of any LP solver.

Checks include:

* the original cycle double cover, the unique common-edge formula, and the centre of every deleted edge;
* the Hamilton paths and their common endpoints, and exact fourfold internal coverage;
* the necessary within-family displacement condition and the cross-family exceptional-displacement formulas;
* Hamiltonicity of every global cycle, the graph's degree and edge count, and the exact rational primal objective;
* **all pairs** of distinct positive-support global cycles intersect, by recording which support columns own each edge and comparing the resulting pair set with all pairs;
* the circulant row-sum conditions used in the basicness proof for every tested nondegenerate parameter, and direct modular rank checks of both the circulant and the full `G_p` support incidence matrix for `p<=43`;
* an independent exact edge partition of the full tripartite complement by the `J_j`, and the resulting complete-graph fractional certificate;
* the ordinary three-clique-plus-`D` partition and independent Walecki good optima of the same complete graphs;
* all **960** primitive pairs at primes `11<=p<=257` for the local intersection algebra, including **34** cases with a nonempty predicted cross-exception set. Thus the exceptional cases in Lemma 3.1 were actually exercised, not silently omitted;
* a separate primitive-pair existence scan at all **1,227** primes from 5 through 9,973. This finite scan is not used in place of Section 8's infinitude proof.

Full graph certificates were checked for **32 parameter choices on 24 primes**, up to `p=257`, hence up to 771 vertices. Both `beta=2` and genuinely distinct path families were tested. In every case the checker found support packing number exactly one on `G_p`, exactly `p` on the extended complete graph, and the residual `3p(p-1)/2`.

The all-cycle dual inequalities require no cycle enumeration: the proof `|C|<=n` applies to every simple cycle, including those not listed by the checker.

### 10.1 Reproducible checker

Save the following code block to a temporary `.py` file and run it with `python3`. No third-party packages are required. The exact output is recorded immediately after it.

<!-- CHECKER_START -->

```python
#!/usr/bin/env python3
"""Exact finite checks for ResearchOptimalSupport.md; standard library only."""
from collections import Counter
from itertools import combinations
from fractions import Fraction


def edge(u, v):
    assert u != v
    return (u, v) if u < v else (v, u)


def path_edges(P):
    assert len(P) == len(set(P))
    return frozenset(edge(u, v) for u, v in zip(P, P[1:]))


def cycle_edges(C):
    assert len(C) >= 3 and len(C) == len(set(C))
    return path_edges(C) | {edge(C[-1], C[0])}


def primes_to(n):
    return [p for p in range(2, n + 1)
            if all(p % d for d in range(2, int(p**0.5) + 1))]


def prime_factors(n):
    out, d = [], 2
    while d*d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def primitive(a, p):
    return a % p != 0 and all(pow(a, (p-1)//q, p) != 1
                              for q in prime_factors(p-1))


def primitive_pairs(p):
    return [(b, b * pow(b-1, -1, p) % p) for b in range(2, p)
            if primitive(b, p)
            and primitive(b * pow(b-1, -1, p) % p, p)]


def paths(p, rho, a):
    inv = pow(rho, -1, p)
    return [tuple([c] + [(c + a*pow(inv, j, p)) % p
                         for j in range(p-1)]) for c in range(p)]


def old_cover_check(p, rho, a):
    owners = {}
    for c in range(p):
        C = tuple((c + pow(rho, j, p)) % p for j in range(p-1))
        assert set(C) == set(range(p)) - {c}
        for e in cycle_edges(C):
            owners.setdefault(e, []).append(c)
    E = set(combinations(range(p), 2))
    assert set(owners) == E
    assert all(len(cs) == 2 for cs in owners.values())
    pairs = Counter(tuple(sorted(cs)) for cs in owners.values())
    assert set(pairs) == E and set(pairs.values()) == {1}
    inv = pow(1 + rho, -1, p)
    for (u, v), (c, d) in owners.items():
        assert edge((d + rho*c)*inv % p, (c + rho*d)*inv % p) == (u, v)
    for c in range(p):
        e = edge((c+a) % p, (c+rho*a) % p)
        assert set(owners[e]) == {c, (c+(rho+1)*a) % p}


def walecki(n):
    assert n >= 3 and n % 2 == 1
    r = (n-1)//2
    out = []
    for j in range(r):
        C = [n-1, j]
        for k in range(1, r):
            C += [(j-k) % (n-1), (j+k) % (n-1)]
        C += [(j-r) % (n-1)]
        out.append(cycle_edges(C))
    cov = Counter(e for C in out for e in C)
    assert set(cov) == set(combinations(range(n), 2))
    assert set(cov.values()) == {1}
    return out


def modular_rank(A, q):
    A = [[x % q for x in row] for row in A]
    r, cols = 0, len(A[0])
    for c in range(cols):
        pivot = next((i for i in range(r, len(A)) if A[i][c]), None)
        if pivot is None:
            continue
        A[r], A[pivot] = A[pivot], A[r]
        z = pow(A[r][c], -1, q)
        A[r] = [(x*z) % q for x in A[r]]
        for i in range(r+1, len(A)):
            if A[i][c]:
                z = A[i][c]
                A[i] = [(x-z*y) % q for x, y in zip(A[i], A[r])]
        r += 1
        if r == cols:
            break
    return r


def check(p, b):
    assert primitive(b, p)
    g, a, t = b * pow(b-1, -1, p) % p, b-1, b
    assert primitive(g, p)
    PA, PB = paths(p, b, 1), paths(p, g, a)
    A, B = [path_edges(P) for P in PA], [path_edges(P) for P in PB]
    for P in PA + PB:
        c = P[0]
        assert len(P) == p and set(P) == set(range(p))
        assert P[-1] == (c+t) % p
    old_cover_check(p, b, 1)
    old_cover_check(p, g, a)
    cov = Counter(e for P in A+B for e in P)
    assert set(cov) == set(combinations(range(p), 2))
    assert set(cov.values()) == {4}

    assert p >= 11
    for F, rho, scale in [(A, b, 1), (B, g, a)]:
        step = (rho+1)*scale % p
        assert step != 0
        for c, d in combinations(range(p), 2):
            if F[c].isdisjoint(F[d]):
                assert (d-c) % p in {step, (-step) % p}
    if b != 2:
        k = (b*b-b+1) % p
        assert k != 0
        f = (-b**3+4*b*b-3*b+1) % p
        h = (b**3-b*b-1) % p
        assert (f+h) % p == 3*b*(b-1) % p != 0
        exceptional = set()
        if f == 0:
            exceptional.add(b*(2-b) % p)
        if h == 0:
            exceptional.add(k)
        assert len(exceptional) <= 1 and 0 not in exceptional
        for c in range(p):
            for d in range(p):
                if c != d and A[c].isdisjoint(B[d]):
                    assert (d-c) % p in exceptional

    n = 3*p
    vtx = lambda i, v: i*p + v
    internal = {edge(vtx(i, u), vtx(i, v))
                for i in range(3) for u, v in combinations(range(p), 2)}
    cross = {edge(vtx(i, u), vtx((i+1) % 3, v))
             for i in range(3) for u in range(p) for v in range(p)}
    scales = [1, pow(2, -1, p), 1]
    ends = [t*q % p for q in scales]
    D_expected = {edge(vtx(i, x), vtx((i+1) % 3, (x-ends[i]) % p))
                  for i in range(3) for x in range(p)}
    # Dilate the middle-layer path about its centre, not about zero.
    H = [[cycle_edges(tuple(vtx(i, (c + scales[i]*(v-c)) % p)
                           for i in range(3) for v in PF[c]))
          for c in range(p)] for PF in (PA, PB)]
    J = []
    for j in range(p):
        shifts = [(j-ends[0]) % p, (j-ends[1]) % p, (-2*j-ends[2]) % p]
        C, state = [], (0, 0)
        for _ in range(n):
            i, x = state
            C.append(vtx(i, x))
            state = ((i+1) % 3, (x+shifts[i]) % p)
        assert state == (0, 0)
        J.append(cycle_edges(tuple(C)))
    D = J[0]
    assert D == D_expected
    cov_cross = Counter(e for C in J for e in C)
    assert set(cov_cross) == cross and set(cov_cross.values()) == {1}
    G = internal | D
    degrees = Counter(v for e in G for v in e)
    assert len(G) == n*(p+1)//2 and set(degrees.values()) == {p+1}

    weights4 = Counter()
    for C in H[0] + H[1]:
        assert len(C) == n and C <= G
        assert len(C & D) == 3
        weights4[C] += 1
    weights4[D] += 2
    loads4 = Counter()
    for C, w in weights4.items():
        for e in C:
            loads4[e] += w
    assert set(loads4) == G and set(loads4.values()) == {4}
    assert Fraction(sum(weights4.values()), 4) == Fraction(p+1, 2)
    assert len(weights4) == (p+1 if b == 2 else 2*p+1)
    owners = {}
    for index, C in enumerate(weights4):
        for e in C:
            owners.setdefault(e, []).append(index)
    meeting_pairs = {tuple(sorted(pair)) for cs in owners.values()
                     for pair in combinations(cs, 2)}
    assert len(meeting_pairs) == len(weights4)*(len(weights4)-1)//2
    nu = 1
    assert len(G - D) == n*(p-1)//2

    if b != 2:
        # The exact integer circulant used in the basicness proof.
        M = [[int(edge(i, (i+1) % p) in A[c])
              - int(edge(i, (i+1) % p) in B[c])
              for c in range(p)] for i in range(p)]
        assert all(sum(row) == 2 for row in M)
        assert all(M[i][c] == M[(i-c) % p][0]
                   for i in range(p) for c in range(p))
        if p <= 43:
            assert modular_rank(M, p) == p
    if p <= 43:
        cols = list(weights4)
        incidence = [[int(e in C) for C in cols] for e in sorted(G)]
        assert modular_rank(incidence, 1000003) == len(cols)

    # Explicit ordinary partition: three Walecki decompositions plus D.
    local = walecki(p)
    integral = [frozenset(edge(vtx(i, u), vtx(i, v)) for u, v in C)
                for i in range(3) for C in local] + [D]
    cov_int = Counter(e for C in integral for e in C)
    assert set(cov_int) == G and set(cov_int.values()) == {1}
    assert len(integral) == (3*p-1)//2

    # The same bad basic optimum extends to a COMPLETE graph.
    for C in J[1:]:
        assert C.isdisjoint(G)
        weights4[C] += 4
        for e in C:
            loads4[e] += 4
    complete = set(combinations(range(n), 2))
    assert set(loads4) == complete and set(loads4.values()) == {4}
    assert Fraction(sum(weights4.values()), 4) == Fraction(n-1, 2)
    assert len(weights4) == ((p+1 if b == 2 else 2*p+1) + p-1)
    good = walecki(n)
    assert len(good) == (n-1)//2
    residual = n*(p+1-2*nu)//2
    assert residual == n*(p-1)//2
    return (p, b, g, len(H[0])+len(H[1])+1 if b != 2 else p+1,
            nu, p-1+nu, residual)



def audit_all_primitive_pairs():
    count, exceptions = 0, 0
    for p in primes_to(257):
        if p < 11:
            continue
        for b, g in primitive_pairs(p):
            A, B = paths(p, b, 1), paths(p, g, b-1)
            A0 = path_edges(A[0])
            DA = {z for z in range(1, p)
                  if A0.isdisjoint(path_edges(A[z]))}
            assert DA <= {(b+1) % p, (-b-1) % p}
            assert not (DA & {z*pow(2, -1, p) % p for z in DA})
            if b != 2:
                F = (-b**3+4*b*b-3*b+1) % p
                Q = (b**3-b*b-1) % p
                assert (F+Q) % p == (3*b*(b-1)) % p != 0
                T = set()
                if F == 0:
                    T.add(b*(2-b) % p)
                if Q == 0:
                    T.add((b*b-b+1) % p)
                actual = {z for z in range(1, p)
                          if A0.isdisjoint(path_edges(B[z]))}
                assert actual <= T and len(T) <= 1
                assert not (actual & {z*pow(2, -1, p) % p for z in actual})
                exceptions += bool(T)
            count += 1
    print('All-pair local algebra audit PASS:', count,
          'primitive pairs on primes 11..257;', exceptions,
          'nonempty predicted cross-exception sets.')


def main():
    primes = [p for p in primes_to(101) if p >= 11] + [127, 257]
    parameters = []
    for p in primes:
        pairs = primitive_pairs(p)
        assert pairs
        parameters.append((p, pairs[0][0]))
        # Exercise the genuinely two-orbit construction when beta=2 also works.
        alt = next((b for b, g in pairs if b != 2), None)
        if pairs[0][0] == 2 and alt is not None:
            parameters.append((p, alt))
    rows = [check(p, b) for p, b in parameters]
    print('p beta gamma support_G nu_G nu_K residual_edges')
    for row in rows:
        print(*row)
    print('PASS:', len(rows), 'parameter pairs on', len(primes),
          'primes; exact coverage, Hamiltonicity, maximum support packing,',
          'basicness checks, complete-graph extension, and good Walecki optima.')
    # A separate, larger finite existence scan; not the infinitude proof.
    scan = [p for p in primes_to(10000) if p >= 5]
    for p in scan:
        assert any(primitive(b, p)
                   and primitive(b*pow(b-1, -1, p) % p, p)
                   for b in range(2, p))
    print('Primitive-pair scan PASS:', len(scan), 'primes from 5 through', scan[-1])
    audit_all_primitive_pairs()


if __name__ == '__main__':
    main()
```

<!-- CHECKER_END -->

### 10.2 Recorded output

```text
p beta gamma support_G nu_G nu_K residual_edges
11 2 2 12 1 11 165
13 2 2 14 1 13 234
17 3 10 35 1 17 408
19 2 2 20 1 19 513
23 5 7 47 1 23 759
29 2 2 30 1 29 1218
29 8 26 59 1 29 1218
31 3 17 63 1 31 1395
37 2 2 38 1 37 1998
37 13 35 75 1 37 1998
41 6 34 83 1 41 2460
43 5 12 87 1 43 2709
47 5 13 95 1 47 3243
53 2 2 54 1 53 4134
53 5 41 107 1 53 4134
59 2 2 60 1 59 5133
59 6 13 119 1 59 5133
61 2 2 62 1 61 5490
61 10 35 123 1 61 5490
67 2 2 68 1 67 6633
67 7 57 135 1 67 6633
71 7 13 143 1 71 7455
73 13 68 147 1 73 7884
79 39 53 159 1 79 9243
83 2 2 84 1 83 10209
83 5 22 167 1 83 10209
89 3 46 179 1 89 11748
97 5 74 195 1 97 13968
101 2 2 102 1 101 15150
101 7 18 203 1 101 15150
127 3 65 255 1 127 24003
257 3 130 515 1 257 98688
PASS: 32 parameter pairs on 24 primes; exact coverage, Hamiltonicity, maximum support packing, basicness checks, complete-graph extension, and good Walecki optima.
Primitive-pair scan PASS: 1227 primes from 5 through 9973
All-pair local algebra audit PASS: 960 primitive pairs on primes 11..257; 34 nonempty predicted cross-exception sets.
```

## 11. Protected-file checks

The pre-existing files were left untouched. In particular, the final hashes agree with those recorded before this work:

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde  Submission/Spec.lean
8e820baa6ee2f11a57cc70a8a49277d9e0f3962fb1d597f875805f77232fc802  Submission/ResearchRounding.md
```

A SHA-256 manifest comparison also passed for every pre-existing file in `Submission/`. The checker is embedded above rather than installed over an old checker. No `Spec` or old-file edits were needed.
