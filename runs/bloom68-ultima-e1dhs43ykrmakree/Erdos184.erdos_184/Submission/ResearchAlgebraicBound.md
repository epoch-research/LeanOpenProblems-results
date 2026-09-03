# The actual cycle-partition polynomial: a characteristic-zero determinant obstruction

## Status

**The requested universal bound is NOT proved.** This investigation does not establish any absolute constant `C` such that every finite even simple graph has an edge partition into at most `C|V(G)|` vertex-simple cycles. It also gives no counterexample to that assertion.

The outcome is a precise obstruction to the suggested algebraic route, not another finite-checker proposal:

1. There is an exact determinant identity whose atoms really are simple cycles. However, each actual partition is weighted by the **chromatic polynomial of its cycle-intersection graph**, not by a power recording its number of cycles.
2. For the suggested inverse determinant, cancellation can be controlled completely over the integers: all resulting coefficients are nonnegative. Nevertheless its order at zero is **always the number of edge-containing components**, not the minimum simple-cycle count. Thus passing from parity to characteristic zero does not repair this particular certificate.
3. No graph-independent scalar **linear** correction of these determinant coefficients can recover the actual polynomial, even if the correction may depend on `n` and `m`. A three-graph identity with fixed `n,m` proves this.
4. An exact nilpotent/logarithmic formula for the genuine polynomial is available. Its necessary vertex-reset operation is not an algebra homomorphism. Applying a global `n`-vertex exterior/nilpotent cutoff before this reset kills every partition of a graph with a vertex of degree at least four.
5. The natural multivariate polynomial with one variable per actual simple cycle is real stable **if and only if the graph has a unique cycle partition**. This is a general obstruction to applying stable-polynomial support theory directly to the exact partition family, not just a small example.

These are paper-level identities and obstruction proofs, with no literature-priority claim or Lean formalization. They do **not** exclude every possible determinant, Pfaffian, representation-theoretic, or auxiliary stable-polynomial construction. They identify exactly what the constructions audited here fail to certify, and the investigation stops at that obstruction.

Only this file and `Submission/ResearchAlgebraicBoundCheck.py` were created. `Spec.lean` and all other existing files were preserved.

---

## 1. Definitions: the genuine objective

Let `G=(V,E)` be a finite simple undirected even graph, `n=|V|`, and `m=|E|`. A cycle is an unoriented vertex-simple cycle of length at least three, identified by its edge set. A partition is an unordered family of such cycles covering each edge exactly once; cycles may share vertices.

Write

```
D(G) = set of actual simple-cycle edge partitions,
Z_G(t) = sum_{D in D(G)} t^{|D|},
c(G) = min_{D in D(G)} |D|.
```

For an edgeless graph the empty partition is the unique partition, so `Z_G=1` and `c(G)=0`. For an even graph, the ordinary repeated simple-cycle deletion argument proves `D(G)` is nonempty. Consequently

```
ord_{t=0} Z_G(t) = c(G).                                      (1.1)
```

Let `kappa_e(G)` count the connected components containing at least one edge. Isolated vertices do not contribute to this parameter.

For a partition `D`, let `I_D` be its **vertex-intersection graph**: its vertices are the cycles in `D`, and two are adjacent when they share an original graph vertex. This is not the bipartite edge-overlap graph used later in Section 6.

No use is made of fractional integrality, cycle-polytope TU, normal cost cones, or reduction modulo two. The fractional theorem in `ResearchFractional.md` and the integral obstructions in `ResearchIncidence.md` and `newSubmission/ResearchDegreeTrades.md` remain separate from (1.1).

---

## 2. Exact determinant identity with genuine simple-cycle atoms

Work over the commuting square-zero edge algebra

```
R_E = Q[x_e : e in E] / (x_e^2 : e in E).
```

For `F subseteq E`, write `x_F=prod_{e in F} x_e`. These monomials form a basis, so `[x_E]` is unambiguous. Form the symmetric matrix

```
A_uv = x_{uv} if uv in E, and 0 otherwise,
Delta_G = det(I-A).
```

Since `Delta_G-1` is nilpotent, `Delta_G^s` is defined by its finite formal binomial expansion and has coefficients in `Q[s]`.

### Theorem 2.1 — determinant/chromatic identity

For every finite simple graph,

```
F_G(s) := [x_E] Delta_G^s
        = sum_{D in D(G)} (-2)^{|D|} chi_{I_D}(s),              (2.1)
```

where `chi_H` is the ordinary chromatic polynomial.

**Proof.** In the permutation expansion of the determinant, a transposition uses an edge variable twice and vanishes. A permutation cycle of length at least three is an actual simple directed cycle. Its permutation sign together with the negative matrix entries gives a factor `-1`, independent of its length. The two orientations of each undirected cycle therefore give `-2`. Distinct permutation cycles are vertex-disjoint. Thus

```
Delta_G = sum_{F a vertex-disjoint family of simple cycles}
                 (-2)^{|F|} x_{union F}.                     (2.2)
```

For an integer `s>=0`, regard the `s` determinant factors as labelled colors. A surviving full-edge monomial chooses vertex-disjoint cycles in each factor, never repeats an edge, and covers all edges. Its union is an actual partition `D`. Assigning its cycles to factors is exactly a proper coloring of `I_D` with `s` colors. Every assignment has weight `(-2)^{|D|}`. This proves (2.1) at all nonnegative integers. Both sides are polynomials in `s`, so it proves the identity formally. The empty graph gives `1` on both sides. ∎

**Important:** (2.1) already uses genuine simple-cycle atoms. Merely replacing a closed-walk discussion by the determinant's permutation expansion does not fix the objective: the unwanted factor is now explicitly `chi_{I_D}(s)`.

### Corollary 2.2 — the inverse determinant has no cancellation, but the wrong valuation

Define

```
R_G(t) = [x_E] det(I-A)^(-t/2).
```

For a graph `H` on `q` vertices, write

```
(-1)^q chi_H(-z) = sum_{j=0}^q b_j(H) z^j.
```

Then `b_j(H)` are nonnegative integers, `b_q(H)=1`, and their first nonzero index is the number of components of `H`. It follows that

```
R_G(t) = sum_{D in D(G)} sum_j
                   2^{|D|-j} b_j(I_D) t^j.                   (2.3)
```

In particular, for an even graph,

```
R_G(t) - Z_G(t) has nonnegative integer coefficients,
ord_{t=0} R_G(t) = kappa_e(G).                               (2.4)
```

**Proof of the coefficient assertions.** Put `B_H(z)=(-1)^q chi_H(-z)`. For a nonloop edge `e`, deletion-contraction gives

```
B_H(z) = B_{H-e}(z) + B_{H/e}(z),
```

with parallel edges after contraction simplified. For an edgeless `q`-vertex graph, `B_H=z^q`. Induction proves nonnegative coefficients. Contraction preserves the number of components; deletion either preserves it or increases it by one. The same induction proves that the first nonzero exponent is exactly the component count. The leading coefficient is one.

Substitution in (2.1) gives (2.3). The `j=|D|` term contributes exactly the corresponding term of `Z_G`, and all lower terms are nonnegative. Finally, `I_D` has exactly `kappa_e(G)` components: cycles from different original components cannot intersect, and an original edge-adjacency chain connects the cycles covering its successive edges. Nonemptiness of `D(G)` now proves (2.4), including the edgeless case. ∎

Thus the apparent low-order integer certificate is **universally nonzero for the wrong reason**. For a connected nonempty even graph, `[t]R_G>0` whether or not `G` has a one-cycle partition. There is no cancellation left whose control could turn this coefficient into a certificate for `Z_G`.

For comparison, the ordinary trace-log expansion identifies `R_G` with the generating polynomial of local transition systems: pair the incident edges at each vertex, follow the resulting edge-simple closed trails, and weight by `t` per trail. A closed trail of length `l` has `2l` rooted directed descriptions; these cancel the factor `2l` in the trace-log denominator. Exponentiation gives unordered trail partitions. Repeated original vertices are allowed. This interpretation is consistent with (2.3), but is **not** used as a simple-cycle certificate.

---

## 3. Exact obstruction families, and why a scalar basis change is insufficient

### 3.1 Arbitrarily many forced simple cycles, but order one

Let `B_h` consist of `h>=1` triangles sharing exactly one common vertex, with all other vertices distinct. It is even and simple, with `n=2h+1` and `m=3h`.

A simple cycle cannot traverse two articulation blocks without repeating the common vertex. Hence the triangle partition is forced, and its intersection graph is `K_h`. Formula (2.1) gives

```
Z_{B_h}(t) = t^h,
R_{B_h}(t) = product_{j=0}^{h-1} (t+2j),
[t] R_{B_h}(t) = 2^{h-1}(h-1)!.                             (3.1)
```

This is a characteristic-zero obstruction for every `h`, with a complete positive coefficient explanation. It is not the earlier failed parity argument. It is also not a counterexample to a linear bound: here `c=(n-1)/2`.

Even the intersection pattern matters independently of the number of atoms. Three triangles sharing one vertex have `R=t(t+2)(t+4)`, whereas three triangles in an articulation chain have `R=t(t+2)^2`. Both have `Z=t^3`, `n=7`, and `m=9`.

### 3.2 No uniform scalar linear transform, even at fixed `n,m`

Fix `l>=3` and consider these even simple graphs, all with `n=m=2l`:

* `G_1=C_{2l}`;
* `G_2`, two vertex-disjoint copies of `C_l`;
* `G_3`, two copies of `C_l` sharing one vertex, together with one isolated vertex.

Their actual and determinant polynomials are

```
          Z_G(t)          F_G(s)
G_1       t               -2s
G_2       t^2              4s^2
G_3       t^2              4s(s-1).
```

Thus

```
F_{G_3} = F_{G_2} + 2 F_{G_1},
but Z_{G_3} != Z_{G_2} + 2 Z_{G_1}.                          (3.2)
```

There cannot be a `Q`-linear operator `L_{n,m}:Q[s] -> Q[t]` satisfying `L_{n,m}(F_G)=Z_G` for all such graphs. Applying it to (3.2) would give `t^2=t^2+2t`. The same obstruction applies to `R_G`, since the change `s=-t/2` is invertible.

This rules out, in particular, recovering the actual polynomial by a fixed coefficient reweighting or scalar Stirling/basis transform of this determinant coefficient. It does **not** rule out graph-dependent transforms retaining the individual intersection graphs, nonlinear transforms, or other auxiliary data. Such additional information is exactly what this scalar coefficient has not separated.

### 3.3 A transparent non-cactus calculation: `K5`

An actual partition of `K5` has either two or three cycles. In the two-cycle case both are Hamilton cycles. There are 12 undirected Hamilton cycles, each with a Hamilton complement, giving six partitions. In the three-cycle case the lengths are `3,3,4`. Choose the common vertex of the triangles in five ways, and split the remaining four vertices into two unordered pairs in three ways. The remaining edges form the required four-cycle. Therefore

```
Z_{K5}(t) = 6t^2 + 15t^3.
```

Every two cycles in `K5` intersect in a vertex, so `I_D` is complete. Consequently

```
R_{K5}(t) = 6t(t+2) + 15t(t+2)(t+4)
          = 132t + 96t^2 + 15t^3.                           (3.3)
```

Of the 243 local transition systems, only 21 are actual simple-cycle partitions. Even the coefficient of `t^2` is contaminated: it is 96 in `R`, but only 6 in `Z`.

---

## 4. An exact formula for `Z`, and the necessary vertex reset

There is no difficulty writing a correct algebraic expression for the actual polynomial. The difficulty is extracting a linear upper bound on its valuation.

Let

```
S_G(x) = sum_{C a simple cycle} x_C  in R_E.
```

Then

```
Z_G(t) = [x_E] exp(t S_G(x))
       = [x_E] product_C (1+t x_C).                         (4.1)
```

A product survives exactly when the cycles are edge-disjoint. The exponential's `q!` ordered descriptions cancel its denominator, so every unordered partition has coefficient one.

To obtain `S_G` from a determinant while really enforcing vertex simplicity, introduce commuting square-zero vertex variables

```
R_{E,V} = R_E[y_v : v in V] / (y_v^2 : v in V),
Y = diag(y_v).
```

Let `rho:R_{E,V}->R_E` be the `R_E`-linear map sending every square-free vertex monomial `y_U` to `1`. Then

```
-1/2 log det(I-YA) = sum_{C a simple cycle} x_C y_{V(C)},
S_G(x) = rho(-1/2 log det(I-YA)),
Z_G(t) = [x_E] exp(t rho(-1/2 log det(I-YA))).                (4.2)
```

**Proof of the first equality.** In

```
-1/2 log det(I-YA) = (1/2) sum_{l>=1} tr((YA)^l)/l,
```

a repeated vertex makes a term zero. A two-step return uses `x_e^2` and is also zero; the diagonal of `A` is zero. Every surviving walk is a vertex-simple cycle of length at least three. Its `l` roots and two orientations give coefficient one. All series are finite in the nilpotent algebras. ∎

### The cutoff obstruction is exact, not heuristic

The map `rho` is **not multiplicative**:

```
rho(y_v^2)=0, but rho(y_v)^2=1.                              (4.3)
```

In particular, it cannot be commuted through the exponential in (4.2). In the bowtie, write its two cycle terms as `a y_U` and `b y_W`, where `U` and `W` share the cutvertex. Then

```
[x_E] exp(t rho(a y_U+b y_W)) = t^2,
[x_E] rho(exp(t(a y_U+b y_W))) = 0.                          (4.4)
```

More generally, in a full edge partition a vertex `v` occurs on exactly `d_G(v)/2` simple cycles. Before resetting the vertex variables, its contribution is `y_v^{d_G(v)/2}`. A single global square-zero copy therefore annihilates **every** full partition whenever some degree is at least four. The same problem occurs with even Grassmann pairs `bar(psi_v) psi_v`; their square is zero.

Using separate nilpotent colors/replicas avoids that annihilation but changes the resource. In a model whose color classes are vertex-disjoint cycle families, the cycles through a vertex must all receive distinct colors, so at least `max_v d(v)/2` colors are required. On `K_{2r+1}` this is `r`, and `n*r` vertex/color slots are quadratic in `n`. This is a statement about that replica model, not a lower bound on the dimension of every conceivable representation.

Resetting **between** atoms gives the correct formula (4.2), but loses the proposed single-vertex-set nilpotency argument. The remaining edge algebra has `m` independent square-zero generators. No linear bound on the number of atoms follows from (4.2).

For orientation, the existing `K_(2r,2r,2r)` family has a partition into `4r^2` triangles and `n=6r`; thus both `deg Z` and `deg R` are `4r^2`. The triangle partition is obtained by indexing each part by `Z_(2r)` and taking `(X_i,Y_j,Z_(i+j))` for all `i,j`. Every edge occurs once, and the length-three lower bound proves maximality of that count. This concerns **maximum** partition size, not minimum size, and supplies no counterexample to the requested bound.

### What elementary sign changes cannot do

Replacing each unoriented edge variable by `epsilon_e x_e` multiplies every full-edge coefficient by the same factor `prod_e epsilon_e`. Similarly, a multiplicative weight per visit to `v` contributes the common factor `a_v^{d(v)/2}` to every transition partition, simple or not. These local edge/visit signs cannot selectively remove the spurious lower-degree terms of `R_G`.

This observation does not cover arbitrary pairing-dependent Pfaffian signs, asymmetric arc weights, or nonlocal representation-theoretic projections. Those would require a new cancellation and nonvanishing argument; none is supplied here.

---

## 5. Why polynomial positivity or degree has not supplied the missing theorem

The desired implication is

```
there exists j <= Cn with [t^j] Z_G(t) > 0.                  (5.1)
```

The audited determinant instead proves `[t^{kappa_e(G)}]R_G>0`, through positive contributions from partitions of *every* size. Inequality `R_G >= Z_G` coefficientwise has the wrong direction for deducing (5.1).

Formula (4.2) restores the correct atoms and exact unit edge capacities, but provides no estimate on the first nonzero exponent after the nonmultiplicative reset. A representation-degree argument would have to apply to **that projected expression**, not to the unprojected determinant or its global exterior degree. An asserted `O(n)` cutoff for it would be the still-missing substantive theorem, not a consequence of the identities above.

---

## 6. A universal obstruction to stability of the natural atom polynomial

Define the multiaffine polynomial with one variable per simple cycle:

```
P_G(z) = sum_{D in D(G)} product_{C in D} z_C.               (6.1)
```

Here real stable means nonzero whenever every variable has strictly positive imaginary part. The coefficients of `P_G` are real and nonnegative.

### Theorem 6.1 — stability iff the partition is unique

For a finite even simple graph, `P_G` is real stable if and only if `D(G)` has exactly one member.

**Proof.** A unique partition gives a monomial, which is stable, including the constant monomial for the empty graph.

Conversely, choose distinct partitions `D,D'`. Remove their common cycles, writing the remaining families as `L` and `R`. Build a bipartite graph `H` on `L union R`, joining cycles when they share an **edge of the original graph**. Every edge covered by these families lies on exactly one left cycle and one right cycle.

Each component of `H` has at least two cycles on each side. Indeed, if there were a single left cycle, all its neighboring right cycles would be cycles contained in its edge set. A simple cycle contains no proper nonempty cycle edge set, forcing the same cycle on both sides, contrary to removal of common cycles. The argument is symmetric.

Set every cycle variable outside `D union D'` to zero. A surviving exact partition must retain each common cycle. For every remaining original edge, its left and right cycle-selection indicators must sum to one. On a connected component of `H`, this forces either all left cycles or all right cycles, and each of those choices is feasible. Thus the specialized polynomial is exactly

```
product_{C in D intersect D'} z_C
  * product_{components K of H}
      ( product_{C in L intersect K} z_C
        + product_{C in R intersect K} z_C ).               (6.2)
```

Choose two left cycles in one component, retain their variables `x,y`, and set every other variable occurring in (6.2) to one. If `H` has `h` components, the resulting bivariate polynomial is

```
2^{h-1}(xy+1).                                             (6.3)
```

It is not stable: it vanishes at `x=y=i`. To justify the real specializations directly, perturb every specialized value `a` (zero or one) to `a+i epsilon` and keep `x=i`. By multiaffinity the full polynomial is `A_epsilon+B_epsilon y`. At `epsilon=0`, its coefficient of `y` is `2^{h-1}i`, which is nonzero, and its root is `i`. For all sufficiently small positive `epsilon`, the root remains in the upper half-plane. Every other variable is also in that half-plane. This is a zero of the original polynomial in the forbidden domain. ∎

Equivalently, the specialization (6.3) has Rayleigh difference

```
(partial_x P)(partial_y P) - P(partial_x partial_y P)
    = -2^{2h-2} < 0.
```

This rules out applying stable/matroid-basis support machinery **directly to (6.1)** for any graph with alternative cycle partitions. It is much stronger than showing a failure on one particular dense graph.

The scope matters. The theorem does **not** say that the diagonal specialization `Z_G(t)=P_G(t,...,t)` is never real-rooted. For example, `Z_{K5}=3t^2(2+5t)` is real-rooted. Nor does it rule out an auxiliary stable polynomial followed by an operation not preserving stability. Even univariate real-rootedness alone would not bound the multiplicity of zero in terms of `n`.

---

## 7. Verification and preserved files

Run from `/workspace/leanproject`:

```
PYTHONDONTWRITEBYTECODE=1 PYTHONHASHSEED=0 \
  python3 Submission/ResearchAlgebraicBoundCheck.py
```

The checker uses only the Python standard library and exact integer/rational arithmetic. It writes no files. Its ten inputs are the empty graph, isolated vertices, a triangle, a hexagon, two disjoint triangles, a bowtie with an isolate, three- and four-triangle bouquets, a three-triangle chain, and `K5`. These are targeted identity/obstruction checks, not a graph catalogue or an attempted finite proof of a universal bound.

The successful run independently verifies:

| Check | Result |
|:---|:---|
| Direct square-free permutation determinant, finite binomial power, and chromatic sum (2.1) | Agree on all ten inputs |
| All local transition systems versus actual simple-cycle exact partitions | 380 transition systems; both polynomials agree with their separate algebraic formulas |
| Vertex-nilpotent determinant logarithm | Exactly the simple-cycle atom polynomial with vertex markers |
| Reset before exponentiation | Exactly `Z_G` on all inputs |
| Exponentiation before reset | Zero on every tested input having degree at least four, as proved generally |
| Fixed-`n,m` scalar linear obstruction | Verified at `n=m=6` |
| Two-partition overlap factorization and negative Rayleigh specialization | All 210 unordered pairs of the 21 `K5` partitions |
| Protected files | All 46 preexisting files under `Submission/` and `newSubmission/` unchanged during the checker |

The key explicit outputs are

```
bowtie:       Z=t^2,             R=2t+t^2
bouquet_3:    Z=t^3,             R=8t+6t^2+t^3
chain_3:      Z=t^3,             R=4t+4t^2+t^3
bouquet_4:    Z=t^4,             R=48t+44t^2+12t^3+t^4
K5:           Z=6t^2+15t^3,     R=132t+96t^2+15t^3.
```

The infinite-family and universal obstruction statements rest on the proofs above, not extrapolation from these tests. The checker does not assert or test a purported universal constant.

The protected specification SHA-256 is unchanged:

```
429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde
```

Independent pre-work aggregate hashes, computed by hashing sorted `sha256sum` output with the two permitted new paths excluded, were:

```
Submission/:    2d25bc715fb50be38d11c96f62c0a32cfa778983d637e3c427db23e2fec1a399
newSubmission/: d06b98641b1d32f62704b53c7d4d5138b68d2b2804269926f2efb2aaec033df1
```

Both post-work aggregate hashes matched these pre-work values exactly.

## Conclusion

The determinant candidate is now audited using actual simple-cycle partitions and with **all characteristic-zero cancellation controlled**. It still has the wrong valuation, exactly and universally. The correct reset formula has no proved vertex-linear valuation bound, and the natural full atom polynomial lacks real stability whenever there is more than one partition.

**No actual `c(G)<=Cn` theorem has been proved.** No edit to the specification is justified. A future algebraic certificate must supply genuinely additional information that separates atom count from intersection-coloring weights and remains nonzero after enforcing vertex simplicity per atom; the formulas here do not supply that missing theorem.
