# Global parity optimization: a matroid-intersection and separator reduction

## Outcome

This does **not** prove `R(Q_n) <= C 2^n`, and it gives no new dimension-uniform Ramsey bound. The additional result proved here is an exact reduction that eliminates **all even-side injections simultaneously**, followed by an arbitrary-batch version that permits changing all odd images as well.

For one missing odd vertex, the possible images of its neighborhood, over *every* compatible even-side injection, are exactly the common bases of two rank-`n` matroids. Failure of extension has an exact two-flat blue certificate. For an arbitrary batch of odd vertices, every attempted reassignment is tested against one fixed reserve matroid; all even images may be rematched globally. Hamming-ball batches give a separator-scale version with only `O(2^n/sqrt(n))` even variables still constrained by frozen odd images.

The unresolved step is to use the simultaneous family of these certificates, as the odd embedding and the batch vary, to obtain a blue cube or a successful red rebuild. No independent-domain, bounded-reconfiguration, uniform-witness, or fractional-to-integral assertion is assumed.

No Lean files were edited. In particular, `Submission/Spec.lean` retains SHA-256
`9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b`.

## 1. Global optimization, including changes of the host cut

Let `n >= 1`, let `X,Y` be the even and odd vertex classes of `Q_n`, and put

```
|X| = |Y| = m = 2^(n-1).
```

All embeddings are ordinary injective graph homomorphisms; extra host edges are irrelevant.

First fix disjoint host sets `A,B`, with `a=|A| >= m` and `|B| >= m`. A feasible red state consists of

* a subset `J` of `Y`;
* an injection `g:J -> B`;
* some injection `f:X -> A` such that all required edges between `X` and `J` are red.

Define `k_R(A,B)` to be the maximum possible `|J|`, optimizing over **both** injections and over `J`. Equivalently, if `L_y(f)` are the user's exact lists, then

```
k_R(A,B) = max_f matching_number(L(f))
         = m - min_f max_{S subset Y} (|S|-|union_{y in S} L_y(f)|).
```

Thus this is global Hall-deficiency minimization, not maximality under a prescribed set of small moves.

For fixed `g`, define

```
D_x = A intersect intersection_{y in J intersect N_Q(x)} N_R(g(y)).
D(S) = union_{x in S} D_x.
```

The intersection with no constraints is `A`. Feasibility says that the bipartite graph with left class `X` and lists `D_x` has a matching saturating `X`. In particular,

```
sigma(S) := |D(S)| - |S| >= 0                 (S subset X).        (1)
```

If `g` attains `k_R(A,B)<m`, then every improvement obtained by changing any number of its odd images and rematching the entire even side is impossible.

### Why this does not replace Ramsey by a stronger fixed-cut problem

In a complete host `V` of size `N >= 2m`, fix any integer `a` with `m <= a <= N-m`. Then

```
there is a red Q_n in V
 iff max_{A subset V, |A|=a} k_R(A,V\A) = m.                       (2)
```

To prove the nontrivial direction in this equivalence, take a red cube, put its `m` even images in `A`, exclude its `m` odd images from `A`, and pad with unused vertices to size `a`. The prescribed range of `a` makes this possible. The other direction is immediate.

Thus changing the cut, including rebuilding inside a red clique missed by an earlier cut, is retained in the global problem. The reductions below apply to each cut. A genuine countercoloring would have to satisfy their failure conditions for both colors and every cut, not merely for one unsuccessful parity injection.

## 2. Eliminating every even injection: the reserve matroid

The following statement applies to any bipartite target, not only to cubes.

Fix a feasible list system `D_x` for `m` left labels `X`, and a set `U subset X` of size `r`. Write `F=X\U`.

Let `M_U` be the transversal matroid on ground set `A` presented by the labels `U` and lists `D_x`: a set of host vertices is independent if it can be matched injectively to distinct labels of `U`.

Let `M_F` be the analogous transversal matroid presented by `F`. Its rank is `m-r`, since the original full matching exists. Define

```
M_res = truncation_to_rank_r(dual(M_F)).                           (3)
```

Its rank function is explicitly

```
r_res(S) = min{r, |S| - (m-r) + r_F(A\S)}.                         (4)
```

In particular, for `|S| <= r`,

```
S is independent in M_res
 iff F can be matched into A\S.                                   (5)
```

This follows directly from the dual rank formula: independence means deleting `S` leaves the full rank `m-r` of `M_F`. The truncation only imposes `|S|<=r`.

### Common-base theorem

The following two families of `r`-subsets of `A` are equal:

1. the images `f(U)` over **all** matchings `f` saturating `X` in the list graph;
2. the common bases of `M_U` and `M_res`.

**Proof.** A full matching matches `U` onto its image `S`, so `S` is a basis of `M_U`; it matches `F` into `A\S`, so (5) makes `S` a basis of `M_res`. Conversely, these two basis conditions give a matching of `U` onto `S` and a matching of `F` into `A\S`. Their union saturates `X`. ∎

Nothing bounds how many old even images change. The matching on `F` may be entirely different from the starting one.

### A structural restriction on the reserve matroid

For any one initial full matching `f`, put

```
P_free = A\f(F),        |P_free|=a-m+r.
```

Keeping `f|F` shows that every at-most-`r` subset of `P_free` is independent in `M_res`. Thus

```
M_res restricted to P_free is the uniform rank-r matroid.         (6)
```

Consequently every flat of reserve rank `j<r` contains at most `j` elements of `P_free`. The reserve matroid is not an arbitrary rank-`r` obstruction: it has this large uniform restriction.

## 3. One missing odd vertex: exact blue certificates

Take a globally optimal state `g:J -> B`, with `k=|J|<m`, and take `y in Y\J`. Put

```
U=N_Q(y),        |U|=n.
```

Construct the two rank-`n` matroids in Section 2 from the domains determined by `g`. For `b in B\g(J)`, write `R_b=N_R(b) intersect A`.

### Root extension criterion

There is an extension with `g(y)=b`, keeping the other odd images but allowing **all even images to change**, if and only if `R_b` contains a common basis of `M_U` and `M_res`.

**Proof.** Exactly the labels in `U` acquire an additional red-adjacency requirement, namely that their images lie in `R_b`. Apply the common-base theorem. ∎

Since `g` was optimized globally, this extension fails for every such `b`.

### Exact capped-slack Hall certificate

Failure is equivalent to the existence of

```
P subset F=X\U,
nonempty T subset U,
W = D(T)\D(P)
```

such that

```
0 <= sigma(P) <= |T|-1,
|R_b intersect W| <= |T|-sigma(P)-1.                              (7)
```

Furthermore,

```
|W| = |T|-sigma(P)+sigma(P union T),
|N_B(b) intersect W| >= sigma(P union T)+1.                        (8)
```

Here `N_B` denotes the blue neighborhood, not the host set `B`.

**Proof.** After imposing `g(y)=b`, a Hall witness decomposes as `P union T`. Its new neighborhood is

```
D(P) union (D(T) intersect R_b).
```

Thus Hall fails exactly when

```
sigma(P) + |R_b intersect (D(T)\D(P))| <= |T|-1.
```

The original Hall condition gives `sigma(P)>=0`, and `T` cannot be empty. This proves (7) and the equivalence. Expanding the definition of `sigma(P union T)` gives the first identity in (8); subtracting the red-neighbor bound gives the blue bound. ∎

This is a genuine global-rematching certificate. It says that an extension failure has a near-tight block of frozen labels, with fewer than `n` units of Hall slack, and a reservoir to which `b` is blue except for at most `n-1` vertices. It does **not** assert that this reservoir is large.

### Exact two-flat form

A flat of a matroid is a set closed under matroid span. Failure of extension is equivalent to the existence of flats

```
F_1 of M_U,    F_2 of M_res,
r_U(F_1)+r_res(F_2) <= n-1,
R_b subset F_1 union F_2.                                         (9)
```

Therefore `b` is blue-complete to

```
A\(F_1 union F_2).                                                (10)
```

This is the matroid-intersection dual, but here it has a short direct Hall proof.

**Proof of failure => (9).** Take `P,T` from (7), and put `q=|R_b intersect W|`. Any matching from `R_b\D(P)` into `U` uses at most `n-|T|` labels outside `T` and at most `q` available images for labels in `T`. Hence

```
r_U(R_b\D(P)) <= n-|T|+q.
```

An independent reserve set contained in `D(P)` can have at most `sigma(P)` elements: deleting more would leave fewer than `|P|` possible images for the frozen labels `P`. Thus

```
r_res(R_b intersect D(P)) <= sigma(P).
```

Their sum is at most `n-1` by (7). Take their closures in their respective matroids. The closures preserve rank and cover `R_b`, proving (9).

**Proof of (9) => failure.** If a common basis `S subset R_b` existed, its elements in `F_1` would number at most `r_U(F_1)`, and its remaining elements, which lie in `F_2`, would number at most `r_res(F_2)`. Thus `|S|<=n-1`, a contradiction. ∎

Each set (10) hits **every** feasible image set of `N_Q(y)`, not just the neighborhood images under one `f`. It is nonempty because a common basis exists before imposing adjacency to `b`.

There are at most

```
sum_{j=0}^{n-1} binom(2a,j)                                      (11)
```

possible flat pairs of total rank at most `n-1`: a rank-`i` flat is the closure of an `i`-element basis, and Vandermonde's identity counts the pairs of bases. At `a=Theta(2^n)`, this upper bound is `exp(O(n^2))`, too large for a useful pigeonhole conclusion about only `Theta(2^n)` candidate vertices.

## 4. Arbitrary odd-image batches, with no radius restriction

The preceding theorem does not by itself justify freezing the odd images. The following exact batch version retains their reconfiguration.

Choose **any** set `Z subset Y` containing at least one unmatched label. Keep only

```
g_0 = g restricted to J\Z
```

frozen, and allow an arbitrary injection

```
h: Z -> B\g_0(J\Z).
```

The proposed new state has

```
|J\Z|+|Z| = k+|Z\J| > k
```

embedded odd labels. Put `U=N_Q(Z)`, `r=|U|`, and `F=X\U`. Define base domains using only `g_0`:

```
D_x^0 = A intersect intersection_{y in (J\Z) intersect N_Q(x)} N_R(g_0(y)).
```

These base domains have a full matching, since only old constraints have been dropped. Define the reserve matroid from `F` and `D^0` as in (3). **It is fixed for this batch and does not depend on h.**

For `x in U`, let

```
D_x^h = D_x^0 intersect intersection_{z in Z intersect N_Q(x)} N_R(h(z)),
```

and let `M_h` be their transversal matroid, of rank at most `r`.

### Arbitrary-batch criterion

The proposed odd reassignment `g_0 union h` can be completed by some even injection if and only if `M_h` and `M_res` have a common independent set of size `r`.

The proof is exactly the two-disjoint-matchings proof in Section 2. In particular, the criterion permits an entirely new injection on all of `X`, not merely on `U`.

Because the old state was globally optimal, **for every h** there are flats `H_h` of `M_h` and `K_h` of `M_res` with

```
A = H_h union K_h,
r_h(H_h)+r_res(K_h) <= r-1.                                      (12)
```

This dual statement also follows directly from Hall. If `P subset F`, `T subset U` witness failure, set `S=A\D^0(P)`. The rank bounds are

```
r_h(S) <= r-|T| + |D^h(T)\D^0(P)|,
r_res(D^0(P)) <= |D^0(P)|-|P|.
```

Hall failure says their sum is at most `r-1`; taking closures produces (12). Conversely, a cover (12) precludes a common independent `r`-set by the same rank count as before.

The choice `Z=Y` allows a complete odd-side rebuild. Thus the framework does not assume that a successful repair, if one exists, can be achieved with `O(1)`, `O(n)`, or `O(n^2)` odd-image changes.

## 5. Cube geometry makes the batch reduction more specific

Fix the unmatched root `y`, and let

```
Z_s = {z in Y : d_H(y,z) <= 2s},
U_s = N_Q(Z_s) = {x in X : d_H(y,x) <= 2s+1}.
```

Binomial coefficients outside their usual range are understood to be zero. Then

```
|Z_s| = sum_{j=0}^s binom(n,2j),
|U_s| = sum_{j=0}^s binom(n,2j+1),
|U_s|-|Z_s| = binom(n-1,2s+1).                                  (13)
```

The last identity follows from
`sum_{i=0}^t (-1)^i binom(n,i)=(-1)^t binom(n-1,t)`.

Freeze only `g|_{J\Z_s}`. Every even label at distance at most `2s-1` from `y` has **no frozen odd neighbor**, so its base domain is exactly `A`. Only the outer even sphere

```
partial U_s = {x : d_H(y,x)=2s+1}
```

can carry frozen adjacency constraints. Its size is `binom(n,2s+1)`, and each of its vertices has at most `n-2s-1` frozen odd neighbors.

Two particular scales are informative:

* `s=1`: `|Z_1|=1+binom(n,2)` odd labels may all change, and all `n` even neighbors of the root become unpinned before the new odd assignment. The affected even set has size `n+binom(n,3)`. Thus the natural first batch already accommodates the stated `Theta(n^2)` odd-image reconfiguration issue.
* Choose odd `2s+1` nearest `n/2`. Standard central-binomial bounds and (13) give

```
|Z_s| = m/2 + O(m/sqrt(n)),
|U_s| = m/2 + O(m/sqrt(n)),
|partial U_s| = O(m/sqrt(n)).                                   (14)
```

Thus a hypothetical countercoloring yields a **half-sized cube-ball rebuilding obstruction with a thin pinned boundary**, tested against a fixed reserve matroid of rank `|U_s|` with a uniform restriction of size `a-m+|U_s|`. Every assignment of all odd labels of the ball fails the exact common-base test.

This is an exact separator reduction, not an assertion that a small boundary can automatically be absorbed. Host-image capacity outside the ball remains in the reserve matroid and is not discarded.

## 6. Precisely what remains unresolved

The following implications have been proved:

1. Full optimization over `f` is exactly represented by the two-matroid common-base family.
2. A failed root extension has the capped-slack certificate (7)-(8) and the genuine blue-complete set (10).
3. Failure of a globally maximal partial embedding persists through every arbitrary odd batch, in the precise sense (12).
4. Cube balls localize the frozen adjacency constraints to the boundary in (14), while retaining global capacity constraints exactly.

What has **not** been proved is a compatibility or growth theorem for these certificates across different odd assignments and different batches. For one optimized `g`, (9) allows the flat pair to depend on `b`. The proven estimates only guarantee that (10) is nonempty; they do not give size `m`, a common reserve for `m` candidate vertices, or a cube-shaped family of compatible reserves. The count (11) does not repair that loss at linear host size.

The batch statement is the stronger information that must be used: for a fixed batch, the reserve matroid is fixed while every internally consistent reassignment `h` is obstructed. At separator scale almost all moving even labels have no frozen adjacency constraints, but after `h` is chosen their red-neighborhood constraints are highly coupled. No argument here turns this simultaneous family of failed matroid intersections into either a blue `Q_n` or a successful red batch.

This is the remaining global combinatorial obstacle. Simply selecting a favorable injection independently for each Hall set, selecting a favorable flat pair independently for each candidate, or replacing the coupled batch by independent domains would not solve it. Nor has a minimum-deficiency augmenting procedure with a justified global termination argument been supplied.

Consequently neither the asserted absolute constant nor a disproof of its existence is established.

## Verification

`check_cube_global_hall_reduction.py` independently checks:

* all 3,672 feasible abstract list systems with `1<=m<=3` and `m<=a<=4`;
* 24,452 common-base identities and reserve-rank/uniform-restriction checks;
* 375,938 root-neighborhood cases, comparing full rematching, matroid intersection, flat covers, and capped-slack Hall certificates;
* 48 Hamming-ball parameter pairs through dimension 12, including exact boundary and surplus identities;
* 423 randomized genuine-cube batch instances in dimensions 2, 3, and 4, allowing large odd and even reconfigurations;
* global optimization over all even injections in 552 actual bipartite colorings (all 512 colorings of `K_(3,3)` for `Q_2`, and 40 sampled colorings of `K_(5,5)` for `Q_3`); for the 370 deficient optima, all 15,124 improving odd-batch assignments were rejected even after unrestricted even rematching.

All checks passed; the output is in `CubeGlobalHallVerification.txt`. The general proofs are above. These finite checks are not evidence that the unresolved linear Ramsey implication holds.
