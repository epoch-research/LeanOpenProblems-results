# Spectral entropy progress: eliminating low-complexity collapsed phases

## Status

**The constant-multiplier spectral cube embedding theorem is not proved here.**
In particular, this file does not remove the `d²` in
`CubeSpectralBenchmark.md`, and does not assert that a high-entropy homomorphism
law has positive injective mass.

A different, dimension-uniform result **is** proved. Under a fixed
`O(sqrt(N))` spectral bound, entire classes of collapsed phases can be eliminated,
including their possible host pools, their mixtures, and a controlled number of
exceptional source vertices. The result has three parts:

1. A **container/counting theorem for uniformly dense pool phases** on any
   source with a perfect matching. Complete bipartite phases are the simplest
   case. The theorem allows overlapping pools, unequal pool sizes, arbitrary
   prescribed source templates, and exceptions to the template.
2. At `N = C h`, the total mass of these phases is at most
   `exp(-h) (N)_h 2^(-dh/2)` under explicit complexity conditions. In particular,
   for prescribed template families this holds when the number of types is
   `o(sqrt(h)/log h)`, the number of exceptional positions is `o(h/log h)`, and
   the logarithm of the number of source templates is `o(h)`.
3. A **hard Hall obstruction, exact collision-defect identity, and exact
   collision-Möbius cancellation** show that this is legitimate configuration
   pruning: the actual injective count is unchanged. These are not marginal
   occupancy estimates. The same obstruction rules out the corresponding
   injective-boundary/individually-injective-half reflection configurations.

For complete-pool phases, one may take

\[
 \boxed{C\ge 64(K+6)^2}
\]

for a suitably chosen spanning subgraph of the original host; the precise
finite-dimensional complexity condition is (6.2) below. This is a constant for
**phase elimination**, not an embedding constant.

The earlier counterexamples are also distinguished from the present hypothesis
by **lower bounds** on their spectral norms: their growing repeated-profile or
clone parameters force the effective `K` to grow. Merely observing that their
published upper bounds are `o(N)` would not establish this distinction.

All counts are labelled; embeddings are ordinary, not induced. All logarithms
are natural. No Lean file, including `Spec.lean`, is changed.

---

## 1. A density-preserving reduction to reference density one half

There is a minor but important issue with the proposed biclique observation.
Under the original assumption, disjoint complete pairs satisfy

\[
 (1-p)\sqrt{|S||T|}\le K\sqrt N.
\]

One cannot discard the factor `1-p` when all that is assumed is `p >= 1/2`.
The following thinning lemma fixes this, while retaining actual density at
least one half. Thus the subsequent homomorphism lower bound has no hidden
loss from a density error.

### Lemma 1.1 (biased thinning)

Let `N >= 2`, `K >= 0`, and let `G` have actual density
`p = e(G)/binom(N,2) >= 1/2`, with

\[
 \|A_G-p(J-I)\|_{op}\le K\sqrt N.
\]

There is a spanning subgraph `G_*` of `G` such that its actual density is at
least `1/2` and

\[
 \|A_{G_*}-\tfrac12(J-I)\|_{op}\le(K+5)\sqrt N,
 \qquad
 \boxed{\|A_{G_*}-\tfrac12J\|_{op}\le\Lambda\sqrt N,
 \quad\Lambda=K+6.}                                      \tag{1.1}
\]

**Proof.** Put `q = 1/2 + 1/N`. If `p < q`, use `G` itself: changing the
reference density costs less than `(N-1)/N < 1` in operator norm.

If `p >= q`, retain each edge independently with probability `theta = q/p`.
Write `A_* = theta A_G + W`, where `W` has independent centred entries above
the diagonal, zero diagonal, and entries with range length at most one. For a
real unit vector `x`, the sum of the squared range lengths in `x^T W x` is at
most `4 sum_{i<j} x_i² x_j² <= 2`. Hoeffding and a Euclidean `1/4`-net give

\[
 \Pr(\|W\|_{op}>4\sqrt N)
 \le 2\exp(-(4-\log9)N).
\]

Writing `D = binom(N,2)`, the expected number of retained edges is `qD`.
The gap to `D/2` is `D/N`; the one-sided Hoeffding bound, using `e(G) <= D`, is

\[
 \Pr(e(G_*)<D/2)
 \le\exp(-2(D/N)^2/e(G))
 \le\exp(-(N-1)/N).
\]

For `N >= 2`, the sum of the last two failure bounds is at most

\[
 e^{-1/2}+2e^{-2(4-\log9)}<0.661<1.
\]

Choose an outcome satisfying both conclusions. Since

\[
 A_*-\tfrac12(J-I)
 =\theta(A_G-p(J-I))+W+\tfrac1N(J-I),
\]

its norm is at most `(K+4)sqrt(N)+1 <= (K+5)sqrt(N)`. Subtracting `I/2`
proves (1.1). The other branch satisfies the same, weaker bounds. ∎

All subsequent uses of `A-J/2` include its diagonal `-1/2`. It is not being
silently replaced by the zero-diagonal centred matrix. Finally,

\[
 \operatorname{inj}(H,G)\ge\operatorname{inj}(H,G_*).          \tag{1.2}
\]

The phase statements below concern `G_*`; they need not hold for all phases
in the original, possibly nearly complete, graph.

---

## 2. Two elementary spectral restrictions

It is useful to state these with an arbitrary reference `q`. Suppose

\[
 E=A-qJ,\qquad \|E\|_{op}\le\Lambda\sqrt N,
 \qquad 0<q<1.                                             \tag{2.1}
\]

### 2.1 Dense rectangles, including overlapping sets

If nonempty sets `S,T` have average cross-density at least `q+delta`, where
`0 < delta <= 1-q`, then

\[
 \delta |S||T|
 \le\mathbf1_S^T E\mathbf1_T
 \le\Lambda\sqrt{N|S||T|}.
\]

Consequently, with `beta = Lambda/delta`,

\[
 \boxed{|S||T|\le\beta^2 N.}                               \tag{2.2}
\]

The average counts ordered pairs in `S x T`, with the true zero adjacency
diagonal. The sets need not be disjoint.

For the reference `q=1/2` and a complete pair, `delta=1/2`, so `beta=2Lambda`.
Complete pairs are automatically disjoint in a simple graph.

### 2.2 Repeated profiles and approximate clones

Suppose a binary profile `b_y`, `y in T`, agrees with the adjacency rows from
`S` on all but at most `epsilon |S||T|` entries. Set
`sigma_y = 2b_y-1` on `T` and zero outside `T`, and put
`alpha = min(q,1-q)`. Directly, entry by entry,

\[
 \mathbf1_S^T E\sigma
 \ge(\alpha-\epsilon)|S||T|.
\]

Thus if `epsilon < alpha`,

\[
 \boxed{(\alpha-\epsilon)^2 |S||T|\le\Lambda^2 N.}       \tag{2.3}
\]

Here a disagreement decreases the signed contribution by exactly one; a
correct entry contributes either `q` or `1-q`.

In particular, at reference one half, identical rows on a set of size at
least `rho N` have multiplicity at most `4Lambda²/rho`. More generally,
profiles with error fraction `epsilon < 1/2` have multiplicity at most
`Lambda²/[rho(1/2-epsilon)²]`. This rules out growing exact clone parameters,
and also sufficiently accurate growing approximate-clone parameters.

For the original zero-diagonal matrix `A-p(J-I)`, (2.3) remains valid with
`Lambda=K` when `S,T` are disjoint: its `S x T` block is exactly `A-pJ`.

---

## 3. The general phase-elimination theorem

The next theorem is not restricted to cubes and uses no graph-counting or PSD
inequality.

Let `H` have `h=2m >= 2` vertices and a fixed perfect matching. Fix:

* a host satisfying (2.1);
* `0 < delta <= 1-q`, and `beta = Lambda/delta > 0`;
* an integer `t >= 1`;
* a nonempty finite family `Tcal` of maps `tau:V(H) -> [t]`;
* an integer `0 <= s <= h`.

The maps `tau` specify **source types**, not host labels. They need not be
surjective or proper colourings. Define

\[
 a=\min\{N,\lfloor\beta\sqrt N\rfloor\},\qquad
 D_a=\sum_{i=1}^{a}\binom Ni,\qquad
 R=\max\{1,N/\beta^2\},
\]
\[
 B_s(H,N,\beta)=\sum_{j=0}^{s}\binom hj R^j.                 \tag{3.1}
\]

### Definition: a uniformly dense pool witness with exceptions

Such a witness consists of:

* `tau in Tcal`;
* a set `F subset V(H)` with `|F| <= s`;
* nonempty host pools `S_1,...,S_t`.

Whenever `uv` is an edge of `H-F`, putting `i=tau(u)`, `j=tau(v)`, require

\[
 \begin{split}
  |N_G(x)\cap S_j|&\ge(q+\delta)|S_j| &&(x\in S_i),\\
  |N_G(y)\cap S_i|&\ge(q+\delta)|S_i| &&(y\in S_j).
 \end{split}                                               \tag{3.2}
\]

There is no requirement on source edges incident with `F` in the witness.
A homomorphism belongs to `Ccal = Ccal(Tcal,s,delta)` if it has such a witness
and `phi(v) in S_tau(v)` for every `v notin F`. Its images on `F` are arbitrary,
subject still to being a homomorphism of the **whole** source `H`.

Pools may overlap. Witnesses and pools may depend on the map being counted;
all possible pools and all possible witnesses are included in `Ccal`.

For `q=1/2`, `delta=1/2`, condition (3.2) says that the required pool pairs
are complete. This includes ordinary product homomorphism phases. For example,
`delta=1/4` permits genuinely non-complete pool pairs of minimum cross-degree
at least three quarters. Mere **average** density suffices for (2.2), but is
not substituted for (3.2) in the counting theorem.

### Theorem 3.1 (hard obstruction and total mass)

Every `phi in Ccal` satisfies

\[
 \boxed{|\operatorname{im}\phi|\le m+ta+s.}                  \tag{3.3}
\]

Moreover,

\[
 \boxed{
 |Ccal|\le |Tcal|(1+D_a)^t(\beta^2N)^m B_s(H,N,\beta).
 }                                                         \tag{3.4}
\]

The simpler bound `(1+D_a)^t <= (N+1)^(at)` is always valid, including `a=0`.

For the positive collision-defect polynomial

\[
 Z_{Ccal}(z)=\sum_{\phi\in Ccal}z^{h-|\operatorname{im}\phi|},
 \qquad r_0=\max\{0,m-ta-s\},
\]

all coefficients of degrees less than `r_0` vanish, and, for `0 <= z <= 1`,

\[
 0\le Z_{Ccal}(z)
 \le z^{r_0}|Tcal|(1+D_a)^t(\beta^2N)^m B_s(H,N,\beta).       \tag{3.5}
\]

Use `0^0=1` only for the vacuous case `r_0=0`.

### Proof

Fix a witness, with `|F|=j`, and form the type graph from the edges of `H-F`.
It can have loops. Call a type **small** if `|S_i| <= a`, and large otherwise.
By (2.2), every edge of the type graph has a small endpoint; a loop cannot
be at a large type. In particular, the large types are independent.

Let `r(F)` be the number of edges of the fixed perfect matching meeting `F`.
Then `r(F) <= j`, and its other `m-r(F)` edges lie in `H-F`. Let `U` be the
nonexceptional source vertices of small type. Every one of those intact
matching edges meets `U`, so

\[
 |U|\ge m-r(F)\ge m-j.
\]

The images of `U` lie in a union of at most `t` pools, each of size at most
`a`. Therefore

\[
 |\operatorname{im}\phi|
 \le ta+(h-|U|)\le m+ta+j\le m+ta+s,
\]

proving (3.3).

For the count, record only, for each type, either its small pool or the symbol
`large`. This is a **fingerprint** with at most `(1+D_a)^t` possibilities.
For a small pool `S`, put

\[
 T_\delta(S)=\{x:|N_G(x)\cap S|\ge(q+\delta)|S|\}.
\]

Once the small pools and their positions are fixed, replace every large pool
by

\[
 S_i^*=\bigcap_{j:\,ij\text{ an edge of the type graph}}T_\delta(S_j).
                                                               \tag{3.6}
\]

An empty intersection means all of `V(G)`. All neighbours of a large type are
small, and (3.2) gives `S_i subset S_i^*`. Keep small pools unchanged.
This produces one containing Cartesian box for each realized fingerprint.
Give each exceptional position the full host as its domain.

For each type edge, the enlarged pair still has average density at least
`q+delta`: for a small-large edge this follows from the definition of (3.6),
and for a small-small edge from the original witness. Thus every **intact**
matching edge has domain-size product at most `beta² N`, by (2.2).
All `2r(F)` positions of the other matching edges have domain size at most `N`.
The containing box consequently has size at most

\[
 (\beta^2N)^{m-r(F)}N^{2r(F)}
 =(\beta^2N)^m(N/\beta^2)^{r(F)}
 \le(\beta^2N)^mR^j.                                      \tag{3.7}
\]

We only count containing boxes; it is not asserted that every map in an
enlarged box is a homomorphism. Nor need enlargement preserve both directional
minimum-degree conditions in (3.2). The average-density statement just proved
is exactly what (3.7) needs.

Sum (3.7) over fingerprints, choices of `F`, and `tau`. This proves (3.4), with
no disjointness or uniqueness assumptions. A subset of `[N]` of size at most
`a` can be encoded by its increasing list, padded by zeros to length `a`.
Encoding `large` by the all-zero list proves `1+D_a <= (N+1)^a`.
Finally (3.3) and nonnegativity of coefficients imply (3.5). ∎

### 3.1 A sharper special case: all bicliques, not one chosen biclique

Let `H` be bipartite with parity classes of size `m`, and let `Ccal_bic` be the
homomorphisms whose **entire two image sets** form a complete pair. Take
`delta=1-q`. Then

\[
 \boxed{|Ccal_{bic}|\le 2D_a(\beta^2N)^m,\qquad
 |\operatorname{im}\phi|\le m+a\quad(\phi\in Ccal_{bic}).}    \tag{3.8}
\]

Indeed at least one image set has size at most `a`. Record that set and which
parity it is on, and enlarge the other pool to its full common neighbourhood.
This requires only `2D_a` fingerprints. This proves the proposed `C^(-h/2)`
penalty **after summing over every possible biclique in the host**, up to the
explicit fingerprint factor. A linear-size other side, as in a star phase,
is allowed.

---

## 4. Exact finite-population and injective-count consequences

These consequences refer to the actual count, not a replacement partition
function whose relation to embeddings is conjectural.

### 4.1 An explicit Hall obstruction in every forbidden box

If `ta+s < m`, the set `U` in the proof has

\[
 |U|\ge m-s>ta\ge\left|\bigcup_{u\in U}S_{\tau(u)}\right|.
                                                               \tag{4.1}
\]

Thus the support matrix of the witness has no injective assignment, even if
all graph-edge constraints are dropped. It also has no feasible fractional
row distributions with row sums one and column sums at most one: summing those
constraints over `U` contradicts (4.1).

In the notation of `CubeOccupancyPruning.md`, the capacitated entropy of each
such support matrix is `-infinity`, and its rectangular permanent is exactly
zero. This is a **conditional hard-capacity obstruction**, not an estimate of
expected loads.

### 4.2 Exact preservation of the injection coefficient

Let `Omega = Hom(H,G)`, `Omega_surv = Omega \ Ccal`, and

\[
 Z_G(z)=\sum_{\phi\in\Omega}z^{h-|\operatorname{im}\phi|}.
\]

There is the exact coefficientwise identity

\[
 \boxed{Z_G(z)=Z_{surv}(z)+Z_{Ccal}(z).}                     \tag{4.2}
\]

If `ta+s < m`, then

\[
 \boxed{\operatorname{inj}(H,G)=Z_G(0)=Z_{surv}(0).}          \tag{4.3}
\]

In fact **every count with collision defect less than `m-ta-s`** is preserved.
If `Z_surv(1)>0` and `mu_surv` is the uniform law on surviving homomorphisms,

\[
 \boxed{\operatorname{inj}(H,G)
       =Z_{surv}(1)\,\Pr_{\mu_{surv}}(\phi\text{ injective}).} \tag{4.4}
\]

No positivity of the last probability is inferred here.

### 4.3 The entire signed collision background cancels inside the removed class

For a set `Acal` of homomorphisms, define

\[
 H_{Acal}(\pi)=|\{\phi\in Acal:\phi\text{ is constant on every block of }\pi\}|,
 \qquad
 \mu(\pi)=\prod_{B\in\pi}(-1)^{|B|-1}(|B|-1)!.
\]

Quotient labels are allowed to coincide accidentally. The exact partition
lattice identity is

\[
 \sum_{\pi}\mu(\pi)H_{Acal}(\pi)
 =|\{\phi\in Acal:\phi\text{ injective}\}|.                 \tag{4.5}
\]

For a fixed map, the inner sum is over partitions refining its actual fibres.
It factors over those fibres; the factor of size `b` is `(1)_b`, hence is zero
unless `b=1`. For completeness, the polynomial
`sum_pi x^(number of blocks) product_B (-1)^(|B|-1)(|B|-1)!` is `(x)_b`:
interpret each block as a permutation cycle. Inserting a new element either
creates a singleton, of weight `x`, or inserts it into one of `b` cycle
positions, each changing the sign. This gives the recurrence
`P_(b+1)(x)=(x-b)P_b(x)`, with `P_0(x)=1`. Thus the cancellation is an
all-orders algebraic identity, not an extrapolation from finitely many checks.

It follows from (4.1) that

\[
 \sum_\pi\mu(\pi)H_{Ccal}(\pi)=0,
 \qquad
 \boxed{\operatorname{inj}(H,G)
      =\sum_\pi\mu(\pi)H_{\Omega_{surv}}(\pi).}              \tag{4.6}
\]

This removes the **full** positive and negative collision background of the
class at once. It is not a bound on its raw negative activities. In particular,
no positive core with negative isolated-vertex dressing is discarded on its
own. The restriction to `Ccal` is a global configuration restriction; no local
polymer factorization for this restriction is asserted.

### 4.4 An exact exclusion relevant to finite-population reflection

In the coordinate-swap reflection of `Q_d`, with `d>=2`, write `h=4r`. The boundary has
`2r` vertices, and each half has `r` vertices. An injective boundary together
with an injective half-extension avoiding the boundary uses `3r` distinct
host vertices. Therefore any pair of such half-extensions, even overlapping
each other, produces a full homomorphism with image size at least `3r`.

Consequently,

\[
 \boxed{ta+s<h/4\quad\Longrightarrow\quad
 Ccal\text{ contains no such boundary/half-extension pair}.} \tag{4.7}
\]

If all pairs of extensions of a proposed boundary family admit these pool
witnesses, then that family has **no half-extensions at all**: otherwise pair
an extension with itself. Thus its extension weights, negative Kneser mass,
and injective contribution are all zero. This statement only concerns the
specified class; it is not a general upper bound on Kneser negative mass.

---

## 5. Exact comparison with the cube baseline

Now let `H=Q_d`, `d>=1`, `h=2^d`, `m=h/2`, and `e=dh/2`. Suppose `N>=h`,
write `C=N/h>1`, and set

\[
 \mathcal B_d(N)=(N)_h2^{-e}.
\]

This is the **one-colour** finite-population random baseline.

From (3.4), the exact algebraic comparison is

\[
 \frac{|Ccal|}{\mathcal B_d(N)}
 \le |Tcal|(1+D_a)^t B_s\,
      \frac{N^h}{(N)_h}\left(\frac{\beta^2}{C}\right)^{h/2}.
                                                               \tag{5.1}
\]

Indeed `2^e = h^(h/2)`. The finite-population correction satisfies

\[
 \log\frac{N^h}{(N)_h}
 \le\sum_{i=0}^{h-1}\frac{i}{N-i}
 \le\frac{h(h-1)}{2(N-h+1)}
 \le\frac{h}{2(C-1)}.                                      \tag{5.2}
\]

Equations (5.1)--(5.2) prove that the per-vertex entropy penalty remains after
aggregating **all host realizations** of the specified source templates. No
count of maximal bicliques, and no assumption that the phases are disjoint,
is required.

### 5.1 The homomorphism lower bound, with the diagonal corrected

If the actual density of the host is at least `1/2`, the usual cube Sidorenko
inequality gives

\[
 \operatorname{hom}(Q_d,G)
 \ge N^h\left(\tfrac12(1-1/N)\right)^e
 \ge\mathcal B_d(N).                                      \tag{5.3}
\]

For the second inequality, Bernoulli gives
`1-i/N <= (1-1/N)^i`, so

\[
 (N)_h/N^h\le(1-1/N)^{\binom h2}\le(1-1/N)^e.
\]

The sole graph-counting input in this file is this established cube Sidorenko
inequality, which follows from the weakly norming property of the
cube. The same input is used in `CubeOccupancyPruning.md`; see Hatami,
*Graph norms and Sidorenko's conjecture*, arXiv:0806.0047, with the local source
at `/corpus/src/0806.0047/normFinal.tex`. Theorem 3.1 itself does not need it.

---

## 6. Explicit endpoint corollaries

### Corollary 6.1 (prescribed templates; all host pools; exceptions allowed)

Use `G_*` from Lemma 1.1, set `q=1/2`, and choose `0 < delta <= 1/2`. Put

\[
 \Lambda=K+6,\qquad \beta=\Lambda/\delta,\qquad
 C=N/h\ge16\beta^2.                                        \tag{6.1}
\]

Let `a,D_a,R,B_s,Tcal,t,s` be as in Section 3. Here `R=N/beta² >= 16h`.
If

\[
 \boxed{
 L:=\log|Tcal|+at\log(N+1)
       +\log\left(\sum_{j=0}^s\binom hj(N/\beta^2)^j\right)
 \le h/4,
 }                                                         \tag{6.2}
\]

then

\[
 \boxed{|Ccal|\le e^{-h}\mathcal B_d(N),\qquad ta+s<h/4.}     \tag{6.3}
\]

In particular (4.3), (4.6), and (4.7) apply.

**Proof.** Equations (5.1)--(5.2) bound the logarithm of the relative mass by

\[
 L+\frac{h}{2(C-1)}-\frac h2\log(C/\beta^2)
 \le h\left(\tfrac14+\tfrac1{30}-\tfrac12\log16\right)
 <-h.
\]

Both `log(N+1)` and `log R` exceed one. Since `B_s >= R^s`, (6.2) also implies
`ta+s < h/4`. ∎

For **complete** pool phases, `delta=1/2`, so the explicit multiplier condition
is `C >= 64(K+6)²`. For minimum-cross-degree `3/4` phases, take `delta=1/4`
and `C >= 256(K+6)²`.

In entropy language, every probability law supported on `Ccal` satisfies

\[
 H(\Phi)\le\log|Tcal|+t\log(1+D_a)+m\log(\beta^2N)+\log B_s
 \le\log\mathcal B_d(N)-h.
\]

This includes arbitrary mixtures of the permitted pool realizations, not just
independent uniform choices in one fixed pool system. It is an entropy bound
for laws supported on the class, not a bound on its probability under an
arbitrarily reweighted Gibbs law.

### 6.2 A genuinely high-entropy surviving law, and its exact limitation

Let `Z = hom(Q_d,G_*)`, and `Z_surv = |Omega_surv|`. By (5.3) and (6.3),

\[
 (1-e^{-h})Z\le Z_{surv}\le Z,
 \qquad Z_{surv}\ge(1-e^{-h})\mathcal B_d(N)>0.               \tag{6.4}
\]

Thus the uniform surviving law has Shannon entropy at least
`log B_d(N) + log(1-e^(-h))`. More importantly, the exact relation to the
original embedding problem is

\[
 \boxed{
 \operatorname{inj}(Q_d,G)
 \ge\operatorname{inj}(Q_d,G_*)
 =Z_{surv}\Pr_{\mu_{surv}}(\text{injective}).
 }                                                         \tag{6.5}
\]

For the full uniform homomorphism law `mu` on `G_*`,

\[
 \Pr_\mu(\text{injective})
   =(Z_{surv}/Z)\Pr_{\mu_{surv}}(\text{injective}),\qquad
 1-e^{-h}\le Z_{surv}/Z\le1.                                \tag{6.6}
\]

These classes cannot be responsible for a large hom-to-injective ratio: their
removal changes the injection probability by at most the factor
`(1-e^(-h))^(-1)`. But (6.5) does **not** say that the surviving injection
probability is positive. Controlling that probability is the remaining
embedding problem.

### 6.3 Growing prescribed templates

Fix `K`, `delta`, and a real constant `C_0 >= 16 beta²`, and take
`N_d = ceil(C_0 2^d)`. The fully explicit conclusion of Corollary 6.1 applies
at every `d` satisfying (6.2). In particular it applies for all sufficiently
large `d` to any sequence with

\[
 \log|Tcal_d|=o(h),\qquad
 t_d=o(\sqrt h/\log h),\qquad
 s_d=o(h/\log h).                                          \tag{6.7}
\]

To check the last claim without concealing a factor, use

\[
 a\le\beta\sqrt N,\qquad
 B_s\le(s+1)(hR)^s\quad(R\ge1).
\]

Each term of (6.2) is then `o(h)`. No unspecified asymptotic threshold is
needed to apply the theorem: (6.2) is its finite test.

In particular, a fixed cube-to-small-cube quotient with `t=O(h^(1/3))` types,
or with `t=polylog(h)` types, is allowed. Pools can be reselected arbitrarily
for each map. This is much more than bounding the entropy of one predetermined
biclique.

### 6.4 All source templates with a fixed number of types

If **every** map `tau:V(Q_d)->[t]` is permitted, then `|Tcal| <= t^h`.
Absorb this factor into the leading entropy penalty. The same conclusions
hold provided

\[
 \boxed{C\ge16\beta^2t^2,
 \qquad at\log(N+1)+\log B_s\le h/4.}                       \tag{6.8}
\]

This eliminates all such `t`-type phases, not just prescribed source patterns.
The factor `t²` in this version is explicit; it is not hidden in `K`.

For `s=0`, a simple, very conservative sufficient size condition for the
second inequality in (6.8) is

\[
 \boxed{N\ge(16\beta t C)^4.}                              \tag{6.9}
\]

Indeed `log(N+1) <= 3 N^(1/4)` for `N>=1`, since
`log N <= (4/e)N^(1/4)` and `log 2 <= (log 2)N^(1/4)`. Therefore

\[
 at\log(N+1)\le3\beta tN^{3/4}\le(3/16)h<h/4.
\]

Conditions such as (6.9) are intended at a **fixed** ratio `N/h=C` as the
cube grows. They are not a claim that biclique phases remain collapsed for
arbitrarily large `N` with `h` held fixed.

For the biclique class in (3.8), the sharper fingerprint cost is just
`log(2D_a)`, with no source-template factor. Under (6.1), a bound
`log(2D_a) <= h/4` gives the same `exp(-h)` mass estimate. Injective-count
preservation holds whenever `a<m`, and reflection exclusion whenever `a<h/4`,
by its sharper defect bound `m-a`. A convenient joint sufficient complexity
condition is `log 2 + a log(N+1) <= h/4`.

---

## 7. Why the previous obstructions do not refute this theorem

### 7.1 The reflection construction has a growing spectral lower bound

In `CubeFinitePopulationReflection.md`, choose an unmarked quotient cell.
Its `u` ordinary plus boundary vertices have identical adjacency profiles
outside that colour gadget's entire boundary, a set of size `N-2r`.
This follows from the block-constant initial matrix and the identical ordinary
lists; degree repairs do not touch those boundary rows. There are unmarked
cells once the quotient grows beyond the fixed number of markers.

Both colours have actual density exactly `1/2`. Applying (2.3) to the
disjoint row and column sets gives, for any bound
`||A-(J-I)/2|| <= K sqrt(N)`,

\[
 \boxed{u(N-2r)\le4K^2N,
 \qquad K\ge\tfrac12\sqrt{u(1-2r/N)}.}                     \tag{7.1}
\]

At fixed `N/h` and `u -> infinity`, `K` must grow. This applies also to the
flat-occupancy refinement, whose ordinary boundary profiles are unchanged.
It is a lower bound on the actual norm, not an inference from an inadequate
`o(N)` upper bound.

There is a second, more robust exclusion that does **not** assume repeated
profiles. With the notation of that file, let the quotient have `M_q` cells,
let the source fibre size be `u`, and let the number of marked residual
positions be `D_*`. Thus `h=4M_q u`. For any fixed pair of phases, outside
at most `4D_*` source positions the full cube uses a complete pool system with

\[
 t\le4M_q,\qquad s\le4D_* .                               \tag{7.2}
\]

The types are the first-two-coordinate choice and the quotient cell. This
single prescribed pattern works while the pools vary with the boundary and
the chosen phases. Tagged versus ordinary cells in the flat-occupancy version
can also be represented by these cell types.

Consequently, in **any reference-one-half host** satisfying
`||A-J/2|| <= Lambda sqrt(N)`, a realization of this template family with

\[
 4M_q a+4D_*<h/4                                         \tag{7.3}
\]

cannot have an injective boundary and an injective half-extension. This is the
exact exclusion (4.7), not just suppression of a lower bound on an error term.
For the original `M_q=2^a_src`, `u=2^(2a_src)` parameter choice, and also for
the polylogarithmic-quotient optimization, (7.3) eventually holds at fixed `K`
and fixed `N/h` for a hypothetical half-density host with that strong bound.
The counting theorem additionally suppresses the whole low-template
homomorphism class, whether or not its maps are half-injective. This statement
is about a phase in the reference-half host itself: thinning a different,
higher-density host need not preserve its original phase or extension lists.

### 7.2 The symplectic blow-ups also force a growing `K`

The clone graph in `CubeOccupancyPruning.md` has `M-1` nonzero base labels,
`L` clones each, and `N=L(M-1)`. A clone class has identical profiles outside
itself. Since both densities tend to `1/2`, (2.3) alone forces

\[
 K\ge(1/2-o(1))\sqrt{L(1-L/N)}\longrightarrow\infty.
\]

One can verify a sharper explicit bound. With `H_0` the symplectic sign matrix
restricted to nonzero labels,

\[
 H_0\mathbf1=-\mathbf1,\qquad H_0^2=MI-J.
\]

On `1^perp`, its eigenvalues have absolute value `sqrt(M)`. The blue adjacency
matrix is `(J-H_0 tensor J_L)/2`. On a lifted zero-sum eigenspace, its centred
matrix `A_B-p_B(J-I)` has eigenvalue `-L lambda/2+p_B`. Therefore both
complementary centred colour matrices satisfy

\[
 \boxed{
 \|A_c-p_c(J-I)\|_{op}\ge L\sqrt M/2-1,
 \qquad
 K\ge\tfrac12\sqrt L\sqrt{M/(M-1)}-1/\sqrt N.
 }                                                        \tag{7.4}
\]

The `L` in that construction grows. Thus the edge-pruning and high-entropy
counterexamples in that file do not obey a fixed-`K` hypothesis.

If a bounded-`L` version is examined with source size chosen so that `N/h` is
a sufficiently large constant, its biclique-supported laws are instead
covered by (3.8) and (5.1). The new theorem concerns
**configuration pruning**, with exact preservation (4.3), not deletion of
host edges. It does not contradict the earlier edge-deletion obstruction.

---

## 8. What is still missing from a full positive proof

Theorem 3.1 and Corollary 6.1 genuinely eliminate broad collapsed classes;
they do not classify all homomorphisms or all Gibbs phases.

* A general homomorphism always has a singleton-pool description with `t=h`.
  The fingerprint entropy is then much too large. It cannot be assigned a
  low-complexity witness for free.
* A general correlated phase need not satisfy the pointwise dense-pool
  condition (3.2), even if some of its one-edge averages are large.
* The surviving measure in (6.4) has high entropy, but no all-orders collision
  cumulant estimate or conditional capacity witness is constructed for it.
* In fact (4.2) preserves all sufficiently small-defect counts. The difficult
  surviving one-collision and other near-injective configurations have not
  been bounded by deleting the deeply collapsed class.

A sufficient next step would be an actual estimate

\[
 \Pr_{\mu_{surv}}(\text{injective})\ge e^{-L_K h}
\]

for this or another exactly identified positive subensemble. Together with
(6.4)--(6.5), that would give a genuine finite-population injective lower
bound. Even just positivity of this probability is unproved here. Replacing
it by uniform marginals, a bound on expected occupancies, or almost-embedding
would not finish the argument.

The signed result (4.6) is deliberately limited: it resums the **entire
removed configuration background**, not an asserted universal PSD estimate
or a new convergent local polymer expansion. No such estimates are assumed.

Thus the contribution is the second requested kind of outcome: a rigorous,
quantified theorem eliminating complete and uniformly dense low-complexity
collapsed phases, with an exact comparison to the actual injective count.
The full constant spectral benchmark remains open in this investigation.

---

## 9. Verification

Run

```
python3 Submission/check_cube_spectral_entropy.py
```

The saved output is `Submission/CubeSpectralEntropyVerification.txt`.
The checker verifies:

* the simultaneous thinning failure bound and the numerical suppression margin;
* exact finite-population and small-set encoding inequalities;
* 30,510 small pool/exception instances of the containing-box proof, including
  252 instances with a large pool;
* a non-complete `3/4`-dense example where enlargement preserves the required
  average density but **does not** preserve both minimum-degree conditions;
* clone/profile spectral lower bounds and the symplectic matrix identity;
* positive collision-defect polynomials and full collision-Möbius cancellation;
* actual labelled counts in a 10-vertex graph with a planted `Q_3`:
  `hom = 848844`, removed star-phase homomorphisms `= 33580`, and
  `inj = 6192`, with the injective count exactly unchanged;
* explicit finite endpoint regimes for the reflection-template parameters.
  For example, `K=1`, `Lambda=7`, `C=3136`, `d=122`,
  `t=4*2^40`, `s=84` pass (6.2), using its stated upper bound for `B_s`.

These are checks of the proved formulas, not a computational proof of the
unresolved embedding statement. Spectral numerical checks have tolerance;
the proofs use exact operator inequalities.

`Submission/Spec.lean` retains SHA-256

```
9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b
```
