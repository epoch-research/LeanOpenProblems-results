# Erdős 371: linear cofactor irreversibility and an all-X potential obstruction

## Outcome and precise scope

**Erdős 371 remains open in this work.** No estimate `S(X)=o(X)` is claimed. No Lean file was changed or used as a mathematical premise; in particular the admitted statements in `Spec.lean` were not used.

This attempt tests two stronger mechanisms for proving a vertex-count discrepancy bound, and obtains rigorous obstructions to both:

1. **Opposite-edge cancellation does not leave a small remainder.** In the actual cofactor graph, let
   
   `L_Q(X) = sum_{a<b} |C_X(a,b)-C_X(b,a)|`.
   
   There is a constant `c>0` such that `L_Q(X)>=cX` for every sufficiently large X. The number `V(X+1)` of cofactor vertices satisfies
   
   `V(X+1) (log X)^K = o(X)` for every fixed K.
   
   Thus a bound `L_Q(X)=O(V(X+1)(log X)^K+pi(X))` is false for every fixed K. This is a statement about the **actual arithmetic graph**, not an arbitrary Eulerian countermodel. The positive lower bound uses the established two-point stable-set theorem of Hildebrand, explicitly identified below; it does not assume prime-pair independence.
2. **A full-factor additive potential cannot approximate the signed current with small absolute error.** For every completely additive real function F, including arbitrary X-dependent prime weights, and `M=floor((X-1)/2)`,
   
   `sum_{3<=n<=X} |s(n)+F(Q(n+1))-F(Q(n))| >= (M-2)/2 = X/4-O(1)`.
   
   The same lower bound holds for approximation of `s(n)` by an **arbitrary potential on the prime vertices**. This result is elementary and uses the exact identity `P(2n)=P(n)`, not a probabilistic or limiting assertion.
3. Both obstructions survive deletion of `o(X)` actual edges. The irreversible cofactor edges can be supplied in a fixed interior prime band below the square-root scale. They are not merely an artifact of bounded-multiplicity primes near X.
4. After removing the `O(log X)` LPF-2 incidences and canceling every opposite cofactor-edge pair, `Omega(X)` genuine edges still lie in directed even cycles of length at least four. An `o(X)` simple-path remainder can be proved; the remaining cycles cannot simply be discarded by absolute value.

These conclusions **do not disprove** a signed bound such as `|S(X)|=O(V(X+1))`. In fact such a bound would solve the problem. What is disproved is the proposed route through an absolute pairwise remainder, or through an L1-small linear potential error. Cancellation between different cofactor pairs or between different cycles is still possible and is exactly what these methods have not controlled.

## 1. Exact graph and vertex normalization

Use

\[
 P(1)=1,\quad Q(n)=n/P(n),\quad
 s(n)=\operatorname{sgn}(P(n+1)-P(n)).
\]

For `n>=3`, write

\[
 n=ap,\qquad n+1=bq,\qquad
 p=P(n),\ q=P(n+1).
\]

Full max-multiplicativity gives the **exact**, not optional, conditions

\[
 P(a)\le p,\qquad P(b)\le q,\qquad bq-ap=1.                 \tag{1}
\]

Also `(a,b)=1`, `a!=b`, and

\[
 s(n)=-\operatorname{sgn}(b-a).                            \tag{2}
\]

For example, if `a<b` and `p<=q`, then
`bq-ap=(b-a)q+a(q-p)>=2`, a contradiction; the other case follows in the same way. Equality `a=b` forces `a=1,q-p=1`, whose only prime-to-prime occurrence is `n=2`.

Set

\[
 C_X(a,b)=\#\{3\le n\le X:Q(n)=a,
                                  Q(n+1)=b\}.
\]

There are no loops. Consequently

\[
 S(X)=2-\sum_{a<b}(C_X(a,b)-C_X(b,a))\quad(X\ge2).         \tag{3}
\]

Cancel `min(C_X(a,b),C_X(b,a))` pairs of opposite edges for every unordered pair. The number of remaining edge occurrences is exactly

\[
 L_Q(X)=\sum_{a<b}|C_X(a,b)-C_X(b,a)|
       =X-2-2\sum_{a<b}\min(C_X(a,b),C_X(b,a)).            \tag{4}
\]

Thus `|S(X)-2|<=L_Q(X)` is valid, but, as proved below, cannot give a saving.

### Vertex count, with a quantitative improvement

For `H>=1`, the vertex set on positions `1,...,H` is exactly

\[
 \mathcal V(H)=\{a\ge1:aP(a)\le H\}.                       \tag{5}
\]

Necessity follows from (1). Conversely, for `a>=2` use `n=aP(a)` and
`P(aP(a))=P(a)`; vertex 1 occurs at `n=1`. In particular repeated largest prime factors have not been accidentally excluded. For a vertex `a>=2` its exact multiplicity is

\[
 m_H(a)=\pi(H/a)-\pi(P(a)-1).                             \tag{6}
\]

For `a>=2` outside the vertex set the multiplicity is zero.

Here and below `pi` of a real argument means the number of primes not exceeding that argument.

For any `2<=y<=H`, splitting (5) at `a=H/y` gives

\[
 V(H):=|\mathcal V(H)|\le H/y+\Psi(H,y),                  \tag{7}
\]

where `Psi(H,y)` counts y-smooth positive integers up to H. For fixed `0<sigma<1`, Rankin's elementary bound is

\[
 \Psi(H,y)\le H^\sigma
       \prod_{p\le y}(1-p^{-\sigma})^{-1}
       \le H^\sigma\exp(C_\sigma y^{1-\sigma}).           \tag{8}
\]

For the second inequality, bound `-log(1-p^{-sigma})` by a constant times `p^{-sigma}`, and bound the sum over primes by the sum over all integers. No prime distribution theorem is needed here.

Given fixed `K>=0`, take

\[
 y=(\log H)^{K+2},\qquad
 \sigma=1-\frac{1}{2(K+2)}.
\]

Equations (7)-(8) give

\[
 V(H)\le\frac{H}{(\log H)^{K+2}}
       +H^\sigma\exp(C_\sigma\sqrt{\log H}),
 \qquad V(H)(\log H)^K=o(H).                             \tag{9}
\]

The small number of vertices is therefore genuinely available, with more than an arbitrary fixed logarithmic saving. The obstruction is not a weak vertex estimate.

## 2. A purely arithmetic certificate of irreversibility

Suppose an edge `a->b` occurs at n. Any other occurrence in the same direction, at m, satisfies

\[
 m-n\equiv0\pmod a,\qquad m-n\equiv0\pmod b.
\]

Any occurrence in the opposite direction satisfies

\[
 m+n+1\equiv0\pmod a,\qquad m+n+1\equiv0\pmod b.
\]

Since `(a,b)=1`, these become

\[
 ab\mid m-n \quad\hbox{(same direction)},\qquad
 ab\mid m+n+1 \quad\hbox{(opposite direction)}.            \tag{10}
\]

Define the actual edge set

\[
 I_X=\{3\le n\le X:Q(n)Q(n+1)>2X+1\}.                   \tag{11}
\]

**Lemma.** If `n in I_X` has vertices a,b, then

\[
 C_X(a,b)=1,\qquad C_X(b,a)=0.                            \tag{12}
\]

Indeed distinct same-direction indices differ by less than `ab`, and an opposite pair has `0<m+n+1<=2X+1<ab`, contradicting (10). Distinct members of `I_X` therefore give distinct unordered pairs, and

\[
                         L_Q(X)\ge |I_X|.                \tag{13}
\]

This conclusion does not discard cofactor smoothness or primality. It is a necessary divisor condition on genuine LPF edges, and rules out the opposite occurrence even before imposing those additional conditions.

## 3. There are linearly many irreversible cofactor edges, for all large X

Here the only non-elementary input for the cofactor lower bound is specified explicitly.

### Established input: Hildebrand's two-point stable-set theorem

A set A is stable if, for every fixed prime r,

\[
 \#\{n\le H:1_A(rn)\ne1_A(n)\}=o(H).
\]

**Hildebrand's theorem:** if A is stable and has positive lower natural density, then

\[
                 d_-(A\cap(A-1))>0.                     \tag{14}
\]

This is the proved **two-point** theorem, not the open higher-order stable-sets conjecture. A precise accessible source is Tao--Teräväinen, *Value patterns of multiplicative functions and related sequences*, Forum Math. Sigma 7 (2019), e33, arXiv:1904.05096, Section 1.3, immediately preceding the higher-order stable-sets conjecture. The local source `/corpus/src/1904.05096/main.tex`, lines 152-174, states the definition, the prime-factor-band examples, and the proved two-point conclusion.

The band conclusion needed here is also explicitly stated, in a more general form, as the theorem labelled `theo_hildebrand` in J. Teräväinen, *On binary correlations of multiplicative functions*, Forum Math. Sigma 6 (2018), e10, arXiv:1710.01195; local source lines 175-184. It states **positive lower natural density**, not just logarithmic density.

For completeness, fix

\[
                         0<\alpha<\beta<1/2
\]

and use

\[
 A=\{m:m^\alpha<P(m)<m^\beta\}.
\]

Dickman's one-variable theorem gives the positive density
`rho(1/beta)-rho(1/alpha)`. For every fixed r, `P(rm)=P(m)` once `P(m)>=r`; membership can then change only in shrinking exponent neighborhoods of alpha or beta. The continuous one-variable Dickman distribution shows that these exceptional sets have density zero. Thus A is stable and (14) applies. This uses full max-multiplicativity to verify stability, but uses the **proved two-point theorem**, not a naive inference from stability to reflection symmetry.

### Applying the theorem without an invalid density upgrade

Put

\[
 B=\{n:n\in A,\ n+1\in A\}.
\]

By (14), choose `d>0` such that, for all sufficiently large H,

\[
                         |B\cap[1,H]|\ge dH.
\]

Set `eta=d/2`. The elementary deletion of an initial segment gives

\[
 |B\cap[\lceil\eta X\rceil,X]|
                  \ge (d/2)X-O(1).                      \tag{15}
\]

For every n in this set,

\[
 Q(n)Q(n+1)
    >n^{1-\beta}(n+1)^{1-\beta}
    \ge (\eta X)^{2(1-\beta)}.
\]

Because `2(1-beta)>1`, this exceeds `2X+1` for every sufficiently large X. Hence, for some fixed `c>0`,

\[
                 |I_X|\ge cX,\qquad L_Q(X)\ge cX         \tag{16}
\]

for **all** sufficiently large X. This is not a logarithmic-to-natural-density conversion: positive lower natural density is an explicit input to (15).

Together with (9) and `pi(X)=o(X)`, (16) disproves, for every fixed K,

\[
           L_Q(X)=O\big(V(X+1)(\log X)^K+\pi(X)\big).      \tag{17}
\]

No numerical value of c is claimed. The elementary vertex and divisor portions are proved here; Hildebrand's theorem is a cited established input, not newly proved in this note.

### The obstruction is in a substantial interior core

Let `E_X=B intersect [ceil(eta X),X]`. Its endpoint primes lie between

\[
          (\eta X)^\alpha\quad\hbox{and}\quad(X+1)^\beta, \tag{18}
\]

and its cofactor vertices lie between

\[
          (\eta X)^{1-\beta}\quad\hbox{and}\quad
                         (X+1)^{1-\alpha}.              \tag{19}
\]

For example one can fix `alpha=1/4,beta=1/3`. All these edges are bipartite for large X, since both prime labels exceed 2. The graph on just these edges is simple even as an unordered graph, by (12), has at least cX edges, and has at most `(X+1)^(1-alpha)` vertices.

It also contains a polynomial-minimum-total-degree core: repeatedly remove vertices of current total degree less than

\[
                         k=\lfloor X^{\alpha/2}\rfloor.
\]

At most `(k-1)(X+1)^(1-alpha)=o(X)` edges are removed. What remains still has `Omega(X)` edges and minimum **undirected total degree** at least k. No assertion about minimum in-degree, minimum out-degree, expansion, or the signed current of that core is made.

The prime classes in (18) are not bounded-multiplicity prefix classes either. A prime p in that range has the p distinct occurrences `p,2p,...,p^2` with largest prime p, all below X for large X because `beta<1/2`.

## 4. Rare-prime deletion and actual longer cycles

### Deletion cost cannot eliminate irreversibility cheaply

For any set D of deleted edge indices, let `C_{X,D}` be the remaining cofactor counts. The edges in `I_X minus D` are still unique and have no reverse. Therefore

\[
 \sum_{a<b}|C_{X,D}(a,b)-C_{X,D}(b,a)|
                    \ge |I_X|-|D|.                      \tag{20}
\]

In particular any deletion of `o(X)` actual edges leaves a linear absolute remainder.

If a set R of prime labels is deleted together with all incident LPF edges, its edge deletion cost is at most

\[
 2\sum_{p\in R}\left\lfloor\frac{X+1}{p}\right\rfloor
                 \le2(X+1)\sum_{p\in R}\frac1p.          \tag{21}
\]

Thus prime sets of harmonic mass `o(1)` cannot fix the obstruction. Conversely any prime-label set covering all of `E_X` must have harmonic mass at least `c/2-o(1)`. A small *number* of primes is not automatically a small deletion cost; (21) identifies the relevant elementary weight.

Similarly, deleting all cofactor vertices with prefix multiplicity at most `M_X` costs at most `2M_X V(X+1)` edges. For every fixed power of log X as `M_X`, this is `o(X)` by (9), so it also leaves the obstruction intact.

These statements concern eliminating the pairwise absolute remainder. They do **not** say that an `o(X)` deletion cannot make some graph acyclic; breaking a cycle and deleting all its edges are different operations.

### The exact cycle remainder is large

An LPF equal to 2 occurs only at a power of 2. Remove all such incidences from the edge set `3<=n<=X`; at most

\[
                         d_X\le2\lfloor\log_2(X+1)\rfloor
\]

edges are removed. Every remaining cofactor edge joins opposite parities. Now cancel all opposite pairs, retaining actual integer-indexed edges with their original capacities.

The original cofactor word is a single path, so the positive part of its divergence has mass at most 1. Deleting `d_X` edges raises this mass by at most `d_X`; canceling directed two-cycles does not change divergence. Consequently the remaining integral flow decomposes into directed cycles and at most `d_X+1` simple directed paths. Each such path has at most `V(X+1)-1` edges. Its total path mass is therefore

\[
       \le(d_X+1)(V(X+1)-1)=o(X).                         \tag{22}
\]

One way to obtain this decomposition is to start a trail at a vertex of positive divergence, erase a directed simple cycle whenever a vertex repeats, and finish at a negative-divergence vertex. Each nonempty residual path reduces the positive divergence by one. After the boundary is exhausted, the remaining balanced flow decomposes into cycles. All used edges are genuine and used at most once.

By (16), at least `cX-o(X)` irreversible edges survive on these cycles. No two-cycle remains; bipartiteness excludes odd cycles. Thus the retained directed cycles all have even length at least four, and a linear total edge mass must still be treated. There are at least `(cX-o(X))/V(X+1)` edge-disjoint cycles in such a decomposition.

**Crucial limitation:** these cycles need not each have nonzero ordering current. Even nonzero currents of different cycles can cancel. Equation (22) proves an `o(X)` boundary error, not an `o(X)` cycle current.

## 5. An elementary signed-potential obstruction: X/4-O(1)

The preceding result concerned opposite-edge cancellation. The following result addresses a different plausible exact-combinatorial route: replace the ordering statistic by a vertex potential, or by a linear functional of the complete cofactor factor inventory.

### A unit defect on every exact dyadic triangle

For `n>=2`, put

\[
 A=P(n),\qquad B=P(n+1),\qquad C=P(2n+1).
\]

These are pairwise distinct: the corresponding integers are pairwise coprime. Full max-multiplicativity gives

\[
 P(2n)=A,\qquad P(2n+2)=B.
\]

For three distinct real labels, the two-edge comparison from A through C to B is either zero or twice the direct comparison. Hence

\[
 \Delta_n:=s(2n)+s(2n+1)-s(n)\in\{-1,+1\}.               \tag{23}
\]

As a signed chain in the prime graph, `e_{2n}+e_{2n+1}-e_n` has zero boundary and unit absolute ordering current. This is a mixed-orientation cycle certificate; it is not being called an all-forward prime triangle.

### Arbitrary potentials on prime vertices

For any real function h on the primes, even depending arbitrarily on X, set

\[
 u(n)=h(P(n+1))-h(P(n)).
\]

The two edges at `2n,2n+1` telescope, so

\[
                   u(2n)+u(2n+1)-u(n)=0.                \tag{24}
\]

Let `e(n)=s(n)-u(n)` and `M=floor((X-1)/2)`. For `3<=n<=M`, (23)-(24) give

\[
                 1\le |e(n)|+|e(2n)|+|e(2n+1)|.
\]

Every edge index occurs in at most two of these triples: once as a parent and once as a child. Summing proves the all-X bound

\[
 \boxed{\quad
 \sum_{n=3}^X|s(n)-h(P(n+1))+h(P(n))|
          \ge\frac{M-2}{2}=\frac X4-O(1).
 \quad}                                                  \tag{25}
\]

### Completely additive potentials on the integer cofactors

Let F be any real completely additive function,

\[
 F(m)=\sum_\ell \lambda_\ell v_\ell(m),
\]

with entirely arbitrary prime weights. More generally the proof works whenever `F(2a)-F(a)` is independent of a on the needed range. Since `Q(2m)=2Q(m)` for `m>=2`,

\[
 v(n):=F(Q(n+1))-F(Q(n))
 \quad\Longrightarrow\quad v(2n)+v(2n+1)-v(n)=0.          \tag{26}
\]

Applying the same argument to `e(n)=s(n)+v(n)` gives

\[
 \boxed{\quad
 \sum_{n=3}^X|s(n)+F(Q(n+1))-F(Q(n))|
                         \ge\frac{M-2}{2}.
 \quad}                                                  \tag{27}
\]

By (2), this is exactly the L1 error in approximating the cofactor ordering current by the gradient of F. It covers **all linear functionals of the complete prime-valuation vector**, not only logarithmic mass. The weights can be chosen after seeing the entire prefix; the bound is uniform over them.

There is no claim here about an unrestricted, non-additive potential on the integer cofactor vertices. Such a potential need not obey (26).

### The potential obstruction also survives rare deletions

If D edge indices are deleted, at most `2|D|` of the dyadic triangles are lost. Summing only over intact triangles gives, for either potential class,

\[
 \sum_{\substack{3\le n\le X\\n\notin D}}|e(n)|
           \ge\frac{(M-2-2|D|)_+}{2}.                   \tag{28}
\]

Thus `o(X)` deletions cannot make either potential representation have `o(X)` absolute error. This is a positive-mass strengthening of the observation that one exceptional cycle can have nonzero current and zero inventory defect.

Equations (25)-(28) do not exclude a representation with a large but signed-canceling error. They specifically rule out an L1-small error as the way to justify discarding that term.

## 6. A prime-graph comparison needing only one-point prime estimates

For context, the corresponding absolute obstruction at the **prime-vertex** level has an explicit constant and does not require Hildebrand's theorem.

Let `D_X(p,q)` count the actual prime edges for `2<=n<=X`, and let

\[
 L_P(X)=\sum_{p<q}|D_X(p,q)-D_X(q,p)|.
\]

Equation (10) applies with p,q in place of a,b. Thus any edge with
`p q>2X+1` is unique and has no reverse in the prefix. Set `y=sqrt(2X+1)`. Each integer at most X has at most one prime factor greater than y, so prime Mertens and Chebyshev give

\[
 \#\{m\le X:P(m)>y\}
   =\sum_{y<p\le X}\lfloor X/p\rfloor
   =X\log2+O(X/\log X).
\]

The two endpoint marginals differ by at most an endpoint. Inclusion-exclusion, not independence, then gives

\[
 \#\{n\le X:P(n)>y,\ P(n+1)>y\}
       \ge(2\log2-1)X-O(X/\log X).
\]

All these edges satisfy `pq>2X+1`. Consequently

\[
       L_P(X)\ge(2\log2-1-o(1))X,
       \qquad 2\log2-1=0.386294\ldots.                   \tag{29}
\]

This directly rules out an `O(pi(X))` absolute reverse-pair remainder at the prime-graph level. It says nothing about individual signed prime-insertion costs or their aggregate variation; those are different quantities.

## 7. A fully irreversible biased four-cycle

For `X=1,000,000`, the actual cofactor graph contains

\[
           331\longrightarrow6426\longrightarrow7733
              \longrightarrow13818\longrightarrow331.
\]

The exact equations and endpoint largest primes are:

| n | n = a p | n+1 = b q | (p,q) |
|---:|---:|---:|---:|
| 186353 | 331 * 563 | 6426 * 29 | (563,29) |
| 456246 | 6426 * 71 | 7733 * 59 | (71,59) |
| 842897 | 7733 * 109 | 13818 * 61 | (109,61) |
| 925806 | 13818 * 67 | 331 * 2797 | (67,2797) |

The four adjacent cofactor products are

```
2,127,006; 49,692,258; 106,854,594; 4,573,758.
```

Each exceeds `2X+1`. Hence **none of its edges has any reverse anywhere in the full prefix**, by (10), not merely within this selected cycle. All endpoint LPFs exceed 2. Its cofactor ordering current is `+2` and its original LPF ordering current is `-2`.

This is a literal finite certificate, not an asserted infinite family of such biased four-cycles. The asymptotic theorem (16) proves linear irreversible mass; it does not assert linear mass in individually biased four-cycles.

## 8. Verification and remaining issue

`CofactorIrreversibilityVerification.py` independently checks the finite claims using integer arithmetic and a largest-prime-factor sieve. It does not import a Lean target. The recorded output is `CofactorIrreversibilityVerification.log`.

Checks include:

* 999,998 sign-reversal, coprimality, full-LPF admissibility, and parity checks;
* 33,806 exact max-multiplicativity checks and eight complete vertex/multiplicity comparisons;
* 49,997 dyadic unit defects, two classes of integer-weighted potentials, and deletion-robust incidence bounds;
* both congruences (10), uniqueness and absence of reverse edges, and the exact cancellation normalization (4);
* actual edge-disjoint cycle decompositions after deletion of LPF-2 incidences and all opposite pairs;
* prime-label deletion covers and undirected degree-pruning bounds;
* the fully irreversible biased four-cycle above.

Selected finite data are:

| X | cofactor vertices | `L_Q(X)` | `|I_X|` | signed LPF current on `I_X` |
|---:|---:|---:|---:|---:|
| 1,000 | 88 | 354 | 33 | 3 |
| 10,000 | 403 | 3,630 | 431 | 5 |
| 100,000 | 1,894 | 36,966 | 5,513 | 3 |
| 1,000,000 | 9,108 | 367,422 | 67,420 | 72 |

The last two columns illustrate why irreversible mass is **not** a lower bound for the signed bias. At `X=100,000`, after opposite cancellation and LPF-2 removal, a genuine decomposition has 36,866 cycle edges in 2,593 cycles and just 84 edges on ten residual paths. Of the irreversible edges, 5,507 lie on these cycles.

Finite computations verify the algebra and certificates, not (14), (16), or a density asymptotic. The all-X conclusions rest on the proofs and the specifically cited established theorem.

### What a surviving approach must do

A successful cofactor argument must retain signed cancellation **between different unordered cofactor pairs**, or use a genuinely nonlinear, incidence-sensitive treatment of the longer cycles. It cannot conclude by:

* discarding the unmatched opposite-edge remainder as `O(number of vertices)`;
* removing an `o(X)` edge mass and then claiming pairwise symmetry;
* replacing the current by a prime-vertex potential or a linear complete-factor-inventory potential with `o(X)` total absolute error.

These are rigorous obstructions to specified intermediate claims, not a proof or disproof of Erdős 371. No signed recurrence with contraction and no natural-density cancellation estimate was obtained.

`Submission/Spec.lean` retained SHA-256
`d48bb112dcd4fd5c98dae80077b7384df62a14ef9a919fe7d476b9c5ace427bb`.
