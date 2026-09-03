# Globally priced exact extrema: results and remaining gap

These are supporting results, **not a proof or disproof of
`Erdos713.erdos_713.parts.ii`**. The target file remains unchanged with both
admissions. The mathematical deductions below are not Lean theorems unless
explicitly identified as part of `PricedExtremizers.lean`.

## 1. Audited Lean module

`Submission/PricedExtremizers.lean` has 643 lines, namespace
`Erdos713Priced`, and sole import `FormalConjecturesUtil`. Its SHA256 is
`eefcd9ab9ba48f8ff5e5d4eef191486e5aec62f5be2590815cebb1c3a5a6fca4`.
The parent read every source line, strict-compiled the module, rebuilt its
olean and ilean, and reran the 44-public-declaration axiom audit and imported
smoke tests. All passed with only `propext`, `Classical.choice`, and
`Quot.sound`. Logs:

- `/tmp/PricedExtremizers.parent-strict.log`
- `/tmp/PricedExtremizers.parent-build.log`
- `/tmp/PricedExtremizers.parent-audit.log`
- `/tmp/PricedExtremizers.parent-smoke.log`

For an ordinary forbidden graph H, `IsPricedExtremal H G p` states that G is
H-free and every finite H-free competitor J satisfies

    e(J) - e(G) <= p(v(J)) - p(v(G)).

The comparison works for arbitrary finite vertex types. Such a G is an
exact extremizer at its own order. Existence is proved whenever
`ex(n,H) - p(n)` tends to minus infinity and H has an edge.

For `f(n) ~ c n^a`, `1<a`, `c>0`, the price

    powerPrice a c ell n = 2c n^a - ell n

is coercive for every real ell. The module constructs globally priced exact
extrema whose orders are monotone in ell and tend to infinity. It also
proves existence and exact backward differences for quadratic penalties.

The compression is an actual ordinary graph: map the edges under a vertex
map, remove loops, and merge repeated edge images. It is not a fractional
or homomorphism-only surrogate. For identifying distinct u,v, its exact
native edge loss is

    L_G(u,v) = 1_{uv in E(G)} + |N_G(u) intersection N_G(v)|.

If deleting a set D of old edges makes the compressed graph H-free, the
module proves

    p(n) - p(n-1) <= L_G(u,v) + |D|,

including an integral/natural-ceiling version. Smoke tests cover K2, K3,
empty graphs, collapse to a singleton, and extraction of an integral repair
lower bound. The rooted-copy interpretations below are not yet formalized.

## 2. Correct microscopic prices without differentiating ex-increments

Let f(n)=ex(n,H) and suppose f(n)~c n^a, where c>0 and 1<a<2.
There is a simpler localization argument than the varying-quadratic-penalty
construction recorded in the earlier handoff.

For each positive integer N, set

    p_N(j) = 2c j^a - a c N^(a-1) j,

and select any maximizer n_N of f(j)-p_N(j). Coercivity, and hence existence
of this maximizer and of a corresponding globally priced exact graph, is
already formalized. The following localization argument is mathematical,
not yet Lean code.

Define

    eta_N = sup_{j >= 0} |f(j)-c j^a| / [c (N+j)^a].

The supremum is finite and eta_N tends to zero. Indeed, the large-j part is
uniformly small by the given equivalence; the finitely many remaining
numerators are fixed while their denominators tend to infinity.

Write x=n_N/N. Comparing the score at n_N with the score at N gives

    g(x) := x^a - a x + a - 1
       <= eta_N [(1+x)^a + 2^a].

Strict convexity gives g(x)>=0 for x>=0, with equality only at x=1.
For every delta>0, the ratio

    g(x) / [(1+x)^a + 2^a]

has a positive infimum over x>=0, |x-1|>=delta: it is continuous and
strictly positive there, and tends to 1 as x tends to infinity. Therefore
n_N/N tends to 1. In particular n_N tends to infinity.

The explicit backward price is

    mu_N = p_N(n_N) - p_N(n_N-1)
         = 2c [n_N^a-(n_N-1)^a] - a c N^(a-1)
         ~ a c n_N^(a-1).

This differentiates the explicit power price, not the extremal function.
The latter differentiation is invalid even for C4, as documented in the
earlier notes. Every finite ordinary H-free J still satisfies the exact
priced comparison. In particular, deletion of any vertex from G_N shows
that its degree is at least mu_N, without trimming G_N or sacrificing its
exact extremality.

An alternative valid selection uses

    c j^a + c kappa_N N^(a-2)(j-N)^2,
    kappa_N = sqrt(eta_N + 1/N).

The maximizing order then satisfies

    kappa_N (x-1)^2 <= eta_N [(1+x)^a + 2^a].

Since a<2, the right-hand bracket divided by (x-1)^2 is bounded away from
x=1, proving the same localization and backward-price asymptotic. Only the
coercivity, existence, exact displacement inequality, and exact backward
difference for this alternative are in the current Lean module.

## 3. Actual integral rooted split witnesses

In an H-free graph G, identifying u!=v creates H if and only if G contains
an open vertex-split of H rooted at u,v. The split replaces one vertex of H
by two roots and partitions its incident edges into two nonempty sets.
The pattern prescribes no edge between the roots; since copies are ordinary
non-induced copies, the host roots may nevertheless be adjacent.

To see the equivalence, lift a copy in the quotient edge by edge. It must
use the identified vertex, since otherwise it was already a copy in G.
Its incident edges cannot all lift to one root, for the same reason. In the
other direction, identify the two roots of a split copy. All other vertices
remain distinct, producing an ordinary copy of H.

This remains valid after any old-edge deletions. Thus the minimum number
tau of old edges whose deletion repairs the quotient is the integral
transversal number of the hypergraph of all actual rooted split copies.
For a globally priced G of order n, writing mu=p(n)-p(n-1),

    tau + L_G(u,v) >= mu.

Each witness has exactly e(H) edges. The union of a maximal edge-disjoint
packing is a transversal, so the packing has at least

    (mu-L_G(u,v)) / e(H)

members whenever this quantity is positive. This is an integral argument;
it does not invoke the false fractional-repair rounding principle.
If uv is an old edge, adding it to each split copy gives closed split
copies edge-disjoint off their common root edge. They need not be
vertex-disjoint off the roots.

## 4. Almost every old edge has a growing split bundle

The previously established hereditary degree-tail estimate, for decreasing
degrees, is

    d_i <= 8 C n i^(a-2),

with the large-i case following from the average degree. Since
`a(2-a)<1`, it gives

    sum_v d(v)^a = O(n^(1+a(a-1))).

For H-free G, every neighborhood-induced graph is H-free. Therefore

    sum_{uv in E(G)} codeg(u,v)
      = sum_v e(G[N(v)])
      <= C sum_v d(v)^a.

At the selected exact extrema, e(G)~c n^a and mu~a c n^(a-1).
The preceding bound is o(e(G)mu), with exponent gap
`(a-1)(2-a)>0`. Consequently all but o(e(G)) old edges have
`L_G(u,v)=o(mu)` (with a suitable vanishing threshold), and support
Omega(n^(a-1)) rooted closed split copies edge-disjoint off the root edge.
This deduction has not yet been formalized in Lean.

## 5. C8: many robust P8s and C9s

For H=C8, an open vertex-split is a simple eight-edge path between the
roots. An old root edge closes it to C9. In any C8-free G, G[N(w)] contains
no seven-vertex path. The Erdos--Gallai path bound yields

    e(G[N(w)]) <= (5/2) d(w),
    sum_{uv in E(G)} codeg(u,v) <= 5 e(G),
    sum_{uv in E(G)} L_G(u,v) <= 6 e(G).

Thus all but at most `12 e(G)/mu = O(n)` old edges have at least mu/16
edge-disjoint P8s between their endpoints. Summing the packing bound over
root edges and dividing by the nine possible root edges of a C9 gives

    #C9(G_N) >= e(G_N)(mu_N-6)/72
             ~ a c^2 n_N^(2a-1)/72

in the sense that the explicit lower-bound expression has that asymptotic.
This does not assert asymptotic equality for the actual C9 count.

Nikiforov's C8-free degree-square bound

    sum_v d(v)^2 <= 6 e(G) + 3n(n-1)

is stated in `/corpus/src/0903.5352/0903.5352.tex`, theorem `th1`,
lines 109--159. Summing codegrees over all unordered vertex pairs then
shows that all but O(n^(3-a)) pairs have analogous robust P8 bundles at
these priced extrema. Neither the edge nor the all-pairs conclusion
currently implies rationality of a.

## 6. A legal integral improvement of twin-saturated examples

Let F=(A,B) be D-regular with |A|=|B|=M and girth greater than 8. Replace
each a in A by three twins and add a triangle inside each triple. Call the
result U+. It has

    v(U+) = 4M,       e(U+) = 3MD + 3M.

It contains neither C8 nor C9. Indeed, projecting a cycle of length at most
9 to F gives a closed walk whose support is a tree: F is bipartite and has
no cycle of length at most 8. The corresponding expanded tree consists of
blocks `K3 join an independent set`, glued at individual B-vertices.
Every simple cycle lies in one such block, whose circumference is at most 6.

Choose b0 in B. For each a in N_F(b0), set

    S_a = N_F(a) minus {b0}.

These D sets are disjoint and each has size D-1. Delete all old edges at
the selected A-triples, including their triangles, costing `3D^2+3D`.
Inside each S_a insert an arbitrary C8-free graph R_a, using only B-vertices.
This remains C8-free:

* A remaining old path between two distinct vertices of the same S_a has
  length at least 8. A shorter path, projected into F and combined with
  the two-edge path through the deleted a, would yield a cycle of length
  at most 8 in F.
* Between distinct sets S_a,S_b, such a path has length at least 6, using
  the analogous four-edge path through a,b0,b. Possible intersections
  with b0 only produce an even shorter forbidden base cycle.
* A mixed cycle with one run of new edges has an old segment of length
  at least 8. One with at least two runs has at least two old segments of
  length at least 6. Neither can be C8. Entirely new cycles lie within an
  R_a and are excluded by its choice.

Taking R_a extremal gives the exact same-order gain

    D ex(D-1,C8) - 3D^2 - 3D.

Under the power-law hypothesis with a>1, this is asymptotic to c D^(a+1)
and is positive for large D. A single-fiber version can include its three
now-isolated vertices in the replacement and gains
`ex(D+3,C8)-3D-3`.

Therefore these examples are not exactly globally extremal, even after
all intrafiber clique edges have been inserted. This corrects the earlier
local-saturation obstruction, but does not eliminate its near-extremal
version. In the C8-relevant scaling D of order n^(a-1), the D-fiber gain is
of order n^(a^2-1). The known range a<=5/4 makes this subleading relative
to n^a. No leading-scale improvement or sharp exponent comparison follows.

## 7. The unresolved requirement

The original goal is rationality for every finite ordinary bipartite H
whenever a positive pure-power asymptotic exists. None of the verified
pricing, integral repair, split-bundle, or replacement facts supplies a
rationality-producing equality. In particular, there is still no exclusion
of a hypothetical irrational C8 exponent between 6/5 and 5/4. A leading-scale
integral comparison, or some other genuinely new H-specific argument, is
needed. No proof may be integrated into Spec on the basis of these partial
results, and no proof/disproof claim has been submitted.


## 8. Subsequent simultaneous-compression investigation

`Submission/SimultaneousCompressionProgress.md` records a new native-loss
estimate for old-edge matchings, and a leading-order obstruction to sharing
only single-pair repairs. The obstruction occurs at actual priced extrema
for two-connected bipartite H. Supporting finite graph comparisons are
formalized in `Submission/CompressionSubgraph.lean`; its complete axiom audit
also covers all 91 declarations of PricedExtremizers, including generated and
private ones. These results still do not settle the rationality conjecture.