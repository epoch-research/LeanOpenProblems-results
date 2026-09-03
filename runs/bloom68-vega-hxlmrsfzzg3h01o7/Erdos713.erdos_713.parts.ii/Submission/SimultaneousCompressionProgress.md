# Simultaneous identifications and the missing multi-split repairs

This is supporting work, **not a proof or disproof of Erdos 713**. Spec is
unchanged. Except for the finite results listed in section 6, these arguments
have been checked mathematically but are not yet formalized in Lean.

## 1. Exact simultaneous repair

Let pi partition the vertices into singletons and k doubletons. Let L_pi be
the native loss, and tau_pi the minimum number of old edges whose deletion
makes the simultaneous quotient H-free. At a globally priced exact extremizer,

    tau_pi + L_pi >= p(n)-p(n-k),
    tau_pi + L_pi >= e(G)-ex(n-k,H).

The second inequality compares exact extremal numbers at different orders;
it does not differentiate their increments.

The repair hyperedges are actual simultaneous vertex-splits of H. Several
H-vertices may split between their corresponding doubleton classes; distinct
H-vertices use distinct classes. These are injective lifts of ordinary
copies. Every witness has e(H) old edges. The integral transversal number
is exactly tau_pi, and a maximal edge-disjoint packing has at least
tau_pi/e(H) members.

This hypergraph is NOT the union of the individual-pair repair hypergraphs.
For example, contract two disjoint edges of C_(2r+2). Each single quotient
is C_(2r)-free, but their simultaneous quotient is C_(2r).

## 2. Native loss for OLD-edge matchings

If G is C_(2r)-free and M is an old-edge matching of size k, then

    L_M(G) <= sum_{uv in M} [1+codeg(u,v)] + (r-2)k/2.

Make an auxiliary graph B on the matched pairs. Join two pairs when the old
edges between their fibers contain two disjoint edges. A path on r vertices
in B supplies two disjoint tracks through r matched pairs; close them with
the matching edges in the two endpoint pairs to obtain an ordinary C_(2r).
Thus B is P_r-free, so Erdos--Gallai gives e(B)<=(r-2)k/2.

Account for the repeated quotient edges. Two incident old edges are charged
to the codegree of the other contracted pair. Between two doubleton classes,
two disjoint old edges lose one, charged to B; three old edges lose two,
covered by two codegree contributions; four lose three, covered by four
codegree contributions. Singleton-doubleton collisions are codegrees, and
the k contracted old edges are the loops. This proves the bound.

For C8 the extra term is k. Thus matching uniformly low-loss old edges
makes native loss negligible relative to k times the microscopic price.
The unresolved issue is repair, not hidden native collisions.

## 3. A leading-scale obstruction at actual priced extrema

Suppose H is two-connected and bipartite, ex(n,H)~c n^a, and 1<a<2. Let G
be a selected priced exact extremizer, and put e=e(G). Choose a balanced cut
A,B retaining at least e/2 edges, and let F=G[A,B].

Every identification of u in A with v in B is H-free in F. Otherwise a new
copy uses the merged vertex, corresponding to x in H. Since H-x is connected,
its copy in F has a consistent bipartite orientation. All neighbors of x
lie on the same side, so all incident edges at the merged vertex must lift
to the same endpoint, u or v. Then H was already present in F, a contradiction.

Hence D0=E(G) minus E(F), of size at most e/2, repairs every individual
opposite-side identification considered separately. It need not repair a
simultaneous quotient.

For even n=2m, m>=2, choose a uniformly random bijection A->B. Direct
collision counting gives

    E[L_pi(G)] <= e/m + (sum_v binom(d(v),2))/m
                    + 2 binom(e,2)/(m(m-1)),
    E[sum_{uv in pi} L_G(u,v)]
              <= [e + sum_v binom(d(v),2)]/m.

A loop has probability at most 1/m. Two incident edges collide through one
prescribed pairing, also with probability at most 1/m. Two disjoint edges
require one of two prescribed pairs of assignments, each with probability
1/(m(m-1)). The number of colliding edge pairs bounds the number of suppressed
parallel edges. For odd n, leave one vertex unpaired; O(n)=o(e) allowances
suffice and none of the asymptotic conclusions change.

The established hereditary tail gives

    sum_v d(v)^2 = O(n^2)        if a<3/2,
                  O(n^2 log n)  if a=3/2,
                  O(n^(2a-1))   if a>3/2.

Both expectations are therefore o(e) for every 1<a<2. Choose an actual
bijection for which their sum is o(e). Since n*mu~a*e, all but o(n) selected
pairs have individual loss o(mu), and hence growing single-split bundles.
Their individual minimum repair costs satisfy

    sum_i tau_i >= (a/2-o(1))e,

although the common repair D0 costs at most e/2. This is genuine integral
sharing, not fractional rounding.

The simultaneous quotient, however, has order n/2+O(1) and native loss o(e).
Consequently

    tau_pi(G) >= (1-2^(-a)-o(1))e.

Native loss cannot increase on a spanning subgraph. Thus even AFTER D0 has
been deleted, F needs at least

    tau_pi(F) >= (1/2-2^(-a)-o(1))e

additional old-edge deletions. All individual repair costs in F are zero.
The positive coefficient stays bounded away from zero throughout the C8
interval [6/5,5/4]. The omitted simultaneous obligations are leading-scale.

The global price alone gives the weaker additional coefficient

    3/2-2^(1-a)-a/2.

It is strictly concave in a, vanishes at 1 and 2, and is positive between
them. The full power asymptotic sharpens it to 1/2-2^(-a). These conclusions
are compatible with the rational C4 and C6 exponents; neither implies any
rationality condition.

The orientation argument requires H-x connected. It is not asserted for H
with cut vertices. Since it already applies to C8, any general-H proof using
shared single-pair repairs must nevertheless overcome this obstruction.

## 4. The missing C8 witnesses

In F, no opposite-side pair supports an open P8 split. Nevertheless the
simultaneous repair hypergraph has an edge-disjoint packing of at least

    ((1/2-2^(-a))/8-o(1))e

actual eight-old-edge witnesses. Each splits 2, 4, 6 or 8 vertices of C8.
Temporarily add the pairing edges: a lifted quotient C8 becomes a simple
C_(8+s), where s is the number of split vertices. The augmented graph is
bipartite, so s is even; s=0 is impossible because F is C8-free. These are
C10/C12/C14/C16 closures, not the C9 patterns from single old-edge contraction.
The temporary edges are only a proof device, not an asserted H-free competitor.

If a near-perfect OLD-edge matching has total individual loss o(e), choose
a balanced cut crossing its edges and retaining at least half of G. Random
independent orientations of the matched pairs prove such a cut exists. The
native-loss estimate in section 2 gives the same obstruction for that
matching. Existence of such a near-perfect good old-edge matching is NOT
established here.

## 5. Independent finite checks

`Submission/simultaneous_compression_checks.py` exhaustively checks all
six-vertex graph/old-matching cases satisfying each cycle prohibition:

- 96,019 C4-free graph/matching pairs;
- 382,825 C6-free pairs;
- 708,608 C8-free pairs.

All pass the native-loss bound. It also checks C6/C8/C10 with two disjoint
contracted edges: each single quotient is respectively C4/C6/C8-free, while
the simultaneous quotient is not. Log:
`/tmp/SimultaneousCompression.parent-tests.log`.

The parent independently checked the mathematical proofs and collision
probabilities. These finite tests are not substitutes for those proofs,
nor a numerical counterexample search for the original conjecture.

## 6. Lean scope and audit

`Submission/CompressionSubgraph.lean` imports the freshly rebuilt
`Submission.PricedExtremizers`, not Spec. It proves:

- monotonicity of the actual compression and of native loss;
- if F<=G and deleting D makes its quotient H-free, then
  `e(F)<=ex(|target|,H)+nativeLoss(G,pi)+|D|`;
- the doubled inequality when F retains at least half of G;
- a real retained-fraction/error version;
- the exact global-price comparison after any spanning-subgraph deletion.

The matching estimate, cut/bijection selection, multi-split descriptions and
asymptotic deductions above are not yet Lean theorems. Fresh strict builds
and the complete environment audit passed: all 9 declarations in
CompressionSubgraph and all 91 in PricedExtremizers, including generated and
private declarations, use only the three permitted axioms. No unsafe
declarations or Spec imports were found. Logs:

- `/tmp/CompressionSubgraph.strict.log`
- `/tmp/CompressionSubgraph.priced-build.log`
- `/tmp/CompressionSubgraph.build.log`
- `/tmp/CompressionSubgraph.audit.log`
- `/tmp/CompressionSubgraph.smoke.log`

Imported smoke tests also pass: identity compression has zero native loss,
collapse to a singleton loses exactly all old edges, the half-retention
inequality yields the expected real deficit, and the no-deletion case gives
the original quotient edge bound. Test source:
`/tmp/CompressionSubgraphSmoke.lean`.

CompressionSubgraph source SHA256:
`9125682ddb0e443ede957b4ef36401a5ce3d471c2eaf47c5b5e83c59792131fb`.

## 7. Remaining gap

Shared single-pair repair does not control simultaneous multi-split witnesses.
A proof using simultaneous contraction needs a new, genuinely leading-scale
control of those witnesses. The present obstruction does not exclude every
possible contraction scheme, and does not prove or disprove Erdos 713. No
rationality-producing equality or actual irrational-exponent counterexample
has been obtained.
