# Stable adjacency does not yet yield rational extremal exponents

This is a mathematically checked investigation, not a Lean proof or disproof
of Erdos 713. `Submission/Spec.lean` remains unchanged. No assertion below
identifies a known counting class with arbitrary extremal H-free graphs.

## 1. The valid local stability consequence

If H has bipartition sizes s,t, every H-free graph is K_(s,t)-free. A
half-graph of length s+t, with E(a_i,b_j) iff i<j, contains a K_(s,t)
rectangle using its first s left vertices and last t right vertices.
Irreflexivity ensures the two sides of this rectangle cannot overlap.
Thus adjacency has uniformly bounded ladder index.

Malliaris--Pillay, `1504.06288/1504.06288.tex`, Theorem 1.1 (lines 9--33),
is genuinely applicable to a stable relation in an arbitrary ambient theory.
It does not require or conclude a stable complete ambient theory. The
quantitative finite stable regularity lemma is stated in Malliaris--Shelah,
`2012.09794/2012.09794.tex`, theorem `t:sr` (lines 61--75): an equitable
partition, all pairs epsilon-regular, each density below epsilon or above
1-epsilon, with fewer than `(4/epsilon)^(2^(k+3)-7)` pieces.

This does not supply the necessary counting scale. If e(G)=O(n^a), a<2,
sets of size at least epsilon*n have density O(n^(a-2)/epsilon^2)=o(1)
for fixed epsilon. The O(epsilon*n^2) error can contain all edges. Resolving
the leading edge count needs epsilon=o(n^(a-2)); the partition bound then
grows with n and gives no fixed finite counting profile.

Stable arithmetic regularity is not an automatic strengthening here:
Conant--Pillay--Terry, `1710.06309/1710.06309.tex`, theorems `thm:main`,
`thm:structure`, and `main-lemma`, require a finite group and an appropriate
stable translation-invariant relation. No such structure has been derived
from H-freeness or global pricing.

## 2. Exact C4 extrema can have unstable quantified structure

For odd prime powers q>=15, the orthogonal polarity graph ER_q has vertices
[x] in PG(2,q), and distinct [x],[y] are adjacent iff x dot y=0. It has

    n=q^2+q+1,   e=q(q+1)^2/2=ex(n,C4),   degrees in {q,q+1}.

Furedi's exact extremality theorem is stated in Tait--Timmons,
`1403.4489/1403.4489.tex`, lines 28--38. The looped incidence matrix satisfies
A^2=J+qI; see `1502.02722/1502.02722.tex`, lemma
`eigenvalues of polarity graph`, lines 71--81. In particular these examples
have no low-degree subdivision vertices and are asymptotically regular.

In the ordinary loopless graph, the formula

    Abs(x) := x belongs to no triangle

defines exactly the absolute points x dot x=0. For an absolute point x,
the restriction of the bilinear form to x-perp has radical x and rank one;
two other points there cannot be orthogonal. For a nonabsolute point,
x-perp is a nondegenerate two-dimensional space. Choose a nonisotropic
direction and its distinct perpendicular direction, producing a triangle
through x. Such a direction exists for odd q.

Hence `E(x,y) or (x=y and Abs(x))` recovers projective point-line incidence,
with y indexing y-perp. After naming a projective frame, the usual finite
join/intersection constructions uniformly interpret the coordinate field.
An ultraproduct with odd q tending to infinity therefore interprets an
infinite pseudofinite field. Duret's instability result is stated explicitly
in Beyarslan, `math_0701029/math0701029.tex`, lines 22--26: in characteristic
not 2, `x!=y and x+y is a square` defines a random graph in a pseudofinite
field. Thus these exact extremal graph ultraproducts are unstable, even
though adjacency itself has bounded ladder index.

This refutes the assertion that exact fixed-order extremality and a large
minimum degree automatically restore full stability. It does NOT establish
that these particular orders maximize our specified global power-price
score. That further selection issue remains unproved.

The parent checked the geometry argument and exact finite cases q=3,5,7,17.
`/tmp/StableAdjacencyGeometryCheck.py` verifies the counts, triangle definition,
incidence recovery, C4-freeness, and A^2=J+qI. All pass; log:
`/tmp/StableAdjacencyGeometryCheck.log`. These are supporting exact checks,
not numerical searches for an irrational extremal exponent.

## 3. Full stability plus fixed H permits irrational powers without extremality

Choose irrational theta in (1/2,1), put b=2-theta, and sample G(n,n^(-theta)).
For H=K_(4,4), the expected number of copies is O(n^(8-16theta))=o(1), so
H-freeness holds with probability tending to one. Chernoff bounds give

    e(G)~n^b/2,   d(v)=(1+o(1))*n^(b-1) uniformly in v.

Uniform expected edge counts also hold for cuts whose two sides have fixed
positive proportions: the Chernoff exponent dominates the O(n) logarithm
of the number of cuts. The Shelah--Spencer zero-one law has a stable complete
almost-sure theory T_theta. This is explicitly stated for the classical
static model in Elwes, `1809.08333/1809.08333.tex`, lines 43--47. The paper's
separate evolving process is not being used here.

By imposing successively more sentences of T_theta along with these
high-probability events, diagonal deterministic selection produces an
H-free sequence with the stated pure irrational power and stable ultraproduct
theory. It is NOT an extremal sequence: C4-free graphs are K_(4,4)-free and
supply Omega(n^(3/2)) edges, while b<3/2. The example only shows that full
stability itself does not impose a discrete counting exponent.

There is an important finite-basis distinction. The predimension age defined
by `v(F')-theta*e(F')>=0` for every subgraph F' has no finite ordinary
forbidden-subgraph basis. All forests belong to the age, so any forbidden
basis would consist of cyclic graphs. A finite d-regular graph of girth
exceeding all their orders, with d>2/theta, avoids that list but has negative
total predimension. Also, the finite random graphs above do not themselves
belong to this age: their total predimension is negative. Each fixed bad
configuration disappears eventually, not all infinitely many constraints
simultaneously at every finite stage. Neither identification with a fixed-H
extremal class is legitimate.

## 4. A correct conditional mechanism, with an unproved hypothesis

Van Abel, `2103.03276/2103.03276.tex`, theorem `main` (lines 267--273), proves
that in an uncountably categorical theory, pseudofinite cardinalities of
definable sets are rational-coefficient polynomials in the cardinality t
of a definable strongly minimal set; degree agrees with Morley rank.

If an extremal ultraproduct had this single counting scale, then

    |V|=P(t),   |ordered edges|=Q(t)

would force a=deg(Q)/deg(P), hence rationality, by comparison of leading
powers. The relevant vertex polynomial has positive degree because the
orders tend to infinity. This is a valid CONDITIONAL mechanism, not a
proof that the categorical/counting hypothesis holds. The exact C4 example
above even excludes uncountable categoricity for that family.

An N-dimensional asymptotic class also gives rational powers through its
counting hypothesis. It cannot be asserted solely from stability. See
Garcia--Macpherson--Steinhorn, `1409.8635/1409.8635.tex`, proposition `asymp`.
Their local stability criterion `stablecrit` additionally assumes an
attainability condition; example `stablenonattainability` shows that stable
complete theories need not satisfy it.

Even finite Morley rank does not imply a common scale: disjoint unions of
k equal cliques of size m, with k,m tending to infinity, have the stable
rank-two equivalence-relation theory. Choosing m of order k^r yields exponent
(1+2r)/(1+r), arbitrarily irrational. These graphs are not H-free; they only
separate finite rank from a single polynomial counting parameter.

## 5. Status

The parent read the relevant theorem statements and independently checked
the mathematical deductions above. None is a new Lean theorem. The actual
finite-H/global-price hypotheses have not been shown to imply a discrete
counting scale, an asymptotic class, or uncountable categoricity. Neither a
proof of the target nor a counterexample has been obtained. No change to
Spec or proof/disproof submission is justified by this investigation.
