# A graphic obstruction to mean payment averaged over any minimum partition

## Status and scope

This is a paper-level counterexample to a proposed auxiliary induction, NOT
an Erdős–Gallai counterexample or a Lean proof. `Spec.lean` is unchanged.
Let c(F) be the minimum number of vertex-simple cycles partitioning an even
edge set, cf(F) its exact fractional version, and a(G) the mean of cf(H)
over ALL uniformly sampled cycle-space words H, including the empty word.

There exist arbitrarily large even simple graphs with c(G)=3 such that
EVERY minimum partition D satisfies

    sum_{C in D} [a(G)-a(G-E(C))] <= -3t/1024 -> -infinity.    (1)

Thus neither an arbitrary minimum partition nor optimization over minimum
partitions gives a positive universal average payment per part. This is
not the earlier obstruction to sampling all optimum-compatible circuits.
Here the sum really is over the three parts of EACH single optimum.

The stronger adaptive choice lemma remains unrefuted: the construction
has explicitly good optimum-compatible circuits to delete. Consequently
neither c<=K a nor Erdős–Gallai is settled.

## 1. Hamilton-decomposable cores of high collapsed girth

Fix g=2048. For every sufficiently large even n=2t there is a loopless
6-regular multigraph G with an edge partition into three Hamilton cycles
C1,C2,C3, and a perfect matching P with the following properties:

* Every pair in P has exactly two copies, one in C1 and one in C2.
* There are no other parallel edges.
* After collapsing each doubled matching pair to one edge, the underlying
  simple graph has girth at least g.

Here is a deterministic extremal proof of existence. Fix a matching P on
n vertices. Start with three Hamilton cycles as edge-distinct factors;
choose the first two to contain designated copies of every edge of P.
This is possible by ordering the matching pairs and joining them into a
Hamilton cycle. Collapse only the two designated copies of each P edge.
Other parallel edges, if present, retain their identities.

Among these finitely many triples, minimize lexicographically the counts
of cycles of lengths 2,3,...,g-1 in the collapsed multigraph. If its shortest
cycle has length h<g, it has a non-designated edge e=ab, since the designated
matching by itself has no cycle. In e's Hamilton factor choose another
non-designated edge f=cd with both endpoints at distance greater than g
from {a,b} in the collapsed graph.

Such an f exists when, for example, n>12*5^g. Maximum degree is at most six.
The union of radius-g balls about a,b has fewer than 3*5^g vertices. A
Hamilton factor has at most twice that many edges touching these vertices
and at least n/2 non-designated edges. Thus some eligible f avoids both
balls. (The first two factors actually have non-designated degree one at
each vertex, but this improvement is unnecessary.)

Delete e,f and use the alternative pairing of their four endpoints that
keeps their factor a single Hamilton cycle. Designated matching edges are
untouched. No new cycle of length at most h is created. A cycle using one
new edge requires an old cross-path longer than g. A cycle using both new
edges requires either such cross-paths, or an old alternate a-b path and
an old alternate c-d path. Each alternate path has length at least h-1,
by the old girth; including the two new edges gives length at least 2h.
The original h-cycle through e is destroyed. This contradicts the chosen
lexicographic minimum, proving the claim. Girth at least g also excludes
all unintended parallel pairs.

Degree six forces at least three cycles in every partition, and the
specified factors attain three. Furthermore every minimum partition
consists of three Hamilton cycles: at each vertex all three parts must
supply two of its six edges.

## 2. The full fractional mean is localized at doubled pairs

For an even word H of G, let L(H) count doubled matching pairs for which
both copies are selected and at least one endpoint has degree two in H.
Each such pair is a forced 2-circuit in every exact fractional partition,
so cf(H)>=L(H). We also have

    cf(H) <= L(H) + 2|H|/g.                                 (2)

To prove the upper bound, collapse parallel copies in H. Each bridge of
the collapsed graph has both copies selected, since an even graph cannot
have a one-edge cut. Let b be their number; delete their 2b edges to leave
H0, with m0=|H|-2b. The underlying nontrivial components of H0 are bridgeless
and each has a cycle of length at least g. Their number N is at most m0/g.

Any deleted doubled bridge not counted in L(H) joins two nontrivial
components of H0. Indeed, at most one doubled pair meets any vertex, so
an endpoint isolated after the deletions had degree two before them.
Contracting the components turns the deleted bridges into a forest; hence
b<=L(H)+N<=L(H)+m0/g.

The only external theorem used here is the standard graphic cycle-cone
theorem: a nonnegative vector w on edges of an undirected graph is a
nonnegative combination of simple-cycle incidence vectors iff

    w(e) <= sum_{f in delta(S), f != e} w(f)

for every cut and every edge in it. The exact theorem is reproduced as
Seymour's theorem in `/corpus/src/math_0511675/siam.tex:1554-1563`; the
interpretation as nonnegative cycle combinations is explicit at 1579-1581.
This is a FRACTIONAL theorem, not integer cycle-double-cover integrality.

On the simple underlying graph of H0 give an edge weight one or two
according to its multiplicity. Every weighted cut has even size. No edge
is a bridge. A weight-one edge therefore has other cut weight at least
one; a weight-two edge has positive other cut weight, which must be even,
hence at least two. All cycle-cone inequalities hold. The resulting exact
fractional partition uses cycles of length at least g, so its total mass
is at most m0/g. Lift each weighted cycle by splitting its coefficient
equally among the choices of parallel copies. This gives exact load one
on each original edge and still uses vertex-simple cycles. Restore the b
pair-cycles. The total is at most b+m0/g<=L(H)+2m0/g, proving (2).

## 3. Exact full-space probabilities

For a doubled pair uv, G-{u,v} is connected: one specified Hamilton cycle
uses uv and leaves a spanning path after removing its endpoints. The
projection of the cycle space onto the edges incident with u or v is
therefore exactly the set of patterns even at u and v, uniformly sampled.
To see surjectivity, the remaining required odd vertices have even total
parity, so a connected remaining graph supplies the prescribed boundary
by paths in a spanning tree. Uniformity follows because all fibers of a
linear projection have equal size.

The two pair bits are arbitrary. Once they are fixed, each endpoint has
four other bits with prescribed parity, giving eight choices independently.
There are 4*8^2=256 traces. Both pair bits are one and at least one endpoint
has no other selected edge in 8+8-1=15 traces. Thus E[L(H)]=15t/256.
Every edge has marginal 1/2, and |E(G)|=6t. Equation (2) yields

    15t/256 <= a(G) <= 15t/256 + 6t/g.                       (3)

Now let D={D1,D2,D3} be ANY minimum partition. It consists of Hamilton
cycles. Let ri count doubled pairs left intact in G-E(Di). A Hamilton
cycle on n>2 vertices cannot use both copies of a pair. Each pair is used
by two different parts and survives intact in exactly one deletion, so

    r1+r2+r3=t.

The residual G-E(Di) is 4-regular and partitioned into two Hamilton cycles.
For an intact pair uv, either Hamilton cycle uses a copy of uv, and again
deleting u,v leaves a connected spanning path. The same full-space trace
argument applies. Each endpoint now has two other incident bits, giving
two parity choices. There are 4*2^2=16 traces, of which 2+2-1=3 force the
pair-circuit. Therefore

    a(G-E(Di)) >= 3ri/16,
    sum_i a(G-E(Di)) >= 3t/16.                              (4)

Combining (3) and (4),

    sum_i [a(G)-a(G-E(Di))]
      <= t*(45/256 + 18/g - 3/16)
       = -3t/1024,                 since g=2048.

This holds simultaneously for every minimum partition.

## 4. Simplicity, adaptive choices, and verification limits

Subdivide EVERY edge of the core once, using a private new vertex for each
edge copy. The resulting graph is simple. Every even restriction uses
both halves of a subdivided edge or neither. Circuits, exact fractional
partitions, and the full cycle spaces correspond bijectively, preserving
c, cf, a, and deletion by corresponding circuits. Consequently (1) is a
counterexample within even SIMPLE graphs, not just multigraphs.

The two originally designated factors C1,C2 are nevertheless good choices
for an adaptive deletion. Deleting either removes one copy of every
doubled pair, leaving a simple high-girth core with 4t edges. Every even
restriction then has an actual cycle partition with cost at most its edge
count divided by g. Thus

    a(G-E(Ci)) <= 2t/g,
    a(G)-a(G-E(Ci)) >= (15/256-2/g)t = 59t/1024 > 0.

So this family DOES NOT disprove an existential positive-payment lemma,
c<=K a, a critical-only lemma, or the Erdős–Gallai conjecture. The whole
core is not critical: c=Delta/2=3, but cycles avoid some vertices.

Parent verification: the switching argument, bridge counting, cycle-cone
hypotheses, restriction marginals, and subdivision correspondence were
read and checked independently. A direct exact enumeration of the local
bit patterns returned 15/256 and 3/16; rational arithmetic confirmed both
-3/1024 and 59/1024. No giant graph enumeration was used or claimed. The
cycle-cone input was cross-checked against the local source above. This
note is not a Lean verification and supplies no edit to either admission
in Spec.
