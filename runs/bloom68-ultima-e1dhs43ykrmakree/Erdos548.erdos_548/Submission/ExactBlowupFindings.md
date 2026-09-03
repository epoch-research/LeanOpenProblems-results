# Exact weighted blow-ups and a zero-capacity-loss completion lemma

**Status: unrestricted Erdős–Sós is not proved.** The concrete additional result is an exact theorem for degree-two quotient graphs, together with a conditional one-way completion/lifting lemma. This does not assume general weighted Erdős–Sós, preservation of noncontainment under ordinary cloning, or any stationary-root distribution. No Lean file or specification was changed. All embeddings are injective homomorphisms, not induced embeddings.

## 1. An exact weighted criterion, including odd-cycle blow-ups

For a simple quotient graph F and positive integer weights w_i, let B(F,w) replace i by an independent class C_i of size w_i and replace each quotient edge by a complete bipartite block. Write

    N = sum_i w_i,    E = sum_{ij in E(F)} w_i*w_j,
    D_i = sum_{j adjacent to i} w_j.

**Theorem 1.** If the maximum degree of F is at most two and a,b are positive integers, then

    2E > (a+b-2)N

implies that some i satisfies

    (w_i >= a and D_i >= b)  or  (w_i >= b and D_i >= a).       (1)

In particular B(F,w) contains K_(a,b). Consequently every such weighted blow-up of average degree greater than k−1 contains every k-edge tree, including the entire low-maximum-degree case. This is a direct capacity certificate, not an appeal to weighted Erdős–Sós.

### Proof

Assume a<=b. The case a=1 is just the maximum-degree bound, so put s=a−1>=1, t=b−1>=s, and c=(s+t)/2. Suppose there is no star-supported biclique (1).

Repeatedly delete any whole class whose current weighted degree is at most c. Deleting C_i changes E−cN by −w_i(D_i−c), so positive surplus persists. The process ends nonempty, still with a quotient of maximum degree two, and now every D_i>c>=s. All subsequent quantities refer to these remaining classes.

Every surviving weight satisfies w_i<=t: otherwise C_i and its neighborhood have capacities at least b and a. Call i *medium* if w_i>s and *light* otherwise. For a medium class, failure of (1) gives D_i<=t, hence

    w_i(D_i−s−t) <= −s*w_i.                                (2)

For a light class i,

    w_i(D_i−s−t) <= (s/2) sum_{j medium, j adjacent to i} w_j. (3)

Indeed, with at most one medium neighbor we have D_i<=s+t, so the left side is nonpositive. With two medium neighbors, D_i<=2t. If D_i−s−t is positive, use w_i<=s and D_i−s−t<=D_i/2; otherwise the inequality is immediate.

Sum (3). Each medium class has at most two light neighbors, so the total light contribution is at most s times the medium weight. This cancels (2). Thus

    2E−(s+t)N = sum_i w_i(D_i−s−t) <= 0,

contrary to retained positive surplus. This proves (1). Map the two tree color classes into the indicated biclique to obtain the tree corollary. QED.

The strict threshold is genuine: the uniform q-blow-up of C5 has average degree 2q and contains no K_(q+1,q+1). Any biclique in it has one side in a single quotient class, since C5 has no triangle or 4-cycle.

## 2. Safe completion without shrinking any capacity

The next lemma applies to an arbitrary simple quotient F, not just degree-two quotients.

Let H=B(F,w) and let G be any graph on the same vertex set. Put

    D = E(H) minus E(G),    d = maximum degree of the defect graph D.

Let I be a set of quotient classes meeting every defect edge. Suppose P is a graph of maximum degree Delta and an injective H-embedding of P is available. Equivalently, one can start with a homomorphism h:P→F satisfying |h^(-1)(i)|<=w_i, then choose distinct positions within each class.

**Theorem 2 — zero-capacity-loss lifting.** If

    w_i >= 2*Delta*d   for every i in I,                     (4)

then P embeds in G with exactly the same class assignment h. No capacities are reduced; equality in (4) is allowed. Only classes covering defects must meet (4); other classes need only accommodate their assigned pattern vertices.

### Proof by strictly improving swaps

Start with any class-respecting injection phi. A conflict is a pattern edge mapped into D. Choose one, uv, with h(u)=i in I, and put x=phi(u). For y in C_i, let z be its current occupant, if any. Swapping u with z, or moving u to an unused y, creates no new conflict if:

* y is adjacent in G to all images of neighbors of u;
* if z exists, x is adjacent in G to all images of neighbors of z.

At most Delta*d candidates fail the first condition. At most Delta*d fail the second: x has at most d defective neighbors, each with at most one pattern preimage, and each preimage has at most Delta neighbors that could occupy y.

Crucially, y=x fails **both** conditions because uv was a conflict. Thus their union has size at most 2*Delta*d−1. Condition (4) supplies an allowed y. Since vertices with the same quotient color are nonadjacent in P, neither swapped vertex is a neighbor of the other; the stated tests therefore check all affected edges correctly. The swap eliminates the chosen conflict and creates none. The number of conflicts strictly decreases, so at most e(P) swaps finish. QED.

A useful more local version replaces 2*Delta*d in class i by R_i+S_i. If d_ij bounds the number of defects from each vertex of C_i into C_j, set

    R_i = max_{u: h(u)=i} sum_{v adjacent to u} d_(h(v),i),
    S_i = sum_{j adjacent to i} d_ij *
          max_{v: h(v)=j} |N_P(v) intersect h^(-1)(i)|,

with empty maxima zero. The same two forbidden-set counts prove lifting whenever w_i>=R_i+S_i on a defect cover. This refinement depends on an actual capacitated quotient homomorphism, not merely on raw list sizes.

### An asymmetric Hall improvement for a single complete bipartite block

Suppose K_(p,q) is completed and every vertex misses at most d opposite-side neighbors in G. Let P have bipartition A,B, with sizes a<=p, b<=q and maximum degrees Delta_A, Delta_B on its two sides. Then

    p >= d*(Delta_A+Delta_B)                               (H)

suffices for a color-respecting embedding; **q needs no additional slack**.

Fix any injection of B into the q-side. Each vertex of A has a common-neighbor list on the p-side missing at most r=d*Delta_A positions. Each position is excluded by at most s=d*Delta_B lists. If a nonempty set U of lists violated Hall, a position outside their union would give |U|<=s, while any one list would give |U|>p−r>=s. Contradiction. Thus all of A can be matched, even when both capacities are fully used.

This is an exact forest-packing statement for incomplete bipartite blocks. For the star-supported certificate in Theorem 1, the center has capacity at least min(a,b). Therefore the entire approximate-blow-up conclusion below also holds, **without any minimum cluster-size assumption**, if

    min(a,b) >= d*(Delta_A+Delta_B).                        (6)

For a k-edge tree of maximum degree Delta, the simpler sufficient inequality

    k >= 2*d*Delta^2                                      (7)

implies (6), because each tree color class has at least k/Delta vertices. Conditions (6)–(7) restrict defects, not density: the edge threshold remains exactly k−1.

## 3. Exact edge accounting for approximate blow-ups

For a proposed completion H=B(F,w), also write

    R = E(G) minus E(H).

These are the original edges ignored by the template, including possible within-class edges. The exact identity is

    e(H)−(k−1)N/2
      = [e(G)−(k−1)N/2] + |D|−|R|.                         (5)

Combining Theorems 1 and 2 gives this sufficient criterion:

> If F has maximum degree at most two, the right side of (5) is positive, and the defect-cover capacities satisfy (4), then G contains the specified k-edge tree T, using Delta=Delta(T).

For a critical graph with surplus eta in {1/2,1}, positivity in (5) is **exactly** |D|>=|R|. Thus completed missing edges can compensate for ignored original edges without losing even half a unit of surplus. The lifting theorem, rather than an unjustified cloning claim, certifies the one-way transfer back to G.

## 4. A genuine critical, false-twin-free example where the criterion applies

For t>=1, start with the C5 blow-up of class sizes

    (6t,6t,6t,6t,12t).

It has N=36t and 252t² edges. There is a perfect matching: match C1 to C2, C3 to half of C4, and C0 to the other half of C4. Delete all but one edge of this matching. Call the result G_t. Then

    k=14t,    e(G_t)=252t²−18t+1=(k−1)N/2+1,
    delta(G_t)=12t−1,    d=1.

It is nonbipartite and has no false twins: almost every vertex has its own distinct missing matching partner, and distinct quotient classes have neighborhood differences much larger than two.

Here is a full criticality proof, not just a degree check. Put a=7t−1/2. For a proper subset S of size s<=28t−2, triangle-freeness and Mantel give e(S)<=s²/4<=as. Otherwise X=V−S has 1<=x<=8t+1. Again using triangle-freeness,

    I(X)−ax >= (12t−1−a)x−x²/4
             = x(5t−1/2−x/4)
             >= x(3t−3/4) > 1.

Since the whole surplus is one, e(S)−as=1−[I(X)−ax]<0. Thus every proper induced subgraph is a-sparse.

Nevertheless Theorems 1–2 directly embed every k-edge tree with Delta(T)<=3t, because the smallest class has size 6t=2(3t)d. At t=1 this embeds every subcubic 14-edge tree with no capacity or surplus loss. The plain greedy bound delta>=k fails, and the supplied one-apex CL corollary would require a tree vertex of degree at least four there. So this is a nonvacuous application in the remaining low-degree regime.

In fact the whole family is universal for all k-edge trees after combining this with the supplied CL corollary: a vertex of host degree 18t exists, and delta(G_t−s)>=12t−2. CL handles Delta(T)>=2t+2; our lifting handles Delta(T)<=3t. Since 3t+1>=2t+2 for t>=1, these ranges leave no integer gap. This is a theorem for this displayed family, not for arbitrary critical graphs.

## 5. Compression bookkeeping and the exact unresolved gap

For an **exact** independent blow-up there is also a useful finite compression of criticality tests. Suppose E−aN=eta>0. All proper induced subgraphs are a-sparse if and only if:

1. every proper union of whole quotient classes is a-sparse;
2. D_i>=a+eta for every class i.

Necessity follows from whole-class subsets and deletion of one vertex. For sufficiency, e(S)−a|S| is multiaffine in the counts x_i=|S intersect C_i|. Fix a class with x_i<=w_i−1 and maximize over that box. A corner with x_i=0 is a proper whole-class union. For a corner with x_i=w_i−1 and another class missing, interpolate between proper whole-class unions to get a nonpositive value. The only remaining corner is the full graph minus one vertex, covered by condition 2. Thus the complete induced-subset constraint is retained, not replaced by minimum degree alone.

What remains is a **structural existence theorem**. Given an arbitrary T-free critical graph with high codegree, one would have to produce a partition and a quotient from a proved weighted-universal class such that both:

    |D|>=|R|,    and    the defect-cover lifting bounds hold.

Neither criticality nor a large common neighborhood currently supplies such a partition. In particular, codegree controls |N(u) intersect N(v)|, not the neighborhood symmetric differences required for low defect degree.

There is an explicit warning even at surplus one. Any connected 2r-regular graph Q plus one missing edge is an r-critical graph: every proper cut of Q has positive even size, so e_Q(S)<=r|S|−1 for nonempty proper S; adding the edge preserves e(S)<=r|S|. For a prime power 4r+1, choose Q to be its Paley graph and set k=2r+1. Its codegrees are r−1 or r, while every pair of neighborhoods differs in at least 2r vertices. After adding the edge, codegrees remain of order r and neighborhood differences are still at least 2r−2. Thus full criticality and large codegree alone do not force near twins. These graphs themselves have minimum degree k−1 and are covered by the existing CL corollary; they are not ES counterexamples. Any useful structural dichotomy must exploit T-freeness or first dispose of such already-embeddable cases.

There is an exact obstacle to a delete-only variant: in a critical graph with 0<eta<=1, **no proper subgraph** retains average degree greater than k−1. A proper vertex subset already fails the threshold; on the full vertex set, deleting even one edge exhausts the surplus. Therefore conservative trimming to a blow-up cannot work unless the graph already is that blow-up. Compensated completion plus a valid lifting argument really is necessary for this version of the route.

The present theorem handles weighted paths, cycles (including odd cycles), and disjoint unions of these. It does not establish weighted universality for arbitrary small quotients, let alone arbitrary quotients. Taking all capacities equal to one would recover the original unrestricted difficulty; that observation is not used as a proof. Ordinary cloning/amplification preservation, stationary-root marginals, and polynomial stability are not assumed.

## 6. Verification

Run `python3 Submission/ExactBlowupChecks.py`; the log is `Submission/ExactBlowupChecks.log`. It passed:

* 514,113 exact biclique-capacity certificates on 157,814 weighted path/cycle hosts;
* 60,654 local charging inequalities and 3,135 full-subset/compressed-criticality equivalences;
* 120,384 spanning P8 bijections on all 209 matchings deleted from K4,4, with **zero spare capacity**; 87,552 initial copies had conflicts, all repaired. Independent NetworkX non-induced containment checks covered every defect matching;
* 1,500 additional colored lifts, including 1,469 capacity-threshold equality cases;
* 2,000 asymmetric Hall lifts (1,082 beyond the uniform bound) and 500 additional full-capacity K6,15 examples;
* 181,800 all-subset-size bounds for the critical family through t=100, and ten explicit nonbipartite, false-twin-free graph audits;
* all 1,132 nonisomorphic subcubic 14-edge trees embedded in G_1, including 848 completion copies requiring repair;
* 16 Paley-plus-edge host audits, including 139,290 direct proper-subset checks through order 17.

A separate exact-rational implementation checked the critical-family inequalities through t=500. These finite checks support the displayed mathematical proofs; they are not a proof of general Erdős–Sós and are not Lean formalizations. `Submission/Spec.lean` retains SHA-256 `674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103`.
