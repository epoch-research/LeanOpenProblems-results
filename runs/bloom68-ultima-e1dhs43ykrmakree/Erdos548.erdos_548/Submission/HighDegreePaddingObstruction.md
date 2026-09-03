# A limitation of padding into the proved high-target-degree case

## Status and scope

This is not a proof or disproof of Erdős–Sós. It tests one possible way to apply the already formalized high-target-degree case to arbitrary targets. The tested reduction fails for an exact numerical reason, independently of whether its padded target has high degree. No Lean file was changed.

Fix a k-edge tree T, k>=2. Consider a construction which adjoins s>=1 universal clique vertices to a host G, obtaining H=K_s join G, and applies the known theorem to a larger tree P with K edges.

A natural role-independent extraction guarantee would be

    (R) For every X subset V(P) with |X|<=s, P-X contains T.

Indeed, from any embedding P->H, remove the preimages of the s added host vertices. Property (R) then gives a T-copy wholly inside G. This is a sufficient extraction condition; the following argument does not rule out other extraction arguments using additional edges or structure of G.

## 1. Tree fragmentation lemma

For every tree P of order N and every positive integer k, there is a set X of at most floor(N/(k+1)) vertices such that every component of P-X has order at most k.

Proof. Root P arbitrarily. While the remaining rooted tree has more than k vertices, choose a vertex v of greatest depth whose descendant subtree has at least k+1 vertices. Every child subtree of v has at most k vertices. Put v in X, declare its child subtrees finished, and remove its entire descendant subtree from the working rooted tree. The remaining working graph is a rooted tree or empty. Each iteration removes at least k+1 previously uncharged vertices, so there are at most floor(N/(k+1)) iterations. The finished child subtrees and the final working tree are exactly the components left after deleting X; each has order at most k. QED.

Consequently, if P satisfies (R), then

    |V(P)| >= (s+1)(k+1),
    K >= (s+1)k+s.                                          (1)

Otherwise the fragmentation lemma would provide at most s deleted vertices with all remaining components of order at most k. Since T is connected and has k+1 vertices, it could not occur in the remainder.

This bound on order is sharp without further restrictions on P: connect s+1 vertex-disjoint copies of T by s edges to form a tree. Any set of at most s vertices misses one entire copy.

## 2. Exact density calculation

Take a host G on n vertices with exactly

    e(G) = (k-1)n/2 + 1.

Such simple hosts exist for arbitrarily large n: take q disjoint K_k blocks and add one edge between two blocks, with q>=2 and n=qk. These hosts are not counterexamples; they are legitimate inputs on which a universal reduction must meet its claimed hypotheses.

For H=K_s join G,

    |H|=n+s,
    e(H)=e(G)+sn+s(s-1)/2.

The literal density surplus for a K-edge target is

    2[e(H) - (K-1)(n+s)/2 - 1]
      = (k+2s-K)n + s(s-K).                                 (2)

But (1) implies

    k+2s-K <= -s(k-1) < 0,
    s-K < 0.

Thus (2) is strictly negative. H fails the density hypothesis for P. This failure persists if one replaces the literal +1 threshold by strict average degree greater than K-1: the additional surplus is only 2, whereas (for k>=2, s>=1 and n>=k+1) the negative terms in (2) have magnitude greater than 2.

Adding still more leaves to P to force its maximum degree above K/2 only increases K and worsens the inequality.

## 3. What remains open in this attempt

No reduction of unrestricted ES to the high-degree special case follows from adjoining universal vertices and using a padded tree that survives deletion of every possible set of added-vertex roles. A different, host-sensitive lifting argument might avoid (R); no such argument was obtained here. Ordinary cloning also does not by itself reflect injective containment, because distinct cloned vertices may project to the same original host vertex.

The unrestricted embedding gap remains. `Submission/Spec.lean` retains both original placeholders, and neither submission claim is justified.
