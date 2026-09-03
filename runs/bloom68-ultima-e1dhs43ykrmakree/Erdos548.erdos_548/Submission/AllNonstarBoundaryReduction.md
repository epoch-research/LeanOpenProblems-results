# The near-clique boundary terminal extends to every nonstar tree

## Status

This proves a stronger finite boundary terminal than the version in `GraphicCircuitReduction.md`. It does **not** prove Erdős–Sós: the large forest-density atoms remain unresolved. No Lean file was changed. The finite list edge-sum packing theorem used below has not been formalized in this project.

## 1. Boundary theorem without a maximum-degree restriction

Let k≥3, let r=floor(k/2), and let T be any nonstar tree with k edges. Suppose J has k vertices and at most r−1 missing edges. If an ambient graph contains J and an edge xy with x∈J and y∉J, then the ambient graph contains T.

### Choosing the pendant star

The nonleaves of T induce a tree I with at least two vertices. Choose an end p of I of minimum target degree d. Then

    2≤d≤ceil(k/2)=k−r.

Indeed, if I has two vertices, the sum of their target degrees is k+1. If I has at least three vertices, two distinct ends are nonadjacent, so their sets of incident edges are disjoint and their degrees sum to at most k. Either argument gives the displayed bound.

The vertex p has d−1 leaf neighbors and one nonleaf neighbor u. Delete p and its leaf neighbors. The remainder R is a connected tree of order

    m=k+1−d≥r+1.

We will map p to x, and one of its leaves to y. Write q≤r−1 for the number of missing edges in J. Notice

    d_J(x)≥k−1−q≥k−r≥d,    and    q≤m−2.                 (1)

### Case A: R is not a star

Let B be the t nonneighbors of x in J, excluding x itself. Reserve any d−2 neighbors of x as D for the remaining leaves at p, and set K=J−({x}∪D). Then |K|=m, B⊆K, and the complement of K has at most q−t edges.

Use the finite list edge-sum packing theorem with first graph R, second graph the complement of K, and forbidden assignments u→b for b∈B. Its edge sum is at most

    (m−1)+(q−t)+t=m−1+q≤2m−3.

Since R is a nonstar tree, its maximum degree is at most m−2. The complement and forbidden-assignment graph each have at most q≤m−2 edges, so their required maximum-degree bounds also hold. R is connected of order at least four, excluding all seven exceptional pairs of that theorem. Hence R embeds in K with u avoiding B, and so with its attachment adjacent to x. Restore p at x and its leaves at y and D.

The input theorem is Győri–Kostochka–McConvey–Yager, *A list version of graph packing*, arXiv:1501.02488, theorem `List B-E`, in `/corpus/src/1501.02488/b-e_2015_01_01arXiv.tex`. This is the proved finite edge-sum theorem, not a degree-product conjecture.

### Case B: R is a star

At most 2q≤2r−2 vertices of J are incident with missing edges. Therefore J has at least k−2r+2≥2 universal vertices. Choose one c≠x; in particular c is adjacent to x.

If the attachment u is a center of R, map u to c. Choose d−2 neighbors D of x avoiding c; (1) guarantees enough. After removing x and D, the remaining m-vertex host contains c as a universal vertex, so the rest of the star embeds. This also handles R=K2, by designating u as its center.

Otherwise R has at least three vertices and u is a leaf. Choose z∈N_J(x)\{c}, and reserve d−2 other neighbors D of x avoiding c and z. This is possible because d_J(x)≥d. Map the center of R to c and u to z, and its other leaves to the remaining vertices of J−({x}∪D). Universality of c supplies all star edges, and xz is the required attachment.

In both subcases restore p at x, one leaf at y, and the other leaves at D. All occupied sets are disjoint, and the total order is m+d=k+1. This proves the boundary theorem.

The improvement is genuine: the old proof used Δ(T)≤r to restrict the star-remainder case. Universal vertices in the near-clique instead handle that case for arbitrary nonstar T.

## 2. Consequence for the exact atom reduction

Put a=(k−1)/2. For k≥3, define an a-atom C by

    e(C)=floor(a(|C|−1))+1,
    e_C(S)≤a(|S|−1) for every nonempty proper S.

The following two statements are equivalent, but both remain unproved here:

(A) Every a-atom of order at least k+2 contains every nonstar k-edge tree.

(U) Every connected H of order at least k+1 with e(H)>a(|H|−1) contains every nonstar k-edge tree.

The extraction and connectivity proofs in `GraphicCircuitReduction.md` apply unchanged. A minimal nonempty positive forest-surplus set, followed by edge trimming, is an atom and has order at least k. At order k it has exactly r−1 missing edges and an ambient boundary edge, so the theorem above applies. At order k+1 it has k−1 missing edges, and the ordinary finite edge-sum packing theorem embeds every nonstar spanning tree. Larger atoms are precisely (A). Conversely atoms are connected, so (U) implies (A).

Thus the earlier maximum-degree restriction is unnecessary for the two terminal orders. This does not establish universality of large atoms or justify target-copy lifts through their spanning-tree decompositions.

If (A) were proved for all k≥3, it would imply the full requested conjecture: pass to a connected positive-average-density component and apply (U) to nonstar targets. Star targets follow immediately from the average degree being greater than k−1. Small k can be handled directly. No assertion that the original ES conjecture implies this connected strengthening is made.

## Preservation

`Submission/Spec.lean` remains unchanged, with both original placeholders and hash

    674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103.

The missing mathematical step is still the unrestricted large-atom embedding theorem. No proof or disproof is ready for submission.
