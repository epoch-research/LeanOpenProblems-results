# A full-critical obstruction to choosing the maximum-degree vertex as a leaf-parent

**This is not an Erdős–Sós counterexample.** It rules out a stronger rooted reduction. The general existence of a suitable high vertex and leaf-parent remains unresolved here. No Lean source is changed.

## Target

Take the six-vertex double star R: two degree-three centers joined by an edge, with two leaves at each center. Subdivide every edge once. At each of the four original leaves of R, add two new leaves. Call the resulting tree T.

Then T has 18 edges, 19 vertices, maximum degree three, and bipartition classes of sizes 6 and 13. The smaller class consists of the six original vertices of R. Its only leaf-parents are the four original peripheral vertices, each now of degree three. If any such parent p and its two leaf neighbors are removed, the remainder is a connected tree with color sizes 5 and 11. Its attachment vertex to p belongs to the 11-class.

## Full-critical host

Put a=17/2. Take 18 disjoint complete bipartite graphs H_i=K_(9,136), with sides A_i of size 9 and B_i of size 136. Add h adjacent to all vertices of every A_i, and to no B_i.

This host G has

    n=2611, e=22194, 2e−17n=1.

Its degrees are 162 at h, 137 on all A_i, and 9 on all B_i. Thus h is the unique maximum-degree vertex and has degree well above 18.

Every nonempty proper induced vertex set S satisfies e(S)≤17|S|/2. To check this for ALL sets, write x_i=|S∩A_i| and y_i=|S∩B_i|.

If h is absent, each wing contributes

    2x_i y_i−17(x_i+y_i)≤0.

For x_i≤8 its y_i coefficient is negative; for x_i=9 its maximum is 136−153=−17. If h is present, then

    2e(S)−17|S| = −17 + Σ_i f(x_i,y_i),
    f(x,y)=(2x−17)y−15x.

For 0≤x≤9 and 0≤y≤136, f(x,y)≤1, with equality only for (x,y)=(9,136). Every other pair has f≤0. Therefore any proper set containing h has total at most −17+17=0. The full set has total one. This is exactly full positive-density criticality, with the possible half-unit surplus for even k.

## Why h cannot be any leaf-parent

Suppose T embedded with a leaf-parent p at h. Delete p and its two leaf neighbors from the target copy. The connected remainder lies in a single component H_i of G−h. Its attachment to h must lie in A_i. By uniqueness of the bipartition of a connected tree, its entire 11-vertex attachment color class must then lie in A_i, which has only nine vertices. This is impossible.

The same reasoning excludes any copy of T minus just one leaf whose corresponding parent maps to h: it would still contain the same connected remainder. Thus neither “take the unique maximum-degree host vertex” nor “every high vertex supports some leaf-parent role” is a valid unrestricted reduction, even on a full-critical host with a subcubic target.

## An actual T-copy using h in a different role

Map one of R's two central vertices to h instead. The three components of T minus that center have (small,large) color sizes

    (1,3), (1,3), (3,7).

Place them in three different wings, sending their large classes into A_i and their small classes into B_i. Their attachment vertices are in the large classes, so the edges to h exist. Each wing has ample capacity. This constructs an actual T-copy containing h, but not with h as a leaf-parent.

The host also contains T entirely within any wing in the opposite orientation (6≤9, 13≤136). Thus it is not close to being an ES counterexample.

## Literal surplus-one statement

G itself has surplus 1/2, so it is a critical core rather than a host satisfying the file's literal +1 bound. Two disjoint copies of G have n=5222 and e=44388, exactly one edge above 17n/2. In this literal host, neither of the two maximum-degree vertices can serve as a leaf-parent of T. Each component separately retains the critical certificate above. The disjoint union is not itself claimed to be vertex-critical.

The restricted peripheral boundary theorem in PeripheralParentClosure.md is unaffected: its target condition is an internal end of degree floor(k/2)=9, whereas all ends here have degree three.

## Stronger odd examples: both extrema among high vertices, literal +1 and full criticality

There is also a smaller, odd-parameter version for which the host itself satisfies both full criticality and the file's exact surplus-one bound. Add one more leaf at one peripheral hub of the 18-edge target above. The resulting T' has k=19 edges, color classes of sizes 6 and 14, and maximum degree four. Its four leaf-parents have degrees 3,3,3,4. Removing any one of these parents and all its leaves leaves a connected remainder whose attachment-color class has size 12 or 11.

Put r=9. Take s disjoint wings K_(10,80+q), and add h adjacent to every 10-side A_i. Choose either

    (s,q)=(2,5), or (s,q)=(10,1).

In both cases sq=10, and

    n=1+s(90+q), e=10s(81+q)=9n+1.

For a subset not containing h, a wing with selected counts x,y contributes xy−9(x+y)≤0, because x≤10 and y≤85. For a subset containing h, its total surplus over 9 times its order is

    −9 + Σ_i [(x_i−9)y_i−8x_i].

Each summand is at most q, with equality only at the full wing (x,y)=(10,80+q). For x≤9 it is nonpositive; for x=10 it is y−80. Thus the full host has surplus one, and any proper subset containing h loses at least one and has nonpositive surplus. This verifies full criticality for all subsets, without enumerating them.

The degrees are

    d(h)=10s,   d(A_i)=81+q,   d(B_i)=10.

For (s,q)=(2,5), h has degree 20 and all other high vertices have degree 86: h is the unique **minimum-degree high vertex**. This host has n=191 and e=1720. For (s,q)=(10,1), h has degree 100 and all other high vertices have degree 82: h is the unique **maximum-degree vertex**. This host has n=911 and e=8200.

In either host, h cannot be any leaf-parent of T': the connected remainder would have to put its 11- or 12-vertex attachment-color class into a 10-side of a single wing. Thus both extremal ways of preselecting a high host vertex fail, even with every statement's literal density and full-criticality hypotheses.

T' embeds entirely in every wing (6≤10, 14≤80+q). It also embeds with one central original hub at h. The three components then have color sizes (1,4), (1,3), (3,7); the first two can occupy one wing and the third another. These are still not ES counterexamples or obstructions to role-free coverage of h.
