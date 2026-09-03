# Independent global closing attempt: matching pinches and double-cover collisions

## Outcome — the exact conjecture is still unresolved

I obtained **neither an unrestricted Erdős–Sós proof nor an actual ES counterexample**. No Lean theorem was supplied, no axiom was introduced, and no existing Lean file was edited. In particular, `Submission/Spec.lean` still has its two original `sorry`s and SHA-256

```
674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103
```

The substantive additions are:

* A correct lifting rule allows **one virtual edge anywhere on a pendant path**, not only a pendant edge. There is also a two-virtual-edge rule on one pendant path.
* If a matching of at most r edges is removed from an r-circuit, **every resulting component has at least 2r+1 vertices**, and its total r-deficit is exactly the matching size minus one. Small-component separator traps therefore cannot obstruct the proposed resilience theorem.
* For a balanced target, the positive-density double-cover approach has an exact rigidity statement. In a **strict nonbipartite r-circuit, the only positive pair of sheet domains is X=Y=V(G)**. Thus choosing a better positive asymmetric core cannot remove any overlap or decrease its projection. A fully audited 16-vertex example has minimum degree 6, is 6-degenerate, and defeats the numerical one-apex and two-interface tests for a specified balanced subcubic nonspider; it nevertheless contains that tree explicitly.
* The stronger matching-resilience statement from the checkpoint survived **316 host/tree instances with every matching of size at most r certified**, not merely sampled. These are finite tests, not a theorem. The certificates were checked by a separate exact integer search, rather than trusting floating-point MILP infeasibility.
* A bounded direct search imposed the **full** proper-induced-set criticality constraints and the literal odd-k density. Its 74 returned critical hosts all contained the requested targets. The searches stopped at time limits; they did not exhaust the graph classes.

These findings do not supply the missing arbitrary-host, shape-sensitive selection theorem.

## 1. Matching pinches: a less restrictive sufficient interface

Let C be a simple graph, M a matching, and G the graph obtained by deleting M and adding a new vertex z adjacent to every endpoint of M (and possibly additional vertices). The following statements need no density assumption. Let f be an actual injective T-copy in C.

### 1.1 One virtual edge on a pendant path

Suppose the only edge of the copy belonging to M is f(v)f(u_0). Suppose the component of T-vu_0 containing u_0 is a path

```
u_0-u_1-...-u_l,
```

rooted at its endpoint u_0. This includes l=0. Keep every other target image fixed and set

```
u_0 -> z,
u_i -> f(u_(i-1))    (1 <= i <= l).
```

The edge to v exists because z is adjacent to f(v). For l>=1 the first path edge uses z f(u_0); every subsequent path edge uses an old, nonvirtual path edge. The image f(u_l) is discarded. The new map is injective and realizes exactly T, with no additional target vertex.

Thus the virtual edge can be internal to a long pendant leg. The earlier requirement “at most one virtual edge, necessarily pendant” is sufficient but is **not necessary for this elementary lift**.

### 1.2 Two virtual edges, including the end of that leg

Suppose the copy uses exactly the two matching edges

```
f(v)f(u_0),   f(u_(l-1))f(u_l),
```

where the same pendant path has l>=2. Set

```
u_0 -> z,
u_i -> f(u_(l-i))    (1 <= i <= l),
```

and fix the other images. This follows the old leg backwards from its penultimate vertex. The two edges incident with z are supplied by the two pinched matching edges; every remaining required edge is original. Again only f(u_l) is discarded.

The verifier checked 3,351 one-edge maps and 416 two-edge maps, over all nonisomorphic trees with 2 through 11 vertices and all applicable directed edges. Each resulting injection was checked edge by edge.

### 1.3 Why this does not close circuit lifting

The missing assertion is still that some suitable **fresh** copy exists in the extracted circuit. No argument was found forcing the virtual edges of a copy into these patterns. In particular, a bare internal edge between branching regions is different from an edge on a pendant path.

Even arbitrarily many fresh leaf neighbors at the inserted vertex do not make arbitrary internal-edge lifting valid without the critical-host information. Here is a complete all-role obstruction, not just a fixed-core failure:

* Start with a double star having two degree-three hubs and two leaves at each hub.
* Subdivide every edge once, and lengthen one pendant arm by an additional odd number of edges. For every r>=5 this gives a `(2r+1)`-edge tree T with two degree-three hubs at distance two. All three neighbors of either hub are nonleaves.
* Subdivide one edge of the hub-to-hub path by z and give z r-1 new leaf neighbors.

In the resulting host, z has only two nonleaf neighbors. It cannot be the image of either target hub. The only eligible hub images are the two old hubs, now at distance three rather than two. Since the host is a tree, T has no embedding at all. This was checked independently by two exact matchers for r=5,...,13.

**This host has minimum degree one and a very large density deficit. It is not critical, not W, and not an ES counterexample.** The example only explains why the new pendant-path rule cannot be replaced by an arbitrary-edge rule on the strength of fresh leaves alone.

## 2. A useful global constraint on a matching-deleted circuit

Let r>=1 and k=2r+1, let C be an r-circuit, and let M be a matching of q edges, where `1<=q<=r`. Put H=C-M. For a component S of H define

```
d(S) = r|S| - e_H(S).
```

Then

```
d(S) >= 0,             sum_components d(S) = q-1,
delta(H) >= r,         |S| >= 2r+1 for every component S.      (1)
```

Proof of the first line: a proper component is an induced subset of C with some matching edges removed, so its deficit is nonnegative. If H is connected, its unique component has deficit q-1 directly. Summing edge counts gives the displayed total.

The minimum-degree bound follows because a matching removes at most one edge at a vertex and `delta(C)>=r+1`. Consequently a component with s vertices has `s>=r+1`. If `s<=2r`, simplicity gives

```
d(S) >= rs - s(s-1)/2 = s(2r+1-s)/2 >= r.
```

The last inequality holds on `r+1<=s<=2r`, by concavity and the two endpoint values. It contradicts `d(S)<=q-1<=r-1`. This proves (1).

In particular, a component of the minimum possible order `2r+1=k` is a clique with at most q-1 missing edges. This is a genuine constraint on an attempted matching-resilience obstruction.

The remaining connected case is not settled by (1). It can have arbitrarily large order and deficit in `[0,r-1]`. A general assertion that every such connected, minimum-degree-r host contains the required low-maximum-degree tree would be a substantive strengthened ES-type theorem, not an available induction hypothesis. I did not assume or prove it. Nor did I assume arbitrary prescribed-root packing in the almost-clique components.

## 3. Double covers: enough projected labels, but no general collision elimination

For a nontrivial target, write its positive color-class sizes as a<=b, with `a+b=k+1`. Let X be the set of original vertices permitted on the first sheet of the bipartite double cover and Y those permitted on the other. The natural pruning potential is

```
Q(X,Y) = e_D(X,Y) - (b-1)|X| - (a-1)|Y|,
```

where e_D counts edges of the double cover, so edges with both endpoints in `X intersect Y` are counted twice.

Set

```
I = X intersect Y,   P = X-Y,   R = Y-X,   S = X union Y,
c = (a+b-2)/2,       h = b-a.
```

The exact identity is

```
Q(X,Y) = [e_G(S)-c|S|] + [e_G(I)-c|I|]
         -e_G(P)-e_G(R) - (h/2)(|P|-|R|).                    (2)
```

This follows by partitioning edges, not by any embedding assumption.

### 3.1 Positive potential already rules out the simplest label-count obstruction

For every simple G, `Q(X,Y)>0` implies `|X union Y|>=k+1`.

To prove it, suppose `s=|X union Y|<=a+b-1`, put x=|X| and y=|Y|, and use

```
e_D(X,Y) <= xy-|X intersect Y|.
```

If x<=a-1 or y<=b-1, nonpositivity is immediate from `e_D<=xy`. Otherwise write x=a+u, y=b+v. The overlap has size at least `1+u+v`, and

```
Q(X,Y) <= uv-(a-1)(b-1) <= 0,
```

because `u<=b-1` and `v<=a-1`.

So padding a too-small clique with unrelated vertices is not a counterexample to a *positive-potential* lifting theorem. I explicitly kept this distinction while investigating the double-cover route.

### 3.2 Exact rigidity in the balanced critical case

Now assume `a=b=r+1` and C is an r-circuit. Formula (2) becomes

```
Q(X,Y) = [e_C(S)-r|S|] + [e_C(I)-r|I|] -e_C(P)-e_C(R).       (3)
```

Every positive domain pair has `S=V(C)`. If I is proper, integrality and criticality force

```
e_C(I)=r|I|,    e_C(P)=e_C(R)=0,    Q(X,Y)=1.                (4)
```

The other possibility is `I=V(C)`, hence `X=Y=V(C)`, with Q=2.

Call C **strict** if every nonempty proper S has `e_C(S)<=r|S|-1`. In a strict circuit, (4) is possible only with I empty. In that case P,R form a bipartition of the entire host. Therefore:

> **In every strict nonbipartite r-circuit, the only positive domain pair is `X=Y=V(C)`.**

This is stronger than observing that the ordinary peeling algorithm has no first deletion. It excludes **every** alternative positive pair of sheet domains. Positive-density pruning alone cannot remove even one paired-label overlap in this class.

This does **not** say that the graph has no useful bipartite subgraph or no colored embedding. A sufficient colored minimum-degree certificate need not have positive Q. Nor does it say that the original tree is absent. It isolates the failure of this particular positive-potential induction measure.

### 3.3 A fully critical, nonterminal-for-the-basic-tests example

`GlobalClosingStrictCircuit.json` specifies a 16-vertex graph C with 65 edges, r=4, degrees

```
13,8,7,9,6,8,10,7,7,7,11,6,8,10,6,7.
```

Its maxima of `e(S)-4|S|`, for proper subset orders 1,...,15, are

```
-4,-7,-9,-10,-10,-10,-10,-9,-9,-8,-7,-6,-4,-3,-1.
```

All 65,534 nonempty proper subsets were checked with exact integer arithmetic, using a second subset-counting recurrence in the audit. The triangle 0-1-3-0 shows nonbipartiteness. A 6-degeneracy order is

```
4,9,15,2,8,11,7,12,1,10,13,0,3,5,6,14.
```

Thus it has neither a 7-core nor an 8-core.

Take the balanced subcubic target with edges

```
06,67,71,08,82,19,94,03,15.
```

Its two degree-three hubs are distance three apart; its color classes both have size five. Every high vertex s of C leaves `delta(C-s)=5`, whereas the exact-apex forest budget is `k-Delta(T)=6`. Its adjacent target degree sums and its degree-two-middle endpoint sums are at most five, so neither two-interface signature in the checkpoint meets `delta(C)+sum>=k+3=12`.

Nevertheless the explicit target-label-to-host-label injection

```
[0,4,7,8,5,9,1,3,2,6]
```

embeds it. This example is **not** an ES counterexample. It demonstrates that the positive-double-cover obstruction persists beyond the minimal-support complete-graph example and without the basic apex/core/interface certificates. It does not assert failure of every previously proved sufficient criterion.

## 4. The forest-budget and saturation/shape attempts

I also tried to close the one-unit gap left after mapping a shape-extremal target's high-degree vertex: replace the known `delta>=e(F)` forest theorem by `delta>=e(F)-1`, retaining very large root lists and allowing fresh whole-component embeddings. This is false even with every root list equal to the entire host and every component order at most e(F).

For t>=3 take

```
H = K_(t,t),        F = K_(1,t) disjoint-union K_2.
```

Here `delta(H)=t=e(F)-1` and `|H|>=|F|`. Any t-leaf star occupies one whole host color class; the remaining vertices lie in the other independent class and cannot supply the extra edge. This is an all-role obstruction, not a prescribed-root failure. The first small obstruction found was `K_(3,3)` versus `K_(1,3)+K_2`.

This graph is not a critical ES counterexample. The calculation only invalidates the proposed uniform degree discount. Extra full-critical information might still support a genuinely shape-sensitive theorem, but no such theorem was obtained.

For saturated/shape-extremal witnesses, I retained the established valid premises: more concentrated missing-tree shapes can be excluded, and every relevant nonedge completion has an actual copy using that edge. I tried to combine these copies with the matching-deleted component budget and with the relaxed leg-lifting rule. The missing step remained selecting a copy with a liftable interface; neither saturation nor a larger degree vector specifies the roles of the virtual edges. I did not treat arbitrary star certificates, scalar load allocations, or positive potentials as if they supplied those roles.

A separate dense rooted-packing probe tested the possible sufficient inequality `e(complement H)+Delta(T)<=|T|-1` for arbitrary prescribed roots on orders 4,...,9. All 35,316 tested rooted cases passed. **That proposed general theorem was not proved and is not used in any result here.** Even if true, it would only improve a small-support terminal, not settle the unrestricted connected case in Section 2.

## 5. Global matching tests and direct actual-counterexample searches

### 5.1 All matchings, not just a sample

For fixed C,T, the stronger checkpoint property asks for a T-copy using no M-edge except possibly one pendant edge. A copy f is bad for M exactly when

```
2 * #(internal copy edges in M) + #(pendant copy edges in M) >= 2.  (5)
```

The search uses matching variables on all edges of C, cardinality at most r, and successively adds (5) for actual copies found by an exact matcher. This is a search over the **entire** matching choice space for that instance.

Importantly, a floating-point MILP infeasibility result was not accepted as final. A separate integer backtracking verifier checked that the finite family of copy inequalities cannot be satisfied by any matching of size at most r. It partitions solutions by the first chosen edge of an unfinished inequality, enforces endpoint disjointness exactly, and has an explicit node limit. None of the reported certificates hit that limit. The verifier itself was cross-checked against exhaustive matching enumeration on 500 independent small instances.

Results:

| Circuit source | Parameters | Host/tree instances checked against every matching | Actual-copy inequalities | Outcomes |
|---|---|---:|---:|---|
| Minimum circuits, two-clique bridge circuits, regular-plus-edge circuits, followed by matching pinches | r=2,3,4 | 84 | 969 | all certified |
| Independently generated quota orientations containing a spanning out-tree, with uniform/path/hub-biased completion | r=3,4,5,6 | 232, on 32 hosts | 8,944 | all certified |

The first source additionally tested 1,680 explicit sampled matchings across 420 host/tree instances. Every positive injection was checked edge by edge. The second source is independent of inverse-pinch generation: all outdegrees are r except r+1 at the root, and a spanning out-tree proves root reachability, hence full circuit criticality. Criticality was also checked by an independent integral endpoint-slot flow.

**These 316 finite certificates do not prove the resilience theorem for arbitrary circuits.** No counterexample to that strengthening was found, but no global construction of the required fresh copy was proved.

### 5.2 Direct searches for an actual ES counterexample

These searches did not replace full criticality by minimum degree. For k=2r+1 they imposed:

* exactly `rn+1` edges;
* every proper induced-set inequality `e(S)<=r|S|`;
* minimum degree at least r+1;
* a high vertex, labeled 0;
* a distinct low vertex, labeled 1, with degree at most `k-Delta(T)`, which any counterexample must have by the already proved apex theorem;
* exclusion constraints for every actual target copy discovered.

All sets of order at most `2r+1` are sparse automatically by simplicity; every larger proper set was included explicitly. Each returned candidate was rechecked using exact integer arithmetic and the independent criticality flow before containment was tested.

| k | n | Delta(T) | Structural constraints | Critical candidates returned | Verified copy constraints | Stop |
|---:|---:|---:|---:|---:|---:|---|
| 11 | 15 | 3 | 591 | 36 | 1,080 | 90-second search budget |
| 13 | 17 | 4 | 851 | 38 | 1,140 | 90-second search budget |

All 74 candidates contained T. These runs **did not establish infeasibility** and were **not exhaustive**. They are bounded attempts to find an actual counterexample, not small-case proofs of ES.

## 6. Reproducibility and preservation

New files only:

* `GlobalClosingIndependentChecks.py`: exact embeddings, circuit checks, matching searches, independent exact cut verifier, and self-tests.
* `GlobalClosingCriticalSearch.py`: independent quota-circuit generation and bounded actual ES searches.
* `GlobalClosingAnalyticChecks.py`: explicit leg maps, all-role internal-edge obstruction, strict-circuit audit, matching-component budgets, double-cover identities, and the forest-budget obstruction.
* `GlobalClosingRootedDenseProbe.py`: the optional, explicitly unproved rooted-packing hypothesis probe.
* `GlobalClosingStrictCircuit.json`: the complete graph edge list, all proper-subset maxima, degeneracy order, and explicit T-copy.
* Corresponding `GlobalClosing*Checks.log`, `GlobalClosingActualSearch.log`, and probe logs.

Main checks:

```
python3 Submission/GlobalClosingIndependentChecks.py selftest
python3 Submission/GlobalClosingAnalyticChecks.py
python3 Submission/GlobalClosingIndependentChecks.py resilience --samples 20
python3 Submission/GlobalClosingCriticalSearch.py resilience --samples 8
```

The embedding/circuit/matching self-test has 1,631 independent comparisons. Analytical checks include the 3,767 explicit leg lifts, nine independently matched negative noncritical examples, all 65,534 proper subsets of the strict circuit, 12,000 exact double-cover identities, and all 4,096 domain pairs of the strict 2-circuit `K6-2K2`.

No unrestricted statement should be submitted on the basis of these finite checks or partial lemmas. The remaining task is a complete unrestricted mathematical closure and then its Lean formalization. Neither original `sorry` has been filled.
