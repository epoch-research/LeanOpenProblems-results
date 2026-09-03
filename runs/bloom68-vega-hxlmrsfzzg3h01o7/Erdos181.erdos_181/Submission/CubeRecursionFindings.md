# Hypercube Ramsey recursion investigation

## Outcome and scope

This investigation does **not** prove or disprove the assertion that there is an absolute C with R(Q_n) <= C 2^n. It does give standalone Lean-checked gluing and recurrence lemmas, and explicit counterexamples to several tempting recursive shortcuts. No recurrence with the required error bounds has been established for the actual Ramsey numbers.

`Submission/Spec.lean` was not modified and is not imported by the new Lean file. Its SHA-256 is `9cb89c42b7983ce8600b21cf6ffe9861fee7d6baca58206d9fa2d51c0636203b`.

The new file is `Submission/CubeRecursionInvestigation.lean`, in namespace `CubeRecursionInvestigation`. It uses Mathlib's `SimpleGraph.Copy` and `IsContained`, i.e. injective, noninduced containment. It contains no `sorry`, new axioms, `native_decide`, or use of either opposed placeholder theorem from Spec.

## Lean-checked results

Run:

```sh
lake env lean Submission/CubeRecursionInvestigation.lean
```

The complete file compiles without errors or warnings. The principal declarations are:

- `hypercube_cons_adj`, `cubeSuccIso`: the exact Cartesian-product decomposition K_2 box Q_n is isomorphic to Q_(n+1).
- `copyBoxOfCopies`: disjoint labelled copies of G indexed by H give a copy of H box G when every required matching between corresponding labels is present.
- `cubeCopySucc`: two disjoint red Q_n copies plus **label-compatible** red matching edges give a red Q_(n+1).
- `liftMatchedCube`: a red matching indexed by a set I lifts a Q_n in the intersection of the two transported red graphs to a red Q_(n+1).
- `doubling_recurrence_bound`, `doubling_recurrence_bounded_error`, `doubling_recurrence_summable`: precise normalized additive-error estimates.
- `halving_recurrence_normalized_bound`: a dimension-halving recurrence tolerates normalized A/n errors.
- `harmonicGrowth_recurrence`, `harmonicGrowth_relative_error_tends_to_zero`, `harmonicGrowth_not_bounded`: a counterexample to inferring a linear bound from little-o additive error alone.
- `copy_reflects_adj_at_of_degree_eq`: an injective homomorphism reflects adjacency at a vertex whose source and target degrees agree.
- `arbitrary_matching_not_sufficient`: two red Q_2 copies and a red perfect matching need not give a red Q_3.
- `arbitrary_matching_not_sufficient_even_two_colors`: the same hypotheses do not even force a Q_3 in either color.
- `union_does_not_preserve_cube_freeness`: two Q_2-free graphs can have a union containing Q_2.

Axiom audits of the principal declarations give only `propext`, `Classical.choice`, and `Quot.sound`. The finite graph checks use kernel-evaluated `decide`, not native reduction axioms.

## 1. An explicit obstruction even to an either-color gluing conclusion

On vertices 0,...,7, make precisely these 13 edges red (all other edges blue):

```
01 03 05 06 12 14 23 26 37 45 47 56 67
```

There are two disjoint red squares:

```
0-1-2-3-0       4-5-6-7-4
```

and the red perfect matching

```
0-5, 1-4, 2-6, 3-7.
```

Nevertheless neither color contains Q_3, with the intended noninduced convention.

**No red Q_3.** Red degrees are 4 at 0 and 6 and 3 everywhere else. Any Q_3 uses all eight vertices, has 12 edges, and is 3-regular. The only possible edge to omit from the 13-edge red graph is 06. But the graph remaining after deleting 06 has the odd cycle 0-1-2-6-5-0, whereas Q_3 is bipartite. Thus it is not Q_3. The Lean proof uses local degree saturation to force this odd cycle into the putative copy, rather than relying on an induced-containment argument.

**No blue Q_3.** In blue,

```
N(0) = {2,4,7},     N(6) = {1,3,4}.
```

Both vertices have blue degree 3, so their full neighborhoods would be used by a spanning Q_3. They have exactly one common neighbor, 4. But two distinct vertices of Q_3 have either zero or two common neighbors, never exactly one. Contradiction.

This example is fully formalized by `arbitrary_matching_not_sufficient_even_two_colors`. It refutes the local gluing rule, **not** the existence of an absolute Ramsey constant.

## 2. Exact characterization of pure twisted-cube gluing (paper proof)

Let m >= 2, let p be a permutation of V(Q_m), and let T_p consist of exactly two disjoint copies of Q_m plus the matching x_left -- p(x)_right. Then

> T_p contains Q_(m+1) if and only if p is an automorphism of Q_m.

Proof: both graphs have 2^(m+1) vertices and are (m+1)-regular. Consequently any injective homomorphism Q_(m+1) -> T_p is an isomorphism; noninduced containment does not weaken this conclusion. Let P(p) be the number of Q_m edges xy for which p(x)p(y) is also an edge. Every 4-cycle of T_p either lies in a layer, or uses exactly two matching edges. Thus

```
number of C4's in T_p = 2 * binom(m,2) * 2^(m-2) + P(p).
```

The number in Q_(m+1) is `binom(m+1,2) * 2^(m-1)`. Equality forces `P(p) = m * 2^(m-1)`, so p preserves every edge and, being a permutation of a finite graph, is an automorphism. The converse is label-compatible gluing.

Even requiring the twisted graph to be bipartite is insufficient. For m=3, swap 000 and 110 and fix every other label. This permutation preserves parity but loses two of Q_3's twelve edges. T_p is bipartite and has 22 four-cycles, whereas Q_4 has 24. Hence it has no Q_4. This general characterization is proved above on paper, not formalized in the Lean file. The C4 identity was additionally checked on all 24 permutations for m=2 and a fixed random sample of 100 permutations for m=3.

## 3. What matching compression actually preserves

Given disjoint injections l,r:I -> V(G) with all l(i)r(i) red, define the auxiliary red graph by

```
A(i,j) iff G_red(l(i),l(j)) AND G_red(r(i),r(j)).
```

A red Q_m in A gives a red Q_(m+1) in G; this is `liftMatchedCube`.

The auxiliary blue graph, however, is the **union** of the two transported blue graphs. A blue auxiliary edge can be witnessed in different layers for different edges of a cube. There is no valid same-color lifting lemma on this side.

The smallest obstruction is B_0={01,23}, B_1={03,12}. Each is a matching and hence Q_2-free, but their union is Q_2. This is formalized by `union_does_not_preserve_cube_freeness`.

There is a stronger general obstruction (paper proof): **for every m, Q_m is a union of two C4-free graphs.** Color the edge between subsets S and S union {i} according to the parity of |S|. Each square uses two consecutive lower weights k and k+1, hence both colors. Every 4-cycle in a hypercube is such a square. Therefore neither color contains C4, and thus neither contains any Q_n with n>=2, even though their union contains an arbitrarily high-dimensional cube. So increasing the dimension of the auxiliary blue cube alone cannot repair witness consistency.

### A valid dense-layer sufficient condition (paper proof)

For a graph F on h vertices of maximum degree d, a red graph on N vertices whose blue complement has maximum degree D contains F whenever `N >= h + d D`. Embed vertices greedily: at most h-1 vertices are already used, and each of at most d already embedded neighbors excludes at most D additional candidates.

Consequently, in the matched-pair setting with q pairs, if the two transported blue graphs have maximum degrees D_0 and D_1, then

```
q >= 2^m + m (D_0 + D_1)
```

is sufficient for a red Q_(m+1). The missing-degree condition on the auxiliary intersection follows by a union bound. This is a genuine condition, but two merely red cube copies do not imply it.

Another elementary sufficient condition for two fixed labelled red Q_m copies is fewer than 2^m blue cross-edges: the 2^m translation matchings x -> x+t partition all cross-edges, so one translation matching is entirely red. This too is far stronger than the existence of an arbitrary red perfect matching.

## 4. Exact amortized-error accounting

Suppose `r_(n+1) <= 2 r_n + e_n`. The Lean theorem proves

```
r_n <= 2^n * (r_0 + sum_{k=0}^{n-1} e_k / 2^(k+1)).
```

Thus bounded cumulative normalized errors suffice. For nonnegative errors, summability of `e_k / 2^(k+1)` gives the desired uniform coefficient. For example, errors `O(2^n/n^(1+epsilon))`, epsilon>0, would suffice. No such estimate for the true cube Ramsey numbers was proved here.

Little-o alone is insufficient. Set

```
r_n = 2^n (1 + H_n),    H_n = sum_{k=1}^n 1/k.
```

Then

```
r_(n+1) = 2 r_n + 2^(n+1)/(n+1),
```

so the relative error tends to zero but r_n/2^n diverges. This is fully formalized.

An integer-valued version, proved on paper, is

```
a_0=1,
a_(n+1)=2 a_n + floor(2^(n+1)/(n+1)).
```

Dividing through and summing yields

```
H_n + 2^(-n) <= a_n/2^n <= 1 + H_n.
```

The lower bound uses `floor(x) >= x-1` and a geometric sum. Hence integrality does not rescue the little-o implication.

Even the raw all-dimension recurrence `R(Q_n) <= 2 R(Q_(n-1))` is false: R(Q_1)=2, while coloring K_5 as a red C_5 and its blue complementary C_5 gives R(Q_2)>=6.

### A dimension-halving alternative

The Lean theorem `halving_recurrence_normalized_bound` proves that, for A>=0,

```
a_n <= a_floor(n/2) + A/n  (n>=2)
```

implies

```
a_n <= a_1 + A(1-1/n)  (n>=1).
```

The induction uses `2 floor(n/2) <= n`. Applied to `a_n=r_n/2^n`, it would be enough to prove the combinatorial recurrence

```
r_n <= 2^(n-floor(n/2)) r_floor(n/2) + A 2^n/n.
```

No such recurrence is claimed for Ramsey numbers. The observation is that errors not summable over every dimension can be summable along geometric scales. More generally, paper induction gives a uniform normalized budget A/(2^alpha-1) for A/n^alpha errors along halving chains, for every alpha>0.

## 5. Corpus evidence and the missing hypothesis

Relevant source:

`/corpus/src/1306.0461/1306.0461.tex`

G. Fiz Pontiveros, S. Griffiths, R. Morris, D. Saxton, J. Skokan, *The Ramsey number of the clique and the hypercube*, arXiv:1306.0461.

- Lines 32--41 explicitly distinguish the diagonal hypercube conjecture from their result `r(K_s,Q_n)=(s-1)(2^n-1)+1` for `n>=n_0(s)`.
- Lines 179--185 give their dense-red embedding proposition. It assumes no blue K_s, a small blue maximum degree, and `s <= log_(k+1)(n)`.
- Lines 443--456 use matching compression exactly as above. The phrase "as in Proposition ..." in their matching example includes the internal blue-degree conditions; it is not a matching-only assertion.

Why their forbidden-clique information transfers: a blue K_{R(s)} in the auxiliary union has each edge witnessed in one of two layers. Ordinary clique Ramsey theory finds a K_s with all witnesses in the same layer, contradicting the original blue K_s prohibition. With 2^m layers the corresponding parameter is the 2^m-color clique Ramsey number.

Absence of a blue Q_n does not imply absence of a fixed blue K_s. A blue clique of size 2^n-1 is already a counterexample to that implication. The automatic forbidden clique has size 2^n, not a fixed s. Nor may the eventual fixed-H theorem be specialized to H=Q_n while silently assuming `n>=n_0(Q_n)`; this is exactly the missing uniformity.

Internet access failed, so no claim is made that this corpus search certifies the latest literature status.

## What remains unsupported

- A way to extract enough *simultaneously label-compatible* cube copies with only a summable normalized loss.
- An auxiliary invariant that survives matching compression and treats both colors, rather than merely a forbidden-cube condition on each transported graph.
- Either of the stated sufficient one-step or halving recurrences for the actual Ramsey numbers.
- A family of countercolorings with R(Q_n)/2^n unbounded.

These are substantive combinatorial gaps, not Lean syntax gaps. The finite counterexamples above are not counterexamples to the absolute-C conjecture.
