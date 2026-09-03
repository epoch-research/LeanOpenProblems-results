# Verified bipartite-host Erdős–Sós theorem

## Status and scope

**Complete Lean proof for finite bipartite hosts. This is not a proof of the unrestricted Erdős–Sós conjecture.**

`Submission/Bipartite.lean` imports only `FormalConjecturesUtil`. It does not import or use `Submission.Spec`, `Submission.Auxiliary`, or `Submission.Critical`. The elementary induced-subgraph isomorphism and subsingleton-copy helper are copied into its own namespace; the leaf induction is adapted to preserve a prescribed bipartition.

All three protected source files remain byte-for-byte unchanged.

## Main result

The principal theorem is:

```lean
Erdos548.Bipartite.tree_isContained_of_bipartite_edge_threshold
    {A : Type u} {V : Type v} [Finite A] [Finite V]
    (T : SimpleGraph A) (G : SimpleGraph V) (k : ℕ)
    (hcard : Nat.card A = k + 1) (hT : T.IsTree) (hB : G.IsBipartite)
    (hG : ((k : ℚ) - 1) / 2 * Nat.card V < (G.edgeSet.ncard : ℚ)) :
    T.IsContained G
```

Thus the target and host may have arbitrary, differently sized finite vertex types, even in different universes. Containment is an ordinary `SimpleGraph.Copy`, not an induced embedding. The coefficient uses rational subtraction, so it is `-1/2` at `k = 0`.

Two convenient specializations are also proved:

* `Erdos548.Bipartite.fin_tree_isContained_of_bipartite_edge_threshold`: host `Fin n`, target `Fin (k + 1)`, strict rational threshold.
* `Erdos548.Bipartite.erdos_548_bipartite`: the specification's `k + 1 ≤ n` and `((k : ℚ) - 1) / 2 * n + 1 ≤ e(G)` hypotheses, **with the added hypothesis that the host is bipartite**.

The strict theorem does not need a separate `k + 1 ≤ |V|` assumption: its proof constructs the required injection. It also does not assume a nonempty host; nonemptiness follows from the strict edge threshold.

## Formal proof structure

The proof follows `all_orders_collision.md`, §6.1.

1. **Total Boolean colorings.** Mathlib's `IsTree.isBipartite` and the bipartite-host hypothesis provide proper Boolean colorings of all vertices, including isolated host vertices. A nontrivial tree has an edge, so both its colors occur.

2. **Choose an orientation.** Write `q(b)` for the number of target vertices whose color differs from `b`. For `k > 0`, both counts are positive and `q(false) + q(true) = k + 1`. Give a host vertex `v` cost `q(cG(v)) - 1`. Reversing the host coloring gives the other orientation. Pointwise, the two costs sum to `k - 1`; hence their total costs sum to `(k - 1) * |V|`. The strict rational edge threshold forces at least one total cost to be smaller than `e(G)`. Positivity of both classes justifies all natural-number subtractions. Ordering the two target class sizes is unnecessary.

3. **Weighted peeling.** `exists_weighted_core` proves, for arbitrary nonnegative integer vertex costs and any finite graph, that
   ```lean
   (∑ v, cost v) < G.edgeSet.ncard
   ```
   yields a nonempty induced vertex set `s` such that every vertex of `G.induce s` has degree strictly larger than its original cost. Strong induction deletes any vertex of degree at most its cost. The exact identity
   ```lean
   e(G - v) + degree_G(v) = e(G)
   ```
   ensures each deleted edge is charged exactly once. Nested induced subgraphs are flattened by an explicit isomorphism. For the chosen bipartite costs, the resulting degree bound is at least the full opposite target class size.

4. **Color-preserving greedy tree embedding.** `exists_color_preserving_copy_of_degree` removes a leaf and embeds the remaining tree into the same host with the same degree bounds. Only already used vertices of the required color can block a neighbor. Removing the leaf strictly decreases that class size, so a fresh neighbor exists. The copy remains injective, preserves every target edge, and respects both color classes. No induced-edge condition is claimed. The core has an edge and therefore both host colors occur, as required by the greedy lemma.

5. **The case `k = 0`.** The edge threshold still forces a nonempty host, even though its coefficient is negative. The target is a subsingleton, so a constant map gives the required injective copy. This case does not use positive color-class sizes or the peeling argument.

## Reusable interfaces

Besides the final theorem, the file supplies:

* `exists_weighted_core`: arbitrary natural vertex costs; no bipartiteness assumption.
* `exists_color_preserving_copy_of_degree`: finite enumerated types and degree bounds.
* `exists_color_preserving_copy_of_neighborSet_ncard`: only `Finite` instances, with the hypothesis
  ```lean
  ∀ v, Nat.card {x : A // cT x ≠ cG v} ≤ (G.neighborSet v).ncard
  ```
  and conclusion `∃ f : T.Copy G, ∀ x, cG (f x) = cT x`. The host coloring is assumed surjective, and the target is a tree.
* `isContained_of_coloring_cost_lt`: containment from a positive weighted surplus in a fixed orientation.
* `exists_orientation_cost_lt`: the rational averaging/orientation step.

The JSON verification artifact contains the complete declaration and axiom inventory.

## Verification

Both source files compile with Lean **4.27.0**, with no errors or warnings:

```bash
cd /workspace/leanproject
mkdir -p .lake/build/lib/lean/Submission
lake env lean -o .lake/build/lib/lean/Submission/Bipartite.olean \
  -i .lake/build/lib/lean/Submission/Bipartite.ilean Submission/Bipartite.lean
lake env lean -o .lake/build/lib/lean/Submission/BipartiteVerification.olean \
  -i .lake/build/lib/lean/Submission/BipartiteVerification.ilean \
  Submission/BipartiteVerification.lean
lake env lean --deps Submission/Bipartite.lean
lake env lean --deps Submission/BipartiteVerification.lean
```

`Bipartite.lean` audits all **22 theorem declarations** (including one private helper) and its one isomorphism definition with `#print axioms`. Every transitive dependency uses only `propext`, `Classical.choice`, and `Quot.sound`, or a subset of these. The subsingleton-copy theorem uses no axioms. There is no `sorryAx`, proof hole, newly declared axiom, or native-evaluation shortcut.

`BipartiteVerification.lean` contains **11 compiled interface/boundary examples**:

1. The arbitrary-finite-type theorem produces an ordinary copy.
2. The greedy finite-only theorem preserves prescribed colors.
3. The general weighted-core interface.
4. The strict `Fin n` theorem without a separate host-size assumption.
5. The specification-style `+1` threshold for bipartite hosts.
6. The edgeless singleton at `k = 0` satisfies the negative strict threshold.
7. No empty host satisfies the strict threshold, for any `k`.
8. A one-vertex target cannot embed in an empty host.
9. At `k = 1`, the one-edge host suffices.
10. At `k = 2`, the one-edge host is exactly at the threshold and cannot contain a three-vertex target: strictness matters.
11. The nonregular host `K₂,₃`, with `6 > 5` edges relative to the `k = 3` threshold, contains every four-vertex tree on arbitrary finite labels.

Concrete finite counts in the tests use ordinary kernel-checked `decide` and the degree-sum identity.

## Artifacts and integrity

* `Submission/Bipartite.lean` — self-contained bipartite-host proof and axiom audits.
* `Submission/BipartiteVerification.lean` — compiled interface/boundary checks.
* `Submission/Bipartite.verification.log` — compiler output, dependencies, and integrity checks.
* `Submission/Bipartite.verification.json` — machine-readable results and axiom inventory.
* `Submission/Bipartite.report.md` — this report.
* Matching `.olean` and `.ilean` files in `.lake/build/lib/lean/Submission/`.

Source SHA256:

* `Bipartite.lean`: `721a5e1930bbee5bf22e5d2b4c9c068f3f46218ae2e987e0668e24f4cc213f1d`
* `BipartiteVerification.lean`: `ffbec3191a9e4fccc64e361dcc3aba29d0c6628c943f03f7e411afb9cf8bc123`

Protected files' original and final SHA256 values agree:

* `Submission/Spec.lean`: `674e59904bc58eb7e92883f5bf20dc5070fa9ec90e1640117895768922c0c103`
* `Submission/Auxiliary.lean`: `227fcc37cac1313bd1d9c8033397195fa990f018c784ba9a53e307f6ef1e28c1`
* `Submission/Critical.lean`: `c0dc0d37acc9f1ca3173b6d144e326ccfcbf5a63eb98216fa6099e055b9d71ea`

Nothing here settles the unrestricted conjecture for nonbipartite hosts.
