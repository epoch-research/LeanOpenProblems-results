# Verified cycle/decomposition support

New declarations are in `Erdos184.CycleAux`, in `Submission/CycleAux.lean`,
importing the unchanged `Submission.DecompositionAux`. All requested support
goals, including the optional finite-even-graph result, are proved. **This does
not prove Erdős 184 or a uniform linear bound for general graphs.**

## Main results

- `cycle_toSubgraph_isCycleOrEdge`: for `[Fintype V]`, `hp : p.IsCycle`
  gives `IsCycleOrEdge p.toSubgraph.coe`. The proof uses
  `toSubgraph_connected`, `ncard_neighborSet_toSubgraph_eq_two`, and
  `Subgraph.coe_degree`. The separate regularity lemma gives degree two.
  `trail_toSubgraph_edgeSet_ncard` identifies the ambient edge count with walk
  length; a cycle therefore has at least three edges.
- `subgraphMapIso f hf H` is an explicit intrinsic graph isomorphism
  `H.coe ≃g (H.map f).coe` for an injective homomorphism `f`.
  `isCycleOrEdge_map` transports validity.
- `EdgePartition D s` partitions a specified set of **ambient** edges and agrees
  definitionally with `IsDecomposition G D` when `s = G.edgeSet`. Its `map`,
  `union`, and `erase` lemmas handle transport and finite recombination.
  `edgePartition_map_subgraph` maps a decomposition of `H.coe` to `H.edgeSet`
  using `H.hom` and `Sym2.map Subtype.val`, not an identification of the two
  edge types.
- `isDecomposition_union_subgraphs` combines intrinsic decompositions of
  edge-disjoint `H K : G.Subgraph` whose edge sets cover `G`. Its valid-piece
  wrapper `exists_valid_decomposition_union_subgraphs` gives size
  `≤ D.card + E.card`. **Vertices may overlap.**
- `isDecomposition_replace` replaces `H ∈ D` by an intrinsic decomposition `E`
  using `D.erase H ∪ E.image (Subgraph.map H.hom)`.
  `exists_valid_decomposition_replace` preserves valid pieces and gives size
  `≤ D.card - 1 + E.card`.
  `isDecomposition_insert_deleteEdges` supplies the cycle-removal/reinsertion
  specialization, explicitly lifting residual subgraphs along `Hom.ofLE`.
- `forest_edgeFinset_card_lt` proves `m < n` for a forest on a nonempty finite
  vertex type by extending it to a spanning tree of the complete graph.
  `forest_edgeFinset_card_le_card_sub_one` gives `m ≤ n - 1` with natural
  subtraction, including `n = 0`. `exists_forest_decomposition` uses the existing
  individual-edge construction to give the spec's valid decomposition with
  `D.card ≤ Fintype.card V`. The minimum satisfies
  `decompositionNumber_le_card_of_isAcyclic`.
- `exists_cycle_walk_decomposition_of_even_degrees G heven`, where
  `heven : ∀ v, Even (G.degree v)`, produces an ambient decomposition `D`,
  an actual simple cyclic walk witnessing every member of `D`, and
  `3 * D.card ≤ G.edgeFinset.card`.
  `exists_pure_cycle_decomposition` also states that every intrinsic piece is
  connected and 2-regular, is `IsCycleOrEdge`, and that
  `D.card ≤ G.edgeFinset.card / 3`.
  `decompositionNumber_le_edges_div_three_of_even_degrees` bounds the minimum.

The even-graph proof is strong induction on the finite edge count. A finite
acyclic even graph is edgeless: restrict to its support and combine the strict
forest bound with the degree-sum formula. Thus every non-edgeless even graph has
a cycle. Removing it subtracts degree two on its vertices and zero elsewhere,
preserves even degrees, and removes at least three edges. No Euler-tour
existence statement is assumed or used. Isolated vertices and disconnected
ambient graphs are allowed. The bound `m/3` can be quadratic in `n`.

## Verification and reuse

- All **35** core declarations have retained `#print axioms` commands. Every
  axiom set is a subset of `{propext, Classical.choice, Quot.sound}`; no
  `sorryAx`, admissions, or new axioms occur, and neither unproved spec theorem
  is referenced.
- `Submission/CycleAuxChecks.lean` contains **8** separately audited declarations:
  edgeless graphs on `Fin n`, a triangle with at most one cycle piece, union of
  the two edges of a three-vertex path (sharing a vertex), replacement of the
  top subgraph by its intrinsic edge decomposition, and the zero-vertex forest
  case. Core and checks compile without errors or warnings.
- Degree/cardinality instances can be propositionally equal but not
  definitionally equal after specializing a graph or subtype. Normalize
  intrinsic degrees with `Subgraph.coe_degree`; normalize edge counts with
  `← Set.ncard_coe_finset` and `SimpleGraph.coe_edgeFinset`. The induction also
  explicitly reconciles `Fintype` instances via `Subsingleton.elim`.

Rebuild from `/workspace/leanproject` (the first command may warn about the two
pre-existing unproved spec statements; the other files have no such warnings):

```sh
mkdir -p .lake/build/lib/lean/Submission
lake env lean -o .lake/build/lib/lean/Submission/Spec.olean Submission/Spec.lean
for file in DecompositionAux CycleAux CycleAuxChecks; do
  lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
    -o .lake/build/lib/lean/Submission/$file.olean Submission/$file.lean
done
```

Protected source SHA-256 values, unchanged from before this work:

- `Spec.lean`: `429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde`
- `DecompositionAux.lean`: `61cc5acfb2b84bf7cb4b46db6453f9037faabb2bb2c70165cf265bdff6b985de`
