# Verified decomposition infrastructure

All declarations are in `Erdos184.DecompositionAux`, in
`Submission/DecompositionAux.lean`. This is auxiliary work only: **the uniform
linear bound and the main theorem remain unproved**. `Submission/Spec.lean`
was not modified, and neither of its unproved theorems is used.

## Results

- `edgePiece G e` has ambient edge set `{e}` and exactly one edge in its
  intrinsic graph `(edgePiece G e).coe`. The vertex set is the endpoints of `e`.
- `edgeDecomposition G` is a finite family indexed by `G.edgeSet`.
  `edgeDecomposition_isDecomposition` proves the actual spec's ambient edge-set
  partition condition. `edgeDecomposition_one_edge` and
  `edgeDecomposition_isCycleOrEdge` verify every piece.
- `edgeDecomposition_card` gives **exactly** `G.edgeFinset.card` pieces.
  `exists_one_edge_decomposition` bundles all these conclusions;
  `exists_decomposition_card_eq_edges` gives the shorter spec-shaped version.
  These require only `[Fintype V]`, with decidability supplied classically.
- `decompositionNumber G : ℕ` uses `Nat.find` over admissible decomposition
  cardinalities. `exists_minimum_decomposition` proves attainment;
  `decompositionNumber_le_card` proves minimality against any admissible family;
  `decompositionNumber_le_edgeFinset_card` supplies the elementary upper bound.
- `AsymptoticDecompositionBound` restates the original existential proposition
  without referencing its theorem. `UniformLinearDecompositionBound` states the
  existence of one `C : ℝ`, `0 < C`, such that every finite graph has some
  admissible decomposition of cardinality at most `C * Fintype.card V`.
  `asymptoticDecompositionBound_iff_uniformLinearDecompositionBound` proves their
  equivalence. The forward construction is `f n = C * n`; the reverse direction
  uses `Asymptotics.bound_of_isBigO_nat_atTop` and treats vertex count zero with
  `empty_isDecomposition_of_card_eq_zero`.

## Verification

The file compiles without errors or warnings with Lean 4.27.0. Its retained
`#print axioms` commands audit **all 25 declarations**, including definitions and
its private existence lemma. Every audit reports exactly
`[propext, Classical.choice, Quot.sound]`; none contains `sorryAx`. There are no
`sorry`, `admit`, or new axiom declarations, and no references to the unproved
theorem names.

Rebuild commands from `/workspace/leanproject` (the first compilation only
warns about the two pre-existing unproved statements in the unchanged spec):

```sh
mkdir -p .lake/build/lib/lean/Submission
lake env lean -o .lake/build/lib/lean/Submission/Spec.olean Submission/Spec.lean
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -o .lake/build/lib/lean/Submission/DecompositionAux.olean \
  Submission/DecompositionAux.lean
```

Additional compiled checks verified the edge-decomposition cardinalities of
complete graphs on 0, 2, and 3 vertices (0, 1, and 3), minimum zero for an edgeless
four-vertex graph, and definitional equality of the restated asymptotic
proposition with the explicit original existential formula. The conditional
forward lemma also directly elaborates against that explicit formula.

Unchanged spec SHA-256:
`429c12b5b471b0098bbc8ded194d7c22a4b99c083841d9a549f2bc3cc87dafde`.

## Library pitfalls

1. `H.edgeSet : Set (Sym2 V)` is ambient, but `H.coe.edgeFinset` uses
   `Sym2 H.verts`. The bridge `coe_edgeFinset_card` uses
   `Subgraph.image_coe_edgeSet_coe`, `Sym2.map.injective` (note the nested name),
   and `Set.ncard_image_of_injective`.
2. Indexing pieces by the subtype `G.edgeSet` avoids selecting endpoints or
   accidentally counting two orientations of an edge. Injectivity gives the
   exact cardinality via `Finset.card_image_of_injective`.
3. A `Set.PairwiseDisjoint` goal can retain `Function.onFun`; use `change
   Disjoint H.edgeSet K.edgeSet` before rewriting singleton edge sets.
4. `open scoped Classical` supplies the subtype `Fintype` instances required by
   the spec. Explicit/computable adjacency instances on concrete graphs can
   differ from classical instances hidden in `edgeFinset`; a rewrite may fail
   even when the printed terms look identical. In the complete-graph checks,
   an intermediate cardinality equality proved by `congr` and
   `Subsingleton.elim _ _` reconciled the instances.
5. `bound_of_isBigO_nat_atTop` supplies a global positive constant only where
   the comparison function is nonzero. For `g n = (n : ℝ)`, use it at `n ≠ 0`,
   pass through `Real.le_norm_self` and `Real.norm_natCast`, and independently
   choose the empty decomposition at `n = 0`. No bound on `f 0` is needed.
6. The proposition definitions quantify over `Type u`; the equivalence uses
   explicit `.{u}` so both sides concern the same vertex-type universe.

The edge-count bound can be quadratic in the vertex count. These results do
not supply the missing constant `C`, and no final spec imports or statements
have been changed.
