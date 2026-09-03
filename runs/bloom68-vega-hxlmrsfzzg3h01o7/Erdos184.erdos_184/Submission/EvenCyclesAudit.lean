import Submission.EvenCycles

/-!
# Audit of pure-cycle existence and the conditional equivalences

The expanded main statement checks the precise `Finset G.Subgraph` edge-disjoint
cover and the natural-number `|E| / 3` bound. Boundary checks cover edgeless graphs
(with any number of isolated vertices), a single edge, and a triangle.

The printed axiom reports cover every public declaration in `EvenCycles.lean`
and every theorem here. The executable audit additionally traverses **all**
declarations in the namespace and rejects any transitive axiom dependency other
than `propext`, `Classical.choice`, or `Quot.sound`.

The uniform bounds remain hypothetical. Neither this file nor `EvenCycles.lean`
asserts a linear vertex-count bound or references either admitted proof in Spec.
-/

open SimpleGraph

namespace Erdos184.EvenCycles.Audit
universe u
variable {V : Type u} [Fintype V]

open scoped Classical in
/-- The main theorem has exactly the requested edge-disjoint-cover statement, expanded. -/
theorem exact_pureCycle_statement (G : SimpleGraph V) (hG : ∀ v, Even (G.degree v)) :
    ∃ D : Finset G.Subgraph,
      (∀ S ∈ D, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun S => S.edgeSet) ∧
      (⋃ S ∈ D, S.edgeSet) = G.edgeSet ∧
      D.card ≤ G.edgeFinset.card / 3 := by
  obtain ⟨D, hpieces, hD, hcard⟩ := exists_pureCycle_decomposition G hG
  exact ⟨D, hpieces, hD.1, hD.2, hcard⟩

open scoped Classical in
/-- The existence theorem returns no pieces for an edgeless graph, even with isolated vertices. -/
theorem bot_has_empty_decomposition :
    ∃ D : Finset (⊥ : SimpleGraph V).Subgraph,
      (∀ S ∈ D, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2) ∧
      IsDecomposition ⊥ D ∧ D = ∅ := by
  classical
  obtain ⟨D, hpieces, hD, hcard⟩ := exists_pureCycle_decomposition (⊥ : SimpleGraph V) (by
    intro v
    have hv : Even ((⊥ : SimpleGraph V).degree v) := by simp
    convert hv using 1
    congr!)
  refine ⟨D, ?_, hD, Finset.card_eq_zero.mp ?_⟩
  · intro S hS
    refine ⟨(hpieces S hS).1, ?_⟩
    convert (hpieces S hS).2 using 1
  · have hcard' : D.card ≤ (⊥ : SimpleGraph V).edgeFinset.card / 3 := by
      convert hcard using 1
      congr!
    simpa using hcard'

set_option maxHeartbeats 800000 in
open scoped Classical in
/-- The characterization rules out a pure-cycle decomposition of a single edge. -/
theorem no_pureCycle_decomposition_single_edge :
    ¬ ∃ D : Finset (⊤ : SimpleGraph (Fin 2)).Subgraph,
      (∀ S ∈ D, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2) ∧
      IsDecomposition ⊤ D := by
  classical
  rintro ⟨D, hpieces, hD⟩
  have heven := (even_iff_exists_pureCycle_decomposition (⊤ : SimpleGraph (Fin 2))).mpr
    ⟨D, by
      intro S hS
      refine ⟨(hpieces S hS).1, ?_⟩
      convert (hpieces S hS).2 using 1, hD⟩
  have heven0 : Even ((⊤ : SimpleGraph (Fin 2)).degree 0) := by
    convert heven 0 using 1
    congr!
  simp at heven0

set_option maxHeartbeats 800000 in
open scoped Classical in
/-- On a triangle the bound is attained: the resulting decomposition has one cycle. -/
theorem triangle_has_one_cycle :
    ∃ D : Finset (⊤ : SimpleGraph (Fin 3)).Subgraph,
      (∀ S ∈ D, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2) ∧
      IsDecomposition ⊤ D ∧ D.card = 1 := by
  classical
  obtain ⟨D, hpieces, hD, hcard⟩ := exists_pureCycle_decomposition (⊤ : SimpleGraph (Fin 3)) (by
    intro v
    have hv : Even ((⊤ : SimpleGraph (Fin 3)).degree v) := by simp
    convert hv using 1
    congr!)
  have hcard' : D.card ≤ (⊤ : SimpleGraph (Fin 3)).edgeFinset.card / 3 := by
    convert hcard using 1
    congr!
  have hthree : (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 3 := by
    convert card_edgeFinset_top_eq_card_choose_two (V := Fin 3) using 1
  have hupper : D.card ≤ 1 := by
    simpa only [hthree] using hcard'
  have he : s((0 : Fin 3), 1) ∈ ⋃ S ∈ D, S.edgeSet := by
    rw [hD.2]
    simp
  simp only [Set.mem_iUnion] at he
  obtain ⟨S, hS, _⟩ := he
  have hpos : 0 < D.card := Finset.card_pos.mpr ⟨S, hS⟩
  refine ⟨D, ?_, hD, by omega⟩
  intro T hT
  refine ⟨(hpieces T hT).1, ?_⟩
  convert (hpieces T hT).2 using 1
end Erdos184.EvenCycles.Audit

#print axioms Erdos184.EvenCycles.eq_bot_of_even_isAcyclic
#print axioms Erdos184.EvenCycles.pureCycle_toSubgraph
#print axioms Erdos184.EvenCycles.card_edges_toSubgraph_of_isTrail
#print axioms Erdos184.EvenCycles.isDecomposition_insert_liftPieces
#print axioms Erdos184.EvenCycles.exists_pureCycle_decomposition
#print axioms Erdos184.EvenCycles.exists_pureCycle_decomposition_card_le_edges
#print axioms Erdos184.EvenCycles.piecesGraph
#print axioms Erdos184.EvenCycles.piecesGraph_le
#print axioms Erdos184.EvenCycles.piecesGraph_edgeSet
#print axioms Erdos184.EvenCycles.piecesGraph_eq_of_isDecomposition
#print axioms Erdos184.EvenCycles.degree_sup_of_disjoint
#print axioms Erdos184.EvenCycles.even_degree_spanningCoe_of_regular
#print axioms Erdos184.EvenCycles.even_degree_piecesGraph
#print axioms Erdos184.EvenCycles.card_edges_piecesGraph_le
#print axioms Erdos184.EvenCycles.isDecomposition_union_complement
#print axioms Erdos184.EvenCycles.liftPieces_pureCycle
#print axioms Erdos184.EvenCycles.complement_piecesGraph_eq
#print axioms Erdos184.EvenCycles.even_iff_exists_pureCycle_decomposition
#print axioms Erdos184.EvenCycles.purify_decomposition
#print axioms Erdos184.EvenCycles.UniformEvenPureCycleBound
#print axioms Erdos184.EvenCycles.uniform_even_linear_bound_iff_pureCycle_bound
#print axioms Erdos184.EvenCycles.asymptotic_iff_uniform_even_pureCycle_bound
#print axioms Erdos184.EvenCycles.uniform_linear_bound_iff_uniform_even_pureCycle_bound
#print axioms Erdos184.EvenCycles.Audit.exact_pureCycle_statement
#print axioms Erdos184.EvenCycles.Audit.bot_has_empty_decomposition
#print axioms Erdos184.EvenCycles.Audit.no_pureCycle_decomposition_single_edge
#print axioms Erdos184.EvenCycles.Audit.triangle_has_one_cycle

run_cmd do
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut audited := 0
  for (name, _) in (← Lean.getEnv).constants.toList do
    if (`Erdos184.EvenCycles).isPrefixOf name then
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      audited := audited + 1
  Lean.logInfo m!"Allowed-axiom audit passed for {audited} declarations in Erdos184.EvenCycles."

#check @Erdos184.EvenCycles.exists_pureCycle_decomposition
#check @Erdos184.EvenCycles.exists_pureCycle_decomposition_card_le_edges
#check @Erdos184.EvenCycles.even_iff_exists_pureCycle_decomposition
#check @Erdos184.EvenCycles.purify_decomposition
#check @Erdos184.EvenCycles.uniform_even_linear_bound_iff_pureCycle_bound
#check @Erdos184.EvenCycles.asymptotic_iff_uniform_even_pureCycle_bound
#check @Erdos184.EvenCycles.uniform_linear_bound_iff_uniform_even_pureCycle_bound
#check @Erdos184.EvenCycles.Audit.exact_pureCycle_statement
