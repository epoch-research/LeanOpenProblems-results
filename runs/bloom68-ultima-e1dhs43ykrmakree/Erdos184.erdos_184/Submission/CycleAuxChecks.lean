import Submission.CycleAux

/-! Regression checks for the support lemmas, including empty graphs and subgraph transport. -/

open SimpleGraph
open scoped Classical

namespace Erdos184.CycleAux.Checks

open DecompositionAux

/-- Edgeless graphs, including the zero-vertex graph, need no cycle pieces. -/
theorem edgeless_check (n : ℕ) :
    ∃ D : Finset (⊥ : SimpleGraph (Fin n)).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (⊥ : SimpleGraph (Fin n)) D ∧ D.card = 0 := by
  obtain ⟨D, hcycles, _, hD, hcard⟩ :=
    exists_pure_cycle_decomposition (⊥ : SimpleGraph (Fin n)) (by
      intro v
      simp [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter])
  refine ⟨D, ?_, hD, ?_⟩
  · intro H hH
    refine ⟨(hcycles H hH).1, ?_⟩
    intro v
    simpa only [Subgraph.coe_degree] using (hcycles H hH).2 v
  · have hz : D.card ≤ 0 := by
      convert hcard using 1
      simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset,
        SimpleGraph.edgeSet_bot, Set.ncard_empty, Nat.zero_div]
    exact Nat.eq_zero_of_le_zero hz

/-- The complete graph on three vertices has a pure cycle decomposition of size at most one. -/
theorem triangle_check :
    ∃ D : Finset (⊤ : SimpleGraph (Fin 3)).Subgraph,
      (∀ H ∈ D, H.coe.Connected ∧ H.coe.IsRegularOfDegree 2) ∧
      IsDecomposition (⊤ : SimpleGraph (Fin 3)) D ∧ D.card ≤ 1 := by
  obtain ⟨D, hcycles, _, hD, hcard⟩ :=
    exists_pure_cycle_decomposition (⊤ : SimpleGraph (Fin 3)) (by
      intro v
      have hdeg : (⊤ : SimpleGraph (Fin 3)).degree v = 2 := by simp
      convert (show Even ((⊤ : SimpleGraph (Fin 3)).degree v) from by rw [hdeg]; decide) using 1
      congr 1
      exact Subsingleton.elim _ _)
  refine ⟨D, ?_, hD, ?_⟩
  · intro H hH
    refine ⟨(hcycles H hH).1, ?_⟩
    intro v
    simpa only [Subgraph.coe_degree] using (hcycles H hH).2 v
  · have hc : (⊤ : SimpleGraph (Fin 3)).edgeSet.ncard = 3 := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset,
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      decide
    convert hcard using 1
    simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, hc]

/-- A three-vertex path for checking union of pieces that share a vertex. -/
def threePath : SimpleGraph (Fin 3) where
  Adj a b := a ≠ b ∧ (a = 1 ∨ b = 1)
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless _ h := h.1 rfl

def leftEdge : threePath.Subgraph := edgePiece threePath ⟨s(0, 1), by simp [SimpleGraph.mem_edgeSet, threePath]⟩
def rightEdge : threePath.Subgraph := edgePiece threePath ⟨s(1, 2), by simp [SimpleGraph.mem_edgeSet, threePath]⟩

/-- The intrinsic decompositions of two incident edges really combine in the ambient graph. -/
theorem shared_vertex_union_check :
    ∃ D : Finset threePath.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition threePath D ∧ D.card ≤ 2 := by
  have hd : Disjoint leftEdge.edgeSet rightEdge.edgeSet := by
    simp [leftEdge, rightEdge]
  have hc : leftEdge.edgeSet ∪ rightEdge.edgeSet = threePath.edgeSet := by
    ext e
    induction e using Sym2.ind with
    | h a b =>
      fin_cases a <;> fin_cases b <;>
        simp [leftEdge, rightEdge, threePath]
  obtain ⟨D, hpieces, hD, hcard⟩ := exists_valid_decomposition_union_subgraphs leftEdge rightEdge
    (edgeDecomposition leftEdge.coe) (edgeDecomposition rightEdge.coe)
    (edgeDecomposition_isCycleOrEdge _) (edgeDecomposition_isCycleOrEdge _)
    (edgeDecomposition_isDecomposition _) (edgeDecomposition_isDecomposition _) hd hc
  refine ⟨D, hpieces, hD, ?_⟩
  simpa [leftEdge, rightEdge] using hcard

/-- Replacing the entire graph by an intrinsic decomposition uses the actual subtype transport. -/
theorem replacement_check {V : Type*} [Fintype V] (G : SimpleGraph V) :
    IsDecomposition G
      (({⊤} : Finset G.Subgraph).erase ⊤ ∪
        (edgeDecomposition (⊤ : G.Subgraph).coe).image (Subgraph.map (⊤ : G.Subgraph).hom)) := by
  apply isDecomposition_replace ({⊤} : Finset G.Subgraph)
    (by simp [IsDecomposition]) (by simp)
  exact edgeDecomposition_isDecomposition _

/-- The forest theorem also specializes to the zero-vertex case. -/
theorem zero_vertex_forest_check (G : SimpleGraph (Fin 0)) :
    ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧
      IsDecomposition G D ∧ D.card = 0 := by
  obtain ⟨D, hpieces, hD, hcard⟩ := exists_forest_decomposition G IsAcyclic.of_subsingleton
  exact ⟨D, hpieces, hD, by simpa using hcard⟩

/- Dependency audit for the regression checks. -/

#print axioms edgeless_check
#print axioms triangle_check
#print axioms threePath
#print axioms leftEdge
#print axioms rightEdge
#print axioms shared_vertex_union_check
#print axioms replacement_check
#print axioms zero_vertex_forest_check

end Erdos184.CycleAux.Checks
