import Submission.OptimalCycles

/-!
# Audit of the optimal-cycle infrastructure

The checks below expand the minimum and the fixed-order sufficiency theorem into
original connected/2-regular subgraphs and pairwise edge-disjoint edge covers.
Boundary checks retain arbitrary isolated vertices, include vertex order zero,
rule out evenness of a single edge, and compute the triangle minimum.

Every declaration in `Erdos184.OptimalCycles`, including generated auxiliaries
and these checks, is audited transitively against the whitelist `propext`,
`Classical.choice`, `Quot.sound`. No admitted target proof is referenced.
The OC linear bound remains a hypothesis, never an asserted bound.
-/

open SimpleGraph

namespace Erdos184.OptimalCycles

open EvenCycles EvenReduction
open scoped Classical

universe u
variable {V : Type u} [Fintype V]

/-- The attained minimum is over the exact original edge-disjoint-cover predicate. -/
theorem audit_exact_attained_minimum (G : SimpleGraph V) (hG : IsEven G) :
    ∃ D : Finset G.Subgraph,
      (∀ S ∈ D, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun S => S.edgeSet) ∧
      (⋃ S ∈ D, S.edgeSet) = G.edgeSet ∧
      D.card = minCycleCount G hG ∧
      ∀ P : Finset G.Subgraph,
        (∀ S ∈ P, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2) →
        IsDecomposition G P → D.card ≤ P.card := by
  obtain ⟨D, hD, hcard⟩ := exists_optimal G hG
  refine ⟨D, hD.1, hD.2.1, hD.2.2, hcard, ?_⟩
  intro P hP hcover
  rw [hcard]
  exact minCycleCount_le_card hG ⟨hP, hcover⟩

/-- Hereditary optimality keeps the original pieces exactly when lifted back. -/
theorem audit_exact_subfamily {G : SimpleGraph V} {hG : IsEven G}
    {D C : Finset G.Subgraph} (hD : IsOptimal hG D) (hCD : C ⊆ D) :
    liftPieces (piecesGraph_le C) (piecesOnUnion C) = C ∧
      IsOptimal (even_subfamily hD.1 hCD) (piecesOnUnion C) ∧
      minCycleCount (piecesGraph C) (even_subfamily hD.1 hCD) = C.card :=
  ⟨liftPieces_piecesOnUnion C, hD.subfamily hCD, minCycleCount_subfamily hD hCD⟩

/--
Fully expanded fixed-order sufficiency: every original cycle is in some optimum
in the hypothesis, and the conclusion is an original pure-cycle decomposition.
Both quantifiers range over all graphs on the same `V`, including isolated vertices.
-/
theorem audit_fixed_order_sufficiency (K : ℝ)
    (hOC : ∀ G : SimpleGraph V, ∀ hG : IsEven G,
      (∀ S : G.Subgraph, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2 →
        ∃ D : Finset G.Subgraph,
          (∀ T ∈ D, T.coe.Connected ∧ T.coe.IsRegularOfDegree 2) ∧
          IsDecomposition G D ∧ D.card = minCycleCount G hG ∧ S ∈ D) →
      ∃ D : Finset G.Subgraph,
        (∀ T ∈ D, T.coe.Connected ∧ T.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ K * (Fintype.card V : ℝ))
    (G : SimpleGraph V) (hG : IsEven G) :
    ∃ D : Finset G.Subgraph,
      (∀ T ∈ D, T.coe.Connected ∧ T.coe.IsRegularOfDegree 2) ∧
      Set.PairwiseDisjoint (D : Set G.Subgraph) (fun T => T.edgeSet) ∧
      (⋃ T ∈ D, T.edgeSet) = G.edgeSet ∧
      (D.card : ℝ) ≤ K * (Fintype.card V : ℝ) := by
  have hbound : ∀ E : SimpleGraph V, ∀ hE : IsEven E, OC E hE →
      (minCycleCount E hE : ℝ) ≤ K * (Fintype.card V : ℝ) := by
    intro E hE hEO
    obtain ⟨D, hpieces, hD, hcard⟩ := hOC E hE (by
      intro S hS
      obtain ⟨P, hP, hSP⟩ := hEO S hS
      exact ⟨P, hP.1.1, hP.1.2, hP.2, hSP⟩)
    exact (show (minCycleCount E hE : ℝ) ≤ (D.card : ℝ) by
      exact_mod_cast minCycleCount_le_card hE ⟨hpieces, hD⟩).trans hcard
  obtain ⟨D, hD, hcard⟩ := pureCycle_bound_of_oc_linear_bound K hbound G hG
  exact ⟨D, hD.1, hD.2.1, hD.2.2, hcard⟩

/-- Any edgeless ambient graph has zero cost and OC, regardless of its isolated vertices. -/
theorem audit_edgeless_any_order :
    minCycleCount (⊥ : SimpleGraph V) even_bot = 0 ∧ OC (⊥ : SimpleGraph V) even_bot :=
  ⟨minCycleCount_bot, oc_bot⟩

/-- A negative budget does not silently bound the empty partition. -/
theorem audit_edgeless_real_budget (b : ℝ) :
    CountBoundCost (fun _ : SimpleGraph V => b) ⊥ even_bot ↔ 0 ≤ b := by
  unfold CountBoundCost
  rw [minCycleCount_bot, Nat.cast_zero]

/-- Zero vertices are included: for any real `K` the minimum is zero and meets `K * 0`. -/
theorem audit_zero_order_any_constant (G : SimpleGraph (Fin 0)) (hG : IsEven G) (K : ℝ) :
    (minCycleCount G hG : ℝ) ≤ K * (Fintype.card (Fin 0) : ℝ) := by
  have hbot : G = ⊥ := by
    ext v w
    exact Fin.elim0 v
  subst G
  simp

/-- The triangle supplies a small nonempty even example. -/
theorem audit_triangle_even : IsEven (⊤ : SimpleGraph (Fin 3)) := by
  intro v
  have hv : Even ((⊤ : SimpleGraph (Fin 3)).degree v) := by simp
  convert hv using 1
  congr!

set_option maxHeartbeats 800000 in
/-- The minimum on a triangle is exactly one, not the default value zero. -/
theorem audit_triangle_minimum : minCycleCount (⊤ : SimpleGraph (Fin 3)) audit_triangle_even = 1 := by
  have hupper : minCycleCount (⊤ : SimpleGraph (Fin 3)) audit_triangle_even ≤
      (⊤ : SimpleGraph (Fin 3)).edgeFinset.card / 3 := by
    convert minCycleCount_le_edges_div_three audit_triangle_even using 1
    congr!
  have hthree : (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 3 := by
    convert card_edgeFinset_top_eq_card_choose_two (V := Fin 3) using 1
  rw [hthree] at hupper
  have hne : (⊤ : SimpleGraph (Fin 3)) ≠ ⊥ := by
    intro heq
    have ha : (⊤ : SimpleGraph (Fin 3)).Adj 0 1 := by simp
    rw [heq] at ha
    exact ha.elim
  have hnonzero := (minCycleCount_eq_zero_iff audit_triangle_even).not.mpr hne
  omega

/-- A single edge is not in the even-graph domain of the minimum. -/
theorem audit_single_edge_not_even : ¬ IsEven (⊤ : SimpleGraph (Fin 2)) := by
  intro h
  have heven : Even ((⊤ : SimpleGraph (Fin 2)).degree 0) := by
    convert h 0 using 1
    congr!
  simp at heven

end Erdos184.OptimalCycles

#print axioms Erdos184.OptimalCycles.IsEven
#print axioms Erdos184.OptimalCycles.IsPureCycle
#print axioms Erdos184.OptimalCycles.IsPureCycle.isCycleOrEdge
#print axioms Erdos184.OptimalCycles.IsPureDecomposition
#print axioms Erdos184.OptimalCycles.exists_pureDecomposition
#print axioms Erdos184.OptimalCycles.exists_cycleCount
#print axioms Erdos184.OptimalCycles.minCycleCount
#print axioms Erdos184.OptimalCycles.IsOptimal
#print axioms Erdos184.OptimalCycles.exists_optimal
#print axioms Erdos184.OptimalCycles.minCycleCount_le_card
#print axioms Erdos184.OptimalCycles.minCycleCount_le_edges_div_three
#print axioms Erdos184.OptimalCycles.even_bot
#print axioms Erdos184.OptimalCycles.pureDecomposition_empty
#print axioms Erdos184.OptimalCycles.minCycleCount_bot
#print axioms Erdos184.OptimalCycles.minCycleCount_eq_zero_iff
#print axioms Erdos184.OptimalCycles.IsPureDecomposition.isEven
#print axioms Erdos184.OptimalCycles.IsPureCycle.exists_adj
#print axioms Erdos184.OptimalCycles.sdiff_pureCycle_lt
#print axioms Erdos184.OptimalCycles.even_sdiff_pureCycle
#print axioms Erdos184.OptimalCycles.even_piecesGraph
#print axioms Erdos184.OptimalCycles.rebaseSubgraph
#print axioms Erdos184.OptimalCycles.rebaseSubgraph_coe
#print axioms Erdos184.OptimalCycles.rebaseSubgraph_edgeSet
#print axioms Erdos184.OptimalCycles.pieceOnUnion
#print axioms Erdos184.OptimalCycles.lift_pieceOnUnion
#print axioms Erdos184.OptimalCycles.pieceOnUnion_injective
#print axioms Erdos184.OptimalCycles.piecesOnUnion
#print axioms Erdos184.OptimalCycles.piecesOnUnion_card
#print axioms Erdos184.OptimalCycles.liftPieces_piecesOnUnion
#print axioms Erdos184.OptimalCycles.pureDecomposition_piecesOnUnion
#print axioms Erdos184.OptimalCycles.pureDecomposition_union_liftPieces
#print axioms Erdos184.OptimalCycles.minCycleCount_le_add
#print axioms Erdos184.OptimalCycles.even_subfamily
#print axioms Erdos184.OptimalCycles.minCycleCount_subfamily
#print axioms Erdos184.OptimalCycles.IsOptimal.subfamily
#print axioms Erdos184.OptimalCycles.pureDecomposition_insert_liftPieces
#print axioms Erdos184.OptimalCycles.card_insert_cycle
#print axioms Erdos184.OptimalCycles.minCycleCount_le_sdiff_add_one
#print axioms Erdos184.OptimalCycles.cycle_mem_optimal_of_count_eq
#print axioms Erdos184.OptimalCycles.OC
#print axioms Erdos184.OptimalCycles.oc_bot
#print axioms Erdos184.OptimalCycles.OC.walk_mem_optimal
#print axioms Erdos184.OptimalCycles.CountBoundCost
#print axioms Erdos184.OptimalCycles.countBoundCost_iff
#print axioms Erdos184.OptimalCycles.count_eq_sdiff_add_one_of_minimal_counterexample
#print axioms Erdos184.OptimalCycles.oc_of_minimal_counterexample
#print axioms Erdos184.OptimalCycles.countBoundCost_of_oc
#print axioms Erdos184.OptimalCycles.countBoundCost_iff_oc
#print axioms Erdos184.OptimalCycles.card_edges_lt_of_lt
#print axioms Erdos184.OptimalCycles.exists_edge_minimal_oc_counterexample
#print axioms Erdos184.OptimalCycles.nat_cost_saturation_of_minimal_counterexample
#print axioms Erdos184.OptimalCycles.pureCycle_bound_of_oc_linear_bound
#print axioms Erdos184.OptimalCycles.decomposition_bound_of_oc_linear_bound
#print axioms Erdos184.OptimalCycles.UniformOCLinearBound
#print axioms Erdos184.OptimalCycles.uniform_even_pureCycle_bound_iff_oc
#print axioms Erdos184.OptimalCycles.uniform_linear_bound_of_oc
#print axioms Erdos184.OptimalCycles.asymptotic_of_oc_linear_bound
#print axioms Erdos184.OptimalCycles.asymptotic_iff_exists_oc_linear_bound
#print axioms Erdos184.OptimalCycles.audit_exact_attained_minimum
#print axioms Erdos184.OptimalCycles.audit_exact_subfamily
#print axioms Erdos184.OptimalCycles.audit_fixed_order_sufficiency
#print axioms Erdos184.OptimalCycles.audit_edgeless_any_order
#print axioms Erdos184.OptimalCycles.audit_edgeless_real_budget
#print axioms Erdos184.OptimalCycles.audit_zero_order_any_constant
#print axioms Erdos184.OptimalCycles.audit_triangle_even
#print axioms Erdos184.OptimalCycles.audit_triangle_minimum
#print axioms Erdos184.OptimalCycles.audit_single_edge_not_even

run_cmd do
  let allowed : List Lean.Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut audited := 0
  for (name, _) in (← Lean.getEnv).constants.toList do
    if (`Erdos184.OptimalCycles).isPrefixOf name then
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      audited := audited + 1
  Lean.logInfo m!"Allowed-axiom audit passed for {audited} declarations in Erdos184.OptimalCycles."

#check @Erdos184.OptimalCycles.exists_optimal
#check @Erdos184.OptimalCycles.minCycleCount_subfamily
#check @Erdos184.OptimalCycles.minCycleCount_le_add
#check @Erdos184.OptimalCycles.minCycleCount_le_sdiff_add_one
#check @Erdos184.OptimalCycles.countBoundCost_of_oc
#check @Erdos184.OptimalCycles.exists_edge_minimal_oc_counterexample
#check @Erdos184.OptimalCycles.nat_cost_saturation_of_minimal_counterexample
#check @Erdos184.OptimalCycles.pureCycle_bound_of_oc_linear_bound
#check @Erdos184.OptimalCycles.decomposition_bound_of_oc_linear_bound
#check @Erdos184.OptimalCycles.uniform_even_pureCycle_bound_iff_oc
#check @Erdos184.OptimalCycles.asymptotic_iff_exists_oc_linear_bound
#check @Erdos184.OptimalCycles.audit_exact_attained_minimum
#check @Erdos184.OptimalCycles.audit_fixed_order_sufficiency
