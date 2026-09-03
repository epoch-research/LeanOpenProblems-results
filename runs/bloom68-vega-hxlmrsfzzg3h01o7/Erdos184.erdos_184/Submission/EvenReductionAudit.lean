import Submission.EvenReduction

/-!
# Audits for the even-graph reduction

The two target checks read the original statement using `type_of%`, without
using either admitted proof from `Submission.Spec`.  The axiom reports cover
every declaration in `EvenReduction.lean` and both target checks.  The linear
bounds for even graphs remain hypotheses throughout.
-/

open Filter SimpleGraph

namespace Erdos184.EvenReduction.Audit

universe u

open scoped Classical in
/-- The even cycle/edge hypothesis implies exactly the original target's type. -/
theorem evenBound_exactTarget (K : ℝ)
    (hEven : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph,
        (∀ S ∈ D, IsCycleOrEdge S.coe) ∧ IsDecomposition G D ∧
        (D.card : ℝ) ≤ K * (Fintype.card V : ℝ)) :
    type_of% @Erdos184.erdos_184.{u} := by
  exact asymptotic_of_even_linear_bound K hEven

open scoped Classical in
/-- The pure-cycle hypothesis also implies exactly the original target's type. -/
theorem evenCycles_exactTarget (K : ℝ)
    (hEven : ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, Even (G.degree v)) →
      ∃ D : Finset G.Subgraph,
        (∀ S ∈ D, S.coe.Connected ∧ S.coe.IsRegularOfDegree 2) ∧
        IsDecomposition G D ∧ (D.card : ℝ) ≤ K * (Fintype.card V : ℝ)) :
    type_of% @Erdos184.erdos_184.{u} := by
  exact asymptotic_of_even_cycle_bound K hEven

end Erdos184.EvenReduction.Audit

#print axioms Erdos184.EvenReduction.liftSubgraph
#print axioms Erdos184.EvenReduction.liftSubgraph_verts
#print axioms Erdos184.EvenReduction.liftSubgraph_coe
#print axioms Erdos184.EvenReduction.liftSubgraph_edgeSet
#print axioms Erdos184.EvenReduction.liftSubgraph_injective
#print axioms Erdos184.EvenReduction.liftPieces
#print axioms Erdos184.EvenReduction.mem_liftPieces
#print axioms Erdos184.EvenReduction.liftPieces_card
#print axioms Erdos184.EvenReduction.liftPieces_pairwiseDisjoint
#print axioms Erdos184.EvenReduction.liftPieces_edgeUnion
#print axioms Erdos184.EvenReduction.isDecomposition_union_liftPieces
#print axioms Erdos184.EvenReduction.degree_sdiff_of_le
#print axioms Erdos184.EvenReduction.even_degree_sdiff_iff
#print axioms Erdos184.EvenReduction.even_degree_cycle
#print axioms Erdos184.EvenReduction.sdiff_cycle_lt
#print axioms Erdos184.EvenReduction.exists_acyclic_same_parity
#print axioms Erdos184.EvenReduction.card_edges_le_of_isAcyclic
#print axioms Erdos184.EvenReduction.exists_parity_forest
#print axioms Erdos184.EvenReduction.liftPieces_isCycleOrEdge
#print axioms Erdos184.EvenReduction.extend_decomposition
#print axioms Erdos184.EvenReduction.decomposition_bound_of_even_bound
#print axioms Erdos184.EvenReduction.uniform_linear_bound_of_even
#print axioms Erdos184.EvenReduction.asymptotic_of_even_linear_bound
#print axioms Erdos184.EvenReduction.uniform_linear_bound_of_even_cycles
#print axioms Erdos184.EvenReduction.asymptotic_of_even_cycle_bound
#print axioms Erdos184.EvenReduction.Audit.evenBound_exactTarget
#print axioms Erdos184.EvenReduction.Audit.evenCycles_exactTarget

#check @Erdos184.EvenReduction.exists_parity_forest
#check @Erdos184.EvenReduction.decomposition_bound_of_even_bound
#check @Erdos184.EvenReduction.uniform_linear_bound_of_even
#check @Erdos184.EvenReduction.uniform_linear_bound_of_even_cycles
#check @Erdos184.EvenReduction.Audit.evenBound_exactTarget
#check @Erdos184.EvenReduction.Audit.evenCycles_exactTarget
