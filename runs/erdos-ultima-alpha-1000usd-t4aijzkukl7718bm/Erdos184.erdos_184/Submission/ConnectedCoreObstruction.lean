import Submission.ComponentSeparatingCores
import Submission.SmallSeparatingCores

/-! A connected, 4-edge-connected necessary obstruction to Erdős 184.
No existence or exclusion of that obstruction is asserted. -/
open Filter SimpleGraph
open scoped Classical
namespace Erdos184Work.SeparatingCycleReduction
open Critical EvenCore Rigidity
set_option maxHeartbeats 1200000
universe u

lemma connected_obstruction_of_asymptotic_failure
    (hbad : ¬ (∃ f : ℕ → ℝ,
      (f =O[atTop] fun n : ℕ => (n : ℝ)) ∧
      ∀ {W : Type u} [Fintype W] [DecidableEq W] (R : SimpleGraph W),
      ∃ D : Finset R.Subgraph,
        (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ IsDecomposition R D ∧
        (D.card : ℝ) ≤ f (Fintype.card W))) :
    ∃ (W : Type u) (_ : Fintype W) (R : SimpleGraph W),
      (∀ v, Even (R.degree v)) ∧ EvenMinimal R ∧ R.Connected ∧ R ≠ ⊥ ∧
      4 ≤ number R ∧ ¬ HasSeparatingCycle R ∧ R.IsEdgeConnected 4 ∧
      (∀ v ∈ R.support, 4 ≤ R.degree v) ∧
      (∀ x (p : R.Walk x x), p.IsCycle → ∀ a b,
        (R \ p.toSubgraph.spanningCoe).Reachable a b ↔ R.Reachable a b) := by
  obtain ⟨V,iV,G,he,hm,hne,_,hs,_⟩ := obstruction_of_asymptotic_failure hbad
  letI := iV
  obtain ⟨C,hC⟩ := exists_nonempty_component hne
  let iC : Fintype C := @Subtype.fintype V (fun x => x ∈ C)
    (fun x => Classical.propDecidable _) iV
  letI := iC
  have hCe := component_even he C
  have hCm := component_even_minimal he hm C
  have hCs := no_separation_component hs C
  refine ⟨C,iC,C.toSimpleGraph,hCe,hCm,C.connected_toSimpleGraph,hC,
    no_separating_core_number_ge_four hCe hCm hC hCs,hCs,
    edge_connected_four_of_no_separation hCe hCs C.connected_toSimpleGraph,?_,?_⟩
  · exact no_separating_even_degree_ge_four hCe hCs
  · intro x p hp a b
    exact no_separating_cycle_preserves_reachability hCs hp a b

end Erdos184Work.SeparatingCycleReduction
#print axioms Erdos184Work.SeparatingCycleReduction.connected_obstruction_of_asymptotic_failure
