import Submission.GreedyAvailableMeanDrift

/-!
A sign check for the moving-mean program, NOT a counterexample to Erdős 773.
Even an exactly regular linear four-uniform hypergraph can have negative
mixed two/four degree covariance after legal selections. Thus the higher
covariance term cannot simply be discarded with the variance's sign.
-/
namespace Erdos773.GreedyMeanCovarianceExample
open Finset GreedyHypergraphState GreedyAvailableMeanDrift HypergraphDegreeTrim
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
noncomputable section

def H : Finset (Finset (Fin 8)) := {{0,1,2,3}, {4,5,6,7}}
def I : Finset (Fin 8) := {0,1}

theorem four_uniform : ∀ e ∈ H, e.card = 4 := by
  decide +kernel

theorem regular : ∀ u : Fin 8, degree H u = 1 := by
  decide +kernel

theorem disjoint_edges : ∀ e ∈ H, ∀ f ∈ H, e ≠ f → Disjoint e f := by
  decide +kernel

theorem legal_choices : (0 : Fin 8) ∈ available H ∅ ∧ (1 : Fin 8) ∈ available H {0} := by
  constructor <;> rw [mem_available] <;> unfold Independent <;> decide +kernel

theorem independent : Independent H I := by
  unfold Independent
  decide +kernel

theorem available_eq : available H I = {2,3,4,5,6,7} := by
  ext u
  rw [mem_available]
  unfold Independent
  fin_cases u <;> decide +kernel

theorem two_degrees : ∀ u : Fin 8, localDegree H I 2 u = if u = 2 ∨ u = 3 then 1 else 0 := by
  intro u
  unfold localDegree incident active
  rw [available_eq]
  fin_cases u <;> norm_num [H, I, Fin.ext_iff, filter_insert, filter_singleton, card_insert_of_notMem] <;> decide +kernel

theorem four_degrees : ∀ u : Fin 8, localDegree H I 4 u = if 4 ≤ u.val then 1 else 0 := by
  intro u
  unfold localDegree incident active
  rw [available_eq]
  fin_cases u <;> norm_num [H, I, Fin.ext_iff, filter_insert, filter_singleton, card_insert_of_notMem] <;> decide +kernel

theorem means : meanDegree H I 2 = 1/3 ∧ meanDegree H I 4 = 2/3 := by
  simp only [meanDegree, FiniteMovingMean.mean, available_eq, two_degrees, four_degrees]
  norm_num [Fin.ext_iff, filter_insert, filter_singleton, card_insert_of_notMem, sum_insert]

/-- Mixed covariance has the opposite sign from a variance, despite exact
initial regularity and disjoint original edges. -/
theorem negative_mixed_covariance : covariance H I 4 2 = -4/3 := by
  rw [covariance, means.1, means.2, available_eq]
  simp only [two_degrees, four_degrees]
  norm_num [Fin.ext_iff, filter_insert, filter_singleton, card_insert_of_notMem, sum_insert]

#print axioms four_uniform
#print axioms regular
#print axioms disjoint_edges
#print axioms legal_choices
#print axioms independent
#print axioms available_eq
#print axioms negative_mixed_covariance
end
end Erdos773.GreedyMeanCovarianceExample
