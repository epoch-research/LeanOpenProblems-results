import Submission.GapCountShapeExample

/-! Ordinary log-concavity, not only ultra-log-concavity, fails for the
survivor-count histogram of a genuine squarefree prime product. This is an
auxiliary obstruction and does not disprove the Jacobsthal conjecture. -/
namespace Erdos970.GapAverages.ShapeExample

/-- Ordinary log-concavity of the finite-period count histogram. -/
def CountLogConcave (N m : ℕ) : Prop :=
  ∀ j : ℕ, frequency N m j * frequency N m (j + 2) ≤
    frequency N m (j + 1) ^ 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma exact_ordinary_shape_failure :
    frequency 231 26 14 = 89 ∧ frequency 231 26 15 = 18 ∧
    frequency 231 26 16 = 4 := by
  decide +kernel

/-- A three-prime product suffices to violate ordinary log-concavity. -/
theorem not_countLogConcave_231 : ¬CountLogConcave 231 26 := by
  intro h
  have hh := h 14
  norm_num only [Nat.reduceAdd] at hh
  rw [exact_ordinary_shape_failure.1, exact_ordinary_shape_failure.2.1,
    exact_ordinary_shape_failure.2.2] at hh
  norm_num at hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The counterexample modulus is squarefree and has precisely three
specified prime factors. -/
lemma modulus_231 :
    (231 : ℕ).primeFactors = {3, 7, 11} ∧ Squarefree (231 : ℕ) := by
  decide +kernel

theorem not_all_squarefree_countLogConcave :
    ¬∀ N : ℕ, 0 < N → Squarefree N → ∀ m : ℕ, CountLogConcave N m := by
  intro h
  exact not_countLogConcave_231 (h 231 (by norm_num) modulus_231.2 26)

#print axioms not_countLogConcave_231
#print axioms not_all_squarefree_countLogConcave
end Erdos970.GapAverages.ShapeExample
