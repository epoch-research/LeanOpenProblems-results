import FormalConjectures.Util.ProblemImports

open Finset Nat Set

def P_a08' (n m : ℕ) : Prop :=
  0 < m ∧ ∃ D ∈ powersetCard n (Nat.divisors m), D.sum id = m

instance (n m : ℕ) : Decidable (P_a08' n m) := by
  unfold P_a08'
  infer_instance

set_option maxRecDepth 100000

lemma test_72 : ¬ P_a08' 9 72 := by decide
lemma test_60 : P_a08' 8 60 := by decide
lemma test_84 : P_a08' 9 84 := by decide
lemma test_range_9 : ∀ x ∈ Finset.range 84, ¬ P_a08' 9 x := by decide
