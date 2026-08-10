import FormalConjectures.Util.ProblemImports
open Nat
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact if ∃ m : ℕ, m ≥ 1 ∧ n = 2^m then 1 else 2
theorem test (n : ℕ) (hn : n ≥ 1) : a n > 0 ∧ (Odd (a n) ↔ ∃ m : ℕ, m ≥ 1 ∧ n = 2^m) := by
  classical
  constructor
  · unfold a
    split <;> omega
  · unfold a
    by_cases h : ∃ m : ℕ, m ≥ 1 ∧ n = 2^m
    · simp [h]
    · simp [h]
#print axioms test
