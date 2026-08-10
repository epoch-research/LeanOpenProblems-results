import FormalConjectures.Util.ProblemImports
open Nat
set_option allowUnsafeReducibility true
attribute [local reducible] Nat.sqrt Nat.sqrt.iter
theorem test_decide (n : ℕ) (h : n = 193) : ∃ p < n, p.Prime ∧ (sqrt (n + p)).Prime := by
  rw [h]
  exact ⟨2, by decide⟩
