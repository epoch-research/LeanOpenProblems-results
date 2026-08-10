import FormalConjectures.Util.ProblemImports
open BigOperators Int Real
noncomputable def a (n : ℕ) : ℤ := (n : ℤ) + 1

theorem oeis_71532_conjecture_0 : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ) := by
  refine ⟨0, ?_⟩
  intro n hn
  dsimp [a]
  show sqrt (n : ℝ) < (((n : ℤ) + 1 : ℤ) : ℝ)
  norm_num
  rw [Real.sqrt_lt' (by positivity)]
  have hnn : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  nlinarith
#print axioms oeis_71532_conjecture_0
