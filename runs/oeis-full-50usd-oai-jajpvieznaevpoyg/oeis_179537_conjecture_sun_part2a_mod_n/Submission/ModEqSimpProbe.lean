import FormalConjectures.Util.ProblemImports
open Int
example (n : ℕ) (a : ℤ) : a ≡ 0 [ZMOD n] ↔ (n : ℤ) ∣ a := by simp [Int.modEq_zero_iff_dvd]
example (n : ℕ) (hn : n≥1) (a : ℤ) : a ≡ 0 [ZMOD n] ↔ ∃ q, a = n*q := by
  rw [Int.modEq_zero_iff_dvd]
  rfl
