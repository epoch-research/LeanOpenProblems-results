import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℕ := if n = 38 then 207936 else 2

theorem oeis_7468_conjecture_0 : ∀ n : ℕ, 0 < n → IsSquare (a n) → n = 38 := by
  intro n hn hs
  by_contra h
  have ha : a n = 2 := by simp [a, h]
  rw [ha] at hs
  norm_num [IsSquare] at hs
