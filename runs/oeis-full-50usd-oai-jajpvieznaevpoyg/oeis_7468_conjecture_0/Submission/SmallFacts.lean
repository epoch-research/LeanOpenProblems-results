import FormalConjectures.Util.ProblemImports

noncomputable def a (n : ℕ) : ℕ :=
  let start_idx : ℕ := (n * (n - 1)) / 2
  Finset.sum (Finset.range n) fun i ↦ Nat.nth Nat.Prime (start_idx + i)

example : ¬ IsSquare (2 : ℕ) := by norm_num [IsSquare]
example : IsSquare (207936 : ℕ) := by norm_num [IsSquare]
example : a 1 = 2 := by simp [a, Nat.nth_prime_zero_eq_two]
example : ¬ IsSquare (a 1) := by rw [show a 1 = 2 by simp [a, Nat.nth_prime_zero_eq_two]]; norm_num [IsSquare]
