import FormalConjectures.Util.ProblemImports
open BigOperators Int Real
noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat

example : a 0 = 0 := by norm_num [a]
example : a 1 = 1 := by norm_num [a]
example : a 2 = 0 := by norm_num [a]
example : a 3 = 1 := by norm_num [a]
example : a 4 = 2 := by norm_num [a]
example : a 8 = 6 := by norm_num [a]

example : ¬ (∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ)) := by
  intro h
  rcases h with ⟨N,hN⟩
  -- finite contradiction only if N <= 2; not enough
  by_cases hle : N ≤ 2
  · have h2 := hN 2 hle
    norm_num [a] at h2
  · sorry
