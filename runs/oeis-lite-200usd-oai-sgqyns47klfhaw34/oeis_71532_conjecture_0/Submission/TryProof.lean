import FormalConjectures.Util.ProblemImports
open BigOperators Int Real

noncomputable def a (n : ℕ) : ℤ :=
  - Finset.sum (Finset.range n) fun k : ℕ =>
      let k_idx : ℕ := k + 1
      let base_real : ℝ := (3 : ℝ) / 2
      let exponent_int : ℤ := floor (base_real ^ k_idx)
      (-1 : ℤ) ^ exponent_int.toNat

example : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (a n : ℝ) > sqrt (n : ℝ) := by
  classical
  -- try many common tactics
  try norm_num [a]
  try positivity
  try aesop
  try omega
  try nlinarith
  try linarith
  try simp [a]
  try exact_mod_cast (by omega)
  sorry
