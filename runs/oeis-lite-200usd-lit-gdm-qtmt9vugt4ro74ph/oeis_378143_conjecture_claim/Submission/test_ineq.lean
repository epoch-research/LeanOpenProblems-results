import FormalConjectures.Util.ProblemImports

open Nat

theorem lt_of_factor {n : ℕ} (hn : 15 ≤ n) (M : ℕ) (hM : M ≤ 167772161) : M < 10 ^ (2 ^ n) + 1 := by
  have h1 : 167772161 < 10 ^ 9 + 1 := by decide
  apply lt_of_le_of_lt hM
  apply lt_of_lt_of_le h1
  apply Nat.add_le_add_right
  apply Nat.pow_le_pow_right (by decide)
  -- 9 ≤ 2 ^ n
  have h2 : 9 ≤ 2 ^ 15 := by decide
  apply le_trans h2
  apply Nat.pow_le_pow_right (by decide) hn
