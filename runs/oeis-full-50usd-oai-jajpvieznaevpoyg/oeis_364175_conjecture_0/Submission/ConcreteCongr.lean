import FormalConjectures.Util.ProblemImports
open Real Nat Int
noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat

example : a (1 * 5 ^ 1) ≡ a (1 * 5 ^ (1 - 1)) [MOD 5 ^ (3 * 1)] := by
  norm_num [a, Nat.ModEq]

example : a (1 * 5 ^ 2) ≡ a (1 * 5 ^ (2 - 1)) [MOD 5 ^ (3 * 2)] := by
  norm_num [a, Nat.ModEq]
