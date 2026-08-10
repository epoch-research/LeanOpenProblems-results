import FormalConjectures.Util.ProblemImports
open Real Nat Int
noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat

example : Real.Gamma ((5:ℝ)/3 + 1) = ((5:ℝ)/3) * ((2:ℝ)/3) * Real.Gamma ((2:ℝ)/3) := by
  rw [show (5:ℝ)/3 + 1 = (5/3) + 1 by norm_num]
  rw [Real.Gamma_add_one]
  · rw [show (5:ℝ)/3 = (2/3)+1 by norm_num]
    rw [Real.Gamma_add_one]
    · ring
    · norm_num
  · norm_num

example : a 1 = 36 := by
  unfold a
  norm_num [Real.Gamma_nat_eq_factorial]
