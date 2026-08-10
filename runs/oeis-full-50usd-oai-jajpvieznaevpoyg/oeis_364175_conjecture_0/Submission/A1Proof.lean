import FormalConjectures.Util.ProblemImports
open Real Nat Int
noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat

lemma gamma_5_3 : Real.Gamma ((5:ℝ)/3) = ((2:ℝ)/3) * Real.Gamma ((2:ℝ)/3) := by
  convert Real.Gamma_add_one (s := (2:ℝ)/3) (by norm_num) using 2 <;> ring

lemma gamma_8_3 : Real.Gamma ((8:ℝ)/3) = ((10:ℝ)/9) * Real.Gamma ((2:ℝ)/3) := by
  have h1 : Real.Gamma ((8:ℝ)/3) = ((5:ℝ)/3) * Real.Gamma ((5:ℝ)/3) := by
    convert Real.Gamma_add_one (s := (5:ℝ)/3) (by norm_num) using 2 <;> ring
  rw [h1, gamma_5_3]
  ring

example : a 1 = 36 := by
  have hg : Real.Gamma ((2:ℝ)/3) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by norm_num))
  dsimp [a]
  norm_num [Real.Gamma_nat_eq_factorial]
  rw [gamma_5_3, gamma_8_3]
  field_simp [hg]
  norm_num
  simp
