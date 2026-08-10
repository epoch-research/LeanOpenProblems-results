import FormalConjectures.Util.ProblemImports
open Real Nat Int
noncomputable def a (n : ℕ) : ℕ :=
  let n_r : ℝ := n.cast
  let val_R : ℝ :=
    (Real.Gamma (6 * n_r + 1) * Real.Gamma (2 / 3 * n_r + 1)) /
    (Real.Gamma (3 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (5 / 3 * n_r + 1))
  (round val_R).toNat

lemma gamma_ratio_pos (m : ℕ) :
    0 < (Real.Gamma (6 * (m:ℝ) + 1) * Real.Gamma (2 / 3 * (m:ℝ) + 1)) /
      (Real.Gamma (3 * (m:ℝ) + 1) * Real.Gamma (2 * (m:ℝ) + 1) * Real.Gamma (5 / 3 * (m:ℝ) + 1)) := by
  apply _root_.div_pos
  · apply mul_pos <;> apply Real.Gamma_pos_of_pos <;> positivity
  · apply mul_pos
    · apply mul_pos <;> apply Real.Gamma_pos_of_pos <;> positivity
    · apply Real.Gamma_pos_of_pos; positivity

example (m : ℕ) : 0 < (Real.Gamma (6 * (m:ℝ) + 1) * Real.Gamma (2 / 3 * (m:ℝ) + 1)) /
      (Real.Gamma (3 * (m:ℝ) + 1) * Real.Gamma (2 * (m:ℝ) + 1) * Real.Gamma (5 / 3 * (m:ℝ) + 1)) := gamma_ratio_pos m

#check round_eq_iff
#check Int.toNat_eq_zero
#check Int.toNat_of_nonneg
#check Int.toNat_eq_natCast
