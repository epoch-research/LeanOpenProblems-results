import Mathlib

lemma exp_four_lt_81 : Real.exp 4 < 81 := by
  calc
    Real.exp 4 = Real.exp (4 : ℕ) := by norm_cast
    _ = Real.exp 1 ^ (4 : ℕ) := (Real.exp_one_pow 4).symm
    _ < (3 : ℝ) ^ (4 : ℕ) := by
      gcongr
      exact Real.exp_one_lt_three
    _ = 81 := by norm_num

lemma log_gt_four {p : ℕ} (hp : 81 ≤ p) : 4 < Real.log (p : ℝ) := by
  rw [← Real.exp_lt_exp]
  calc
    Real.exp 4 < 81 := exp_four_lt_81
    _ ≤ (p : ℝ) := Nat.cast_le.mpr hp
    _ = Real.exp (Real.log (p : ℝ)) := (Real.exp_log (by positivity)).symm
