import Submission.ContinuousCriticalFirstMoment
open scoped ENNReal
example : (1/10 : ℝ≥0∞)*(5/2)=1/4 := by
  apply (ENNReal.toReal_eq_toReal (by finiteness) (by finiteness)).mp
  norm_num
example : (1/4 : ℝ≥0∞)+1/4=1/2 := by
  norm_num
example : (11 : ℝ≥0∞)⁻¹*4⁻¹=1/44 := by
  rw [← ENNReal.mul_inv (by norm_num) (by norm_num)]
  norm_num
