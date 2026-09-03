import Submission.FlexibleChebyshevGain

/-!
# An explicit multiplicity exponent from the flexible Chebyshev budget

This improves the unconditional fixed exponent in the development, but
remains bounded away from the full Erdős 821 range.
-/
open Nat Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

lemma chebyshevRatioConstant_gt_decimal :
    (92129/100000 : ℝ) < chebyshevRatioConstant := by
  have h6 := Real.sum_range_le_log_div (x := (1/11 : ℝ)) (by norm_num) (by norm_num) 3
  have h5 := Real.sum_range_le_log_div (x := (1/9 : ℝ)) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h6 h5
  have h3 : Real.log 3 = Real.log 2+Real.log (6/5)+Real.log (5/4) := by
    rw [← Real.log_mul (by norm_num) (by norm_num),← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    norm_num
  have h5' : Real.log 5 = 2*Real.log 2+Real.log (5/4) := by
    have h2 : Real.log ((2 : ℝ)^2) = 2*Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← h2,← Real.log_mul (by norm_num) (by norm_num)]
    congr 1
    norm_num
  rw [chebyshevRatioConstant_eq,h3,h5']
  linarith [Real.log_two_gt_d9]

/-- The improved fixed exponent is approximately 0.51766062. -/
theorem infinite_g_gt_flexible_chebyshev_uniform (γ : ℝ) (hγ : γ < 2070643/4000001) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  apply infinite_g_gt_flexible_chebyshev_parameters 2000000 4000001 1929358 70643
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ γ ?_
  · apply lt_trans (show (8192/675 : ℝ)*4000001*70643 <
        (92129/100000 : ℝ)*((1929358 : ℝ)-1)^2 by norm_num)
    exact mul_lt_mul_of_pos_right chebyshevRatioConstant_gt_decimal (by norm_num)
  · norm_num
    exact hγ

/-- A short decimal threshold strictly below the proven specialization. -/
theorem infinite_g_gt_point_five_one_seven_six_six (γ : ℝ) (hγ : γ < 25883/50000) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite :=
  infinite_g_gt_flexible_chebyshev_uniform γ
    (hγ.trans (by norm_num : (25883/50000 : ℝ) < 2070643/4000001))

theorem erdos_821_flexible_chebyshev_range (ε : ℝ) (hε : 1929358/4000001 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_flexible_chebyshev_uniform (1-ε) (by linarith only [hε])

theorem erdos_821_point_four_eight_two_three_four (ε : ℝ) (hε : 24117/50000 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_point_five_one_seven_six_six (1-ε) (by linarith only [hε])

lemma flexible_chebyshev_strict_improvement :
    (2064/4001 : ℝ) < 2070643/4000001 := by norm_num

end Erdos821
