import Submission.BlockSieveBudget
import Submission.FlexibleChebyshevSpecialization

/-!
# An explicit improved exponent from the blockwise sieve

The result improves the previous fixed exponent but does not settle
Erdős 821 for arbitrarily small positive epsilon.
-/
open Nat Filter
open scoped Classical BigOperators
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 3000000

theorem infinite_g_gt_block_telescoped_parameters (r t b h : ℕ)
    (heq : r+b+h=t) (hrt : 2*r+1 ≤ t) (hb : 3 ≤ b) (hh : 1 ≤ h)
    (hcap : t+5 ≤ 5*b)
    (hc : (8192/675 : ℝ)*(t : ℝ)*h <
      chebyshevRatioConstant*(((b : ℝ)-2)*((b : ℝ)+h-2)))
    (γ : ℝ) (hγ : γ < 1-(b : ℝ)/t) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  apply infinite_g_gt_block_parameters r t b h heq hrt (by omega) hh hcap ?_ γ hγ
  apply (blockMainLimit_le_telescoped t b h hb).trans_lt
  have hbR : (3 : ℝ) ≤ b := by exact_mod_cast hb
  have hhR : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  exact (div_lt_iff₀ (mul_pos (by linarith) (by linarith))).mpr hc

/-- The blockwise exponent is approximately 0.51828362. -/
theorem infinite_g_gt_block_chebyshev_uniform (γ : ℝ) (hγ : γ < 2073135/4000001) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  apply infinite_g_gt_block_telescoped_parameters 2000000 4000001 1926866 73135
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ γ ?_
  · apply lt_trans (show (8192/675 : ℝ)*4000001*73135 <
        (92129/100000 : ℝ)*(((1926866 : ℝ)-2)*((1926866 : ℝ)+73135-2)) by norm_num)
    exact mul_lt_mul_of_pos_right chebyshevRatioConstant_gt_decimal (by norm_num)
  · norm_num
    exact hγ

theorem infinite_g_gt_point_five_one_eight_two_eight (γ : ℝ) (hγ : γ < 12957/25000) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite :=
  infinite_g_gt_block_chebyshev_uniform γ
    (hγ.trans (by norm_num : (12957/25000 : ℝ) < 2073135/4000001))

theorem erdos_821_block_chebyshev_range (ε : ℝ) (hε : 1926866/4000001 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_block_chebyshev_uniform (1-ε) (by linarith only [hε])

theorem erdos_821_point_four_eight_one_seven_two (ε : ℝ) (hε : 12043/25000 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_point_five_one_eight_two_eight (1-ε) (by linarith only [hε])

lemma block_chebyshev_strict_improvement :
    (2070643/4000001 : ℝ) < 2073135/4000001 := by norm_num

end Erdos821
