import Submission.ScaledProductSmoothDensity

/-!
# A fixed inverse-totient multiplicity exponent above 0.5584

A rescaled sixteen-band refinement. The full Erdős 821 statement remains
unproved; in particular no exponent-amplification principle is asserted.
-/
open Nat Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 2000000

theorem infinite_g_gt_scaled_product_gain (γ : ℝ) (hγ : γ < 372267/666667) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨C,_hC,HC⟩ := exists_scaled_product_smooth_prime_count
  apply infinite_g_gt_of_single_log_smooth_count 40000020 17664000 C (by decide) HC γ
  norm_num
  exact hγ

theorem infinite_g_gt_349_over_625 :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(349/625 : ℝ)}.Infinite :=
  infinite_g_gt_scaled_product_gain _ (by norm_num)

theorem erdos_821_scaled_product_range (ε : ℝ) (hε : 294400/666667 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_scaled_product_gain _ (by linarith only [hε])

lemma scaled_product_gain_improves_fine_product :
    (11141/20001 : ℝ) < 372267/666667 := by norm_num

end Erdos821
