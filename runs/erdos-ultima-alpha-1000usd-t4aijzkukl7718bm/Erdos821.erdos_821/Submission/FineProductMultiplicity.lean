import Submission.FineProductSmoothDensity

/-!
# A fixed inverse-totient multiplicity exponent above 0.557

This is a strict improvement of the earlier fixed exponent, not a
settlement of Erdős 821.
-/
open Nat Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 2000000

theorem infinite_g_gt_fine_product_gain (γ : ℝ) (hγ : γ < 11141/20001) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨C,_hC,HC⟩ := exists_fine_product_smooth_prime_count
  apply infinite_g_gt_of_single_log_smooth_count 400020 177200 C (by decide) HC γ
  norm_num
  exact hγ

theorem infinite_g_gt_557_thousandths :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(557/1000 : ℝ)}.Infinite :=
  infinite_g_gt_fine_product_gain _ (by norm_num)

theorem erdos_821_fine_product_range (ε : ℝ) (hε : 8860/20001 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_fine_product_gain _ (by linarith only [hε])

lemma fine_product_gain_improves_product :
    (11116/20001 : ℝ) < 11141/20001 := by norm_num

end Erdos821
