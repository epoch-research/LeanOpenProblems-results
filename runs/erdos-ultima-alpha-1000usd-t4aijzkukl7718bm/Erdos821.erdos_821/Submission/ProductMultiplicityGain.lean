import Submission.ProductSmoothPrimeDensity

/-!
# A multiplicity exponent above five ninths

This remains a fixed-exponent partial result, not the full conjecture.
-/
open Nat Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 2000000

theorem infinite_g_gt_product_gain (γ : ℝ) (hγ : γ < 11116/20001) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨C,_hC,HC⟩ := exists_product_smooth_prime_count
  apply infinite_g_gt_of_single_log_smooth_count 400020 177700 C (by decide) HC γ
  norm_num
  exact hγ

theorem infinite_g_gt_five_ninths :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(5/9 : ℝ)}.Infinite :=
  infinite_g_gt_product_gain _ (by norm_num)

theorem erdos_821_product_range (ε : ℝ) (hε : 8885/20001 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_product_gain _ (by linarith only [hε])

lemma product_gain_improves_successor : (3667/6667 : ℝ) < 11116/20001 := by norm_num

end Erdos821
