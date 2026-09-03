import Submission.PoolSmoothDensity

/-!
# A fixed inverse-totient multiplicity exponent above 0.598

This gain comes from retaining the initial multiplier pool inside the
successor sieve. It is still a fixed threshold, not Erdős 821 in full.
-/
open Nat Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 2000000

theorem infinite_g_gt_retained_pool_gain (γ : ℝ) (hγ : γ < 1196001/2000001) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨C,_hC,HC⟩ := exists_retained_pool_smooth_prime_count
  apply infinite_g_gt_of_single_log_smooth_count 40000020 16080000 C (by decide) HC γ
  norm_num at hγ ⊢
  exact hγ

theorem infinite_g_gt_299_over_500 :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(299/500 : ℝ)}.Infinite :=
  infinite_g_gt_retained_pool_gain _ (by norm_num)

theorem erdos_821_retained_pool_range (ε : ℝ) (hε : 804000/2000001 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_retained_pool_gain _ (by linarith only [hε])

lemma retained_pool_threshold_improves_scaled_product :
    (372267/666667 : ℝ) < 1196001/2000001 := by norm_num

end Erdos821
