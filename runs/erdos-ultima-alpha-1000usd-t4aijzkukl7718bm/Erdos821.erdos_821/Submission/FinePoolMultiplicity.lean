import Submission.FinePoolSmoothDensity

/-!
# A fixed inverse-totient multiplicity exponent above 0.61

This gain comes from retaining the initial multiplier pool inside the
successor sieve. It is still a fixed threshold, not Erdős 821 in full.
-/
open Nat Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 2000000

theorem infinite_g_gt_fine_pool_gain (γ : ℝ) (hγ : γ < 406667/666667) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨C,_hC,HC⟩ := exists_fine_pool_smooth_prime_count
  apply infinite_g_gt_of_single_log_smooth_count 40000020 15600000 C (by decide) HC γ
  norm_num at hγ ⊢
  exact hγ

theorem infinite_g_gt_sixty_one_hundredths :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(61/100 : ℝ)}.Infinite :=
  infinite_g_gt_fine_pool_gain _ (by norm_num)

theorem erdos_821_fine_pool_range (ε : ℝ) (hε : 260000/666667 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_fine_pool_gain _ (by linarith only [hε])

lemma fine_pool_threshold_improves_retained_pool :
    (398667/666667 : ℝ) < 406667/666667 := by norm_num

end Erdos821
