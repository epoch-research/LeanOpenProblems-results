import Submission.SuccessorSmoothPrimeDensity

/-!
# A multiplicity exponent above 0.55

The weighted cofactor successor sieve supplies every exponent below
3667/6667. This is an unconditional improvement of the preceding finite
local bound, but it is still not the full Erdos 821 conjecture.
-/
open Nat Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve
set_option maxHeartbeats 2000000

theorem infinite_g_gt_successor_gain (γ : ℝ) (hγ : γ < 3667/6667) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨C,_hC,HC⟩ := exists_successor_smooth_prime_count
  apply infinite_g_gt_of_single_log_smooth_count 400020 180000 C (by decide) HC γ
  norm_num
  exact hγ

theorem infinite_g_gt_point_five_five :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(11/20 : ℝ)}.Infinite :=
  infinite_g_gt_successor_gain _ (by norm_num)

theorem erdos_821_successor_range (ε : ℝ) (hε : 3000/6667 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_successor_gain _ (by linarith only [hε])

lemma successor_gain_improves_finite_local : (2303/4351 : ℝ) < 3667/6667 := by norm_num

end Erdos821
