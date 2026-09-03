import Submission.ParametricWideDistribution
import Submission.BlockChebyshevSpecialization

/-!
# A fixed-mass application of the blockwise sieve

The quantitative conclusion has only a single logarithmic counting loss.
The smoothness ratio remains fixed and bounded away from zero.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

theorem widePair_block_smooth_count (a b c h : ℕ) (ha : 21 ≤ a)
    (hb : a+3 ≤ b) (hbc : c+4=b) (heq : 2*a+b+h=widePairScale a)
    (hc : 3 ≤ c) (hh : 1 ≤ h) (hcap : widePairScale a+4 ≤ 5*c)
    (hcoef : (8192/675 : ℝ)*(widePairScale a : ℝ)*h <
      chebyshevRatioConstant*(((c : ℝ)-2)*((c : ℝ)+h-2))) :
    ∃ C : ℕ, 0<C ∧ ∀ᶠ m : ℕ in atTop,
      (independentN (widePairScale a) m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN (widePairScale a) m) (independentN b m)).card : ℝ) := by
  apply fixed_mass_block_smooth_count (widePairPool a) (2*a) (2*a+4) (widePairScale a)
    b c h 16 (widePairMassDenom a) heq (by omega) (by omega) hh hcap
    (by decide) (widePairMassDenom_pos a)
  · filter_upwards [eventually_ge_atTop 1] with m hm
    intro d hd
    have hbd := widePairPool_bounds a m d hd
    exact ⟨by omega,hbd.2.1,hbd.2.2,widePairPool_smooth_odd a b m d (by omega) hb hm hd⟩
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact widePairPool_mass_lower a m hm
  · exact eventually_widePair_progression_lower a ha
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact fun n hn hN => widePair_divisor_incidence_le a m n ha hm hn hN
  · apply (blockMainLimit_le_telescoped (widePairScale a) c h hc).trans_lt
    have hcR : (3 : ℝ) ≤ c := by exact_mod_cast hc
    have hhR : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    exact (div_lt_iff₀ (mul_pos (by linarith) (by linarith))).mpr hcoef

/-- An explicit smooth-prime count of order X/log X at ratio
19268660/40000020. -/
theorem exists_wide_block_smooth_prime_count :
    ∃ C : ℕ, 0<C ∧ ∀ᶠ m : ℕ in atTop,
      (independentN 40000020 m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN 40000020 m) (independentN 19268660 m)).card : ℝ) := by
  apply widePair_block_smooth_count 10000000 19268660 19268656 731360
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [widePairScale])
    (by norm_num) (by norm_num) (by norm_num [widePairScale])
  apply lt_trans (show (8192/675 : ℝ)*(widePairScale 10000000 : ℝ)*731360 <
      (92129/100000 : ℝ)*(((19268656 : ℝ)-2)*((19268656 : ℝ)+731360-2)) by
        norm_num [widePairScale])
  exact mul_lt_mul_of_pos_right chebyshevRatioConstant_gt_decimal (by norm_num)

lemma infinite_g_gt_of_single_log_smooth_count (t b C : ℕ) (hbt : b<t)
    (H : ∀ᶠ m : ℕ in atTop,
      (independentN t m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN t m) (independentN b m)).card : ℝ))
    (γ : ℝ) (hγ : γ<1-(b : ℝ)/t) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  apply infinite_g_gt_of_eventual_polynomial_count (64*t) (64*b) 1 C 1
    (Nat.mul_lt_mul_of_pos_left hbt (by decide)) ?_ γ ?_
  · filter_upwards [H] with m hm
    refine ⟨smoothPrimePool (independentN t m) (independentN b m),?_,?_⟩
    · intro p hp
      obtain ⟨hp,hs⟩ := mem_filter.mp hp
      obtain ⟨hN,hpr⟩ := Nat.mem_primesBelow.mp hp
      refine ⟨hpr,?_,?_⟩
      · change p ≤ independentN t m
        omega
      · simpa only [one_mul] using hs
    · have hh : independentN t m ≤ C*m*(smoothPrimePool (independentN t m) (independentN b m)).card := by
        exact_mod_cast hm
      exact hh.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C (by simp)))
  · simpa only [Nat.cast_mul,Nat.cast_ofNat,
      mul_div_mul_left _ _ (by norm_num : (64 : ℝ) ≠ 0)] using hγ

/-- This slightly improves the earlier explicit blockwise exponent while
also providing the stronger underlying one-logarithm prime count. -/
theorem infinite_g_gt_wide_block_uniform (γ : ℝ) (hγ : γ<1036568/2000001) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨C,_hC,hcount⟩ := exists_wide_block_smooth_prime_count
  apply infinite_g_gt_of_single_log_smooth_count 40000020 19268660 C (by decide) hcount γ
  norm_num
  exact hγ

theorem erdos_821_wide_block_range (ε : ℝ) (hε : 963433/2000001<ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_wide_block_uniform (1-ε) (by linarith only [hε])

end Erdos821
