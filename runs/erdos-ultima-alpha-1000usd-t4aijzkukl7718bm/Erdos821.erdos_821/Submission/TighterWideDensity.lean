import Submission.TighterFamilyDensity
import Submission.ParametricWideDensity

/-!
# A stronger unconditional fixed multiplicity exponent

The longer prime-pair sieve improves the blockwise coefficient from
8192/675 to 8192/765. This gives an exponent above 0.52062, but does not
settle the conjecture for arbitrarily small positive epsilon.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

theorem widePair_tight_block_smooth_count (a b c h : ℕ) (ha : 21 ≤ a)
    (hb : a+3 ≤ b) (hbc : c+4=b) (heq : 2*a+b+h=widePairScale a)
    (hc : 3 ≤ c) (hh : 1 ≤ h)
    (hcoef : (8192/765 : ℝ)*(widePairScale a : ℝ)*h <
      chebyshevRatioConstant*(((c : ℝ)-2)*((c : ℝ)+h-2))) :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      (independentN (widePairScale a) m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN (widePairScale a) m) (independentN b m)).card : ℝ) := by
  apply fixed_mass_block_smooth_count_ambient_tight (widePairPool a) (2*a) (2*a+4)
    (widePairScale a) b c h 16 (widePairMassDenom a) heq (by omega) (by omega) hh
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
  · apply (tightBlockMainLimit_le_telescoped (widePairScale a) c h hc).trans_lt
    have hcR : (3 : ℝ) ≤ c := by exact_mod_cast hc
    have hhR : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    exact (div_lt_iff₀ (mul_pos (by linarith) (by linarith))).mpr hcoef

/-- Order X/log X shifted-prime supply at smoothness ratio 19175170/40000020. -/
theorem exists_tight_wide_smooth_prime_count :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      (independentN 40000020 m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN 40000020 m) (independentN 19175170 m)).card : ℝ) := by
  apply widePair_tight_block_smooth_count 10000000 19175170 19175166 824850
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [widePairScale])
    (by norm_num) (by norm_num)
  apply lt_trans (show (8192/765 : ℝ)*(widePairScale 10000000 : ℝ)*824850 <
      (92129/100000 : ℝ)*(((19175166 : ℝ)-2)*((19175166 : ℝ)+824850-2)) by
        norm_num [widePairScale])
  exact mul_lt_mul_of_pos_right chebyshevRatioConstant_gt_decimal (by norm_num)

/-- The improved unrestricted exponent is approximately 0.5206209896895. -/
theorem infinite_g_gt_tight_wide_uniform (γ : ℝ) (hγ : γ < 2082485/4000002) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨C,_hC,hcount⟩ := exists_tight_wide_smooth_prime_count
  apply infinite_g_gt_of_single_log_smooth_count 40000020 19175170 C (by decide) hcount γ
  norm_num
  exact hγ

theorem infinite_g_gt_point_five_two_zero_six_two :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(26031/50000 : ℝ)}.Infinite :=
  infinite_g_gt_tight_wide_uniform _ (by norm_num)

theorem erdos_821_tight_wide_range (ε : ℝ) (hε : 1917517/4000002 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_tight_wide_uniform (1-ε) (by linarith only [hε])

lemma tight_wide_threshold_strict_improvement :
    (1036568/2000001 : ℝ) < 2082485/4000002 := by norm_num

end Erdos821
