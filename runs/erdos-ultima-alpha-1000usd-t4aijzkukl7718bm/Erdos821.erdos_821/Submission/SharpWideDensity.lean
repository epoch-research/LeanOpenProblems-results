import Submission.SharpFamilyDensity
import Submission.ParametricWideDensity

/-! # A further fixed multiplicity exponent

The sharper cofactor average improves the exponent beyond 0.52112.
The full conjecture for arbitrarily small positive epsilon remains unproved.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

theorem widePair_sharp_block_smooth_count (a b c h : ℕ) (ha : 21 ≤ a)
    (hb : a+3 ≤ b) (hbc : c+4=b) (heq : 2*a+b+h=widePairScale a)
    (hc : 3 ≤ c) (hh : 1 ≤ h)
    (hcoef : (13312/1275 : ℝ)*(widePairScale a : ℝ)*h <
      chebyshevRatioConstant*(((c : ℝ)-2)*((c : ℝ)+h-2))) :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      (independentN (widePairScale a) m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN (widePairScale a) m) (independentN b m)).card : ℝ) := by
  apply fixed_mass_block_smooth_count_ambient_sharp (widePairPool a) (2*a) (2*a+4)
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
  · apply (sharpBlockMainLimit_le_telescoped (widePairScale a) c h hc).trans_lt
    have hcR : (3 : ℝ) ≤ c := by exact_mod_cast hc
    have hhR : (0 : ℝ) ≤ h := Nat.cast_nonneg h
    exact (div_lt_iff₀ (mul_pos (by linarith) (by linarith))).mpr hcoef

/-- Order X/log X shifted-prime supply at smoothness ratio 19154910/40000020. -/
theorem exists_sharp_wide_smooth_prime_count :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      (independentN 40000020 m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN 40000020 m) (independentN 19154910 m)).card : ℝ) := by
  apply widePair_sharp_block_smooth_count 10000000 19154910 19154906 845110
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [widePairScale])
    (by norm_num) (by norm_num)
  apply lt_trans (show (13312/1275 : ℝ)*(widePairScale 10000000 : ℝ)*845110 <
      (92129/100000 : ℝ)*(((19154906 : ℝ)-2)*((19154906 : ℝ)+845110-2)) by
        norm_num [widePairScale])
  exact mul_lt_mul_of_pos_right chebyshevRatioConstant_gt_decimal (by norm_num)

/-- The improved unrestricted exponent is approximately 0.5211274894362553. -/
theorem infinite_g_gt_sharp_wide_uniform (γ : ℝ) (hγ : γ < 694837/1333334) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨C,_hC,hcount⟩ := exists_sharp_wide_smooth_prime_count
  apply infinite_g_gt_of_single_log_smooth_count 40000020 19154910 C (by decide) hcount γ
  norm_num
  exact hγ

theorem infinite_g_gt_point_five_two_one_one_two :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(3257/6250 : ℝ)}.Infinite :=
  infinite_g_gt_sharp_wide_uniform _ (by norm_num)

theorem erdos_821_sharp_wide_range (ε : ℝ) (hε : 638497/1333334 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_sharp_wide_uniform (1-ε) (by linarith only [hε])

lemma sharp_wide_threshold_strict_improvement :
    (2082485/4000002 : ℝ) < 694837/1333334 := by norm_num

end Erdos821
