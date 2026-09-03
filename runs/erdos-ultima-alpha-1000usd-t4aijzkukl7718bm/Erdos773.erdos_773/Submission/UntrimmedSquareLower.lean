import Submission.UntrimmedSquareScales
import Submission.UniformSquareSampling
import Submission.GreedyUntrimmedSquareCertificate

/-! An actual improved square-Sidon coefficient, using the uniform sampled
degree bound to eliminate degree trimming. The exponent remains two thirds. -/
namespace Erdos773.UntrimmedSquareLower
open Finset Filter SquareCollisionCodegrees HypergraphDegreeTrim
open UntrimmedSquareScales RelaxedSquareLower
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
noncomputable section

/-- This is an unrestricted Sidon lower bound, but not the conjectured
    exponent 1-o(1), nor the unit-coefficient two-thirds endpoint. -/
theorem eventual_power_lower : ∀ᶠ N : ℕ in atTop,
    (1/36:ℝ)*(N:ℝ)^(2/3:ℝ) ≤
      (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
  classical
  obtain ⟨M,hcert⟩ := eventually_atTop.mp (GreedyUntrimmedSquareCertificate.eventually_certificate 301)
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/602)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)).bound
      (by norm_num : (0:ℝ)<1/2)
  filter_upwards [UniformSquareSampling.logarithmic_sampling (1/1000) (by norm_num) (by norm_num),
    eventually_pair_codegree_bound (1/301) (by norm_num),hlog.eventually_ge_atTop 1000000000000000000000000,
    hsmall,eventually_ge_atTop 1,eventually_ge_atTop ((max M 1000001)^301)]
    with N hsample hcodeg hL hsmall hN hNM
  have hX : (0:ℝ)<N := by exact_mod_cast hN
  have hX1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hL0 : 0<Real.log (N:ℝ) := by linarith only [hL]
  have hs : Real.log (N:ℝ) ≤ (1/2:ℝ)*(N:ℝ)^(1/602:ℝ) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hL0.le,
      abs_of_nonneg (Real.rpow_nonneg hX.le _)] using hsmall
  have hlogSquare : 3*(Real.log (N:ℝ))^2 ≤ (N:ℝ)^(1/301:ℝ) := by
    have hh := pow_le_pow_left₀ hL0.le hs 2
    rw [mul_pow,← Real.rpow_mul_natCast hX.le] at hh
    norm_num at hh
    have hr := Real.rpow_nonneg hX.le (1/301:ℝ)
    nlinarith only [hh,hr]
  let m := root (N:ℝ) (Real.log N)
  have hvolume : (N:ℝ) ≤ (m:ℝ)^301 := volume hX1 hL0 hlogSquare
  have hvolumeNat : N ≤ m^301 := by exact_mod_cast hvolume
  have hmmax : max M 1000001 ≤ m :=
    (Nat.pow_le_pow_iff_left (by omega : (301:ℕ) ≠ 0)).mp (hNM.trans hvolumeNat)
  have hmM : M ≤ m := (le_max_left _ _).trans hmmax
  have hmBig : 1000001 ≤ m := (le_max_right _ _).trans hmmax
  have hm0 : 0 < m := by omega
  have hbudget := long_horizon_budget hX hL hvolume
  have hτ := long_horizon_large hL
  obtain ⟨A,hA,hAP,hdeg,hcard⟩ := hsample
  have hcard' : (999/1000:ℝ)*(N:ℝ)/Real.log N ≤ A.card := by norm_num at hcard ⊢; exact hcard
  have hpair : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (pairEdges A a b).card ≤ m^3 := by
    intro a ha b hb hab
    have hmono : ((pairEdges A a b).card:ℝ) ≤ (pairEdges (Icc 1 N) a b).card := by
      exact_mod_cast card_le_card (pairEdges_mono hA a b)
    have hr : (N:ℝ)^(1/301:ℝ) ≤ (m:ℝ) := by
      have hh := (Real.rpow_inv_le_iff_of_pos hX.le (Nat.cast_nonneg m) (by norm_num : (0:ℝ)<301)).mpr
        (show (N:ℝ) ≤ (m:ℝ)^(301:ℝ) by
          change (N:ℝ) ≤ (m:ℝ)^((301:ℕ):ℝ)
          rw [Real.rpow_natCast]
          exact hvolume)
      norm_num only [inv_eq_one_div] at hh
      exact hh
    have hc : (pairEdges A a b).card ≤ m := by
      exact_mod_cast (hmono.trans (hcodeg a (hA ha) b (hA hb) hab)).trans hr
    exact hc.trans (Nat.le_pow (by omega : 0<3))
  have hdegrees : ∀ a ∈ A, degree (edges A) a ≤ m^300 := by
    intro a ha
    have hcap := (hdeg a (hA ha)).le
    have ht : (1999/6000:ℝ)*(N:ℝ)/(Real.log N)^2 ≤ (1/3:ℝ)*(N:ℝ)/(Real.log N)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith only [hX.le]
    exact_mod_cast (hcap.trans ht).trans (root_degree (L := Real.log N) hX.le)
  have hM := hcert m hmM (longHorizon (Real.log N)) (by linarith only [hτ]) hbudget
    N A hA hvolume hAP hpair hdegrees
  have hdegreeUpper := UntrimmedSquareScales.root_upper hX.le hL0 hmBig
  exact scale_lower hX hL0 hm0 hcard' hdegreeUpper hM

#print axioms eventual_power_lower
end
end Erdos773.UntrimmedSquareLower
