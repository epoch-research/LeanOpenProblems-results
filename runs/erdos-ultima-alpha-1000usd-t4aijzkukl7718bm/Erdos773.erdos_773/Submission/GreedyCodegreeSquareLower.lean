import Submission.GreedyCodegreeSquareScales

/-!
An actual square-Sidon lower bound from nonlinear extraction. The bound
improves the coefficient but remains at exponent 2/3, below the conjecture.
-/
namespace Erdos773.GreedyCodegreeSquareLower
open Finset Filter SquareCollisionCodegrees GreedyCodegreeSquareScales
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
noncomputable section

/-- Removing the linearizing thinning yields the checked lower coefficient
    1/500. This is not the unit-coefficient endpoint or a larger exponent. -/
theorem eventual_power_lower : ∀ᶠ N : ℕ in atTop,
    (1/500:ℝ)*(N:ℝ)^(2/3:ℝ) ≤
      (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
  classical
  obtain ⟨M,hcert⟩ := eventually_atTop.mp (GreedyCodegreeSquareCertificate.eventually_certificate 301)
  have hlog : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/602)).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop)).bound
      (by norm_num : (0:ℝ) < 1)
  filter_upwards [ControlledSquareSampling.logarithmic_sampling (1/1000) (by norm_num),
    eventually_pair_codegree_bound (1/301) (by norm_num),hlog.eventually_ge_atTop 1000000000000,
    hsmall,eventually_ge_atTop 1,eventually_ge_atTop ((max M 10001)^301)]
    with N hsample hcodeg hL hsmall hN hNM
  have hX : (0:ℝ) < N := by exact_mod_cast hN
  have hX1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hLpos : 0 < Real.log (N:ℝ) := by linarith only [hL]
  have hs : Real.log (N:ℝ) ≤ (N:ℝ)^(1/602:ℝ) := by
    simpa only [Function.comp_apply,Real.norm_eq_abs,abs_of_nonneg hLpos.le,
      abs_of_nonneg (Real.rpow_nonneg hX.le (1/602:ℝ)),one_mul] using hsmall
  have hlogSquare : (Real.log (N:ℝ))^2 ≤ (N:ℝ)^(1/301:ℝ) := by
    have hh := pow_le_pow_left₀ hLpos.le hs 2
    have he : ((N:ℝ)^(1/602:ℝ))^2 = (N:ℝ)^(1/301:ℝ) := by
      rw [← Real.rpow_mul_natCast hX.le]
      norm_num
    rwa [he] at hh
  let m := degreeRoot (N:ℝ) (Real.log N)
  have hvolume : (N:ℝ) ≤ (m:ℝ)^301 := volume301 hX1 hLpos hlogSquare
  have hvolumeNat : N ≤ m^301 := by exact_mod_cast hvolume
  have hmmax : max M 10001 ≤ m :=
    (Nat.pow_le_pow_iff_left (by omega : (301:ℕ) ≠ 0)).mp (hNM.trans hvolumeNat)
  have hmM : M ≤ m := (le_max_left _ _).trans hmmax
  have hm10001 : 10001 ≤ m := (le_max_right _ _).trans hmmax
  have hmpos : 0 < m := by omega
  have hmone : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hupper := root_upper hX.le hLpos hm10001
  have hroot : (N:ℝ)^(1/301:ℝ) ≤ (m:ℝ) := by
    have hh := (Real.rpow_inv_le_iff_of_pos hX.le (Nat.cast_nonneg m) (by norm_num : (0:ℝ) < 301)).mpr
      (show (N:ℝ) ≤ (m:ℝ)^(301:ℝ) by
        change (N:ℝ) ≤ (m:ℝ)^((301:ℕ):ℝ)
        rw [Real.rpow_natCast]
        exact hvolume)
    simpa only [inv_eq_one_div] using hh
  have hm3 : (m:ℝ) ≤ (m:ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hmone (by omega : 1 ≤ 3)
  obtain ⟨A,hAN,hAP,hsize,hAupper,hE⟩ := hsample
  norm_num at hsize hE
  have hK : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → (pairEdges A a b).card ≤ m^3 := by
    intro a ha b hb hab
    have hmono : ((pairEdges A a b).card:ℝ) ≤ ((pairEdges (Icc 1 N) a b).card:ℝ) := by
      exact_mod_cast card_le_card (pairEdges_mono hAN a b)
    exact_mod_cast (hmono.trans (hcodeg a (hAN ha) b (hAN hb) hab)).trans (hroot.trans hm3)
  have hτ : 1 ≤ horizon (Real.log (N:ℝ)) := by linarith only [horizon_ten hL]
  have hbudget := horizon_budget hX hL hvolume
  have hD : 0 < degreeScale (N:ℝ) (Real.log N) := by unfold degreeScale; positivity
  have hM := hcert m hmM (horizon (Real.log (N:ℝ))) hτ hbudget N A hAN hvolume hAP hK
    (degreeScale N (Real.log N)) hD (root_lower hX.le)
  exact scale_lower hX hLpos hmpos (trim_surplus hX hLpos hsize hE) hupper hM

#print axioms eventual_power_lower
end
end Erdos773.GreedyCodegreeSquareLower
