import Submission.ContinuousCriticalFirstMoment

/-! Tightness and a compact-region lower bound for the critical continuous
cost operator. All integrals are nonnegative extended integrals. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology ENNReal
set_option maxHeartbeats 1800000

noncomputable def criticalCutMass (F : ℝ → ℝ≥0∞) (R : ℝ) : ℝ≥0∞ :=
  ∫⁻ s : ℝ in Ioo 1 R, ENNReal.ofReal (criticalWeight s) * F s

lemma criticalMass_le_cut_add_first (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (R : ℝ) (hR : 0 < R) :
    criticalMass F ≤ criticalCutMass F R + ENNReal.ofReal (1/R) * criticalFirstMass F := by
  classical
  let W : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (criticalWeight s) * F s
  have hW : Measurable W := criticalWeight_measurable.ennreal_ofReal.mul hF
  have hh : criticalMass F ≤
      ∫⁻ s : ℝ in Ioi 1, (Iio R).indicator W s +
        ENNReal.ofReal (1/R) * (ENNReal.ofReal s * W s) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    change W s ≤ _
    by_cases hsr : s < R
    · rw [indicator_of_mem (show s ∈ Iio R from hsr)]
      exact le_add_right le_rfl
    · rw [indicator_of_notMem (show s ∉ Iio R from hsr), zero_add]
      have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1/R) * ENNReal.ofReal s := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/R)]
        have h : (1 : ℝ) ≤ (1/R)*s := by
          have hsR : R ≤ s := le_of_not_gt hsr
          rw [one_div_mul_eq_div]
          exact (le_div_iff₀ hR).mpr (by simpa only [one_mul] using hsR)
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal h
      simpa only [one_mul, mul_assoc] using mul_le_mul_left h1 (W s)
  apply hh.trans_eq
  rw [lintegral_add_left (hW.indicator measurableSet_Iio),
    lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi,
    lintegral_const_mul _ (show Measurable (fun s : ℝ => ENNReal.ofReal s * W s) from
      measurable_id.ennreal_ofReal.mul hW)]
  simp only [criticalCutMass, criticalFirstMass, W, mul_assoc]

lemma criticalCostKernel_two_swap (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    criticalCostKernel F 2 =
      ∫⁻ v : ℝ in Ioi 1,
        (∫⁻ t : ℝ in Ioo 2 (v+1), ENNReal.ofReal (criticalCoefficient t)) *
          (ENNReal.ofReal (criticalCoefficient v) * F v) := by
  let A : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (criticalCoefficient t)
  let G : ℝ → ℝ≥0∞ := fun v => A v * F v
  have hA : Measurable A := criticalCoefficient_measurable.ennreal_ofReal
  have hG : Measurable G := hA.mul hF
  have he : criticalCostKernel F 2 = ∫⁻ t : ℝ in Ioi 2,
      A t * (∫⁻ v : ℝ in Ioi 1, if t < v+1 then G v else 0) := by
    unfold criticalCostKernel
    rw [show max (2 : ℝ) (2-1) = 2 by norm_num]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [ltail_triangle G t (mem_Ioi.mp ht).le]
  rw [he, triangular_lintegral A G hA hG 2 1]

lemma criticalCoefficient_lower_on (R t : ℝ) (hR : 1 ≤ R) (ht : 2 ≤ t) (htR : t ≤ R+1) :
    1/(R+1) ≤ criticalCoefficient t := by
  have ht0 : 0 < t := by linarith
  have hR0 : 0 < R+1 := by linarith
  apply (one_div_le_one_div_of_le ht0 htR).trans
  unfold criticalCoefficient
  apply (div_le_div_iff₀ ht0 (sq_pos_of_pos ht0)).mpr
  nlinarith

lemma critical_coefficient_linterval_lower (R v : ℝ) (hR : 1 ≤ R)
    (hv : 1 < v) (hvR : v ≤ R) :
    ENNReal.ofReal ((v-1)/(R+1)) ≤
      ∫⁻ t : ℝ in Ioo 2 (v+1), ENNReal.ofReal (criticalCoefficient t) := by
  have hR0 : 0 < R+1 := by linarith
  have hh : (∫⁻ _t : ℝ in Ioo 2 (v+1), ENNReal.ofReal (1/(R+1))) ≤
      ∫⁻ t : ℝ in Ioo 2 (v+1), ENNReal.ofReal (criticalCoefficient t) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact ENNReal.ofReal_le_ofReal (criticalCoefficient_lower_on R t hR ht.1.le
      (by linarith [ht.2]))
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(R+1))] at hh
  convert hh using 1
  congr 1
  ring

/-- Mass in a fixed compact region gives a positive value at level two. -/
theorem criticalCostKernel_two_ge_cut (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (R : ℝ) (hR : 1 ≤ R) :
    ENNReal.ofReal (1/(R+1)) * criticalCutMass F R ≤ criticalCostKernel F 2 := by
  rw [criticalCostKernel_two_swap F hF, criticalCutMass,
    ← lintegral_const_mul _ (criticalWeight_measurable.ennreal_ofReal.mul hF)]
  apply le_trans _ (lintegral_mono_set (show Ioo (1 : ℝ) R ⊆ Ioi 1 from fun _ h => h.1))
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  have hv0 : 0 < v := by linarith [hv.1]
  have hv1 : 0 ≤ v-1 := by linarith [hv.1]
  have hR0 : 0 < R+1 := by linarith
  have hh := mul_le_mul_left (critical_coefficient_linterval_lower R v hR hv.1 hv.2.le)
    (ENNReal.ofReal (criticalCoefficient v) * F v)
  have he : ENNReal.ofReal ((v-1)/(R+1)) *
      (ENNReal.ofReal (criticalCoefficient v) * F v) =
      ENNReal.ofReal (1/(R+1)) * (ENNReal.ofReal (criticalWeight v) * F v) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (v-1)/(R+1)),
      ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(R+1))]
    congr 2
    unfold criticalCoefficient criticalWeight
    field_simp
    ring
  rwa [he] at hh

/-- The constants chosen here are convenient, not optimized. -/
theorem criticalCostKernel_two_ge_one_div_44 (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (hM : criticalMass F = 1/2) (hV : criticalFirstMass F ≤ 5/2) :
    (1/44 : ℝ≥0∞) ≤ criticalCostKernel F 2 := by
  have hh := criticalMass_le_cut_add_first F hF 10 (by norm_num)
  rw [hM] at hh
  have hc := mul_le_mul_right hV (ENNReal.ofReal (1/(10 : ℝ)))
  have ha : ENNReal.ofReal (1/(10 : ℝ)) * (5/2 : ℝ≥0∞) = 1/4 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  have hb := hh.trans (add_le_add_right hc _)
  rw [ha] at hb
  have hcut : (1/4 : ℝ≥0∞) ≤ criticalCutMass F 10 := by
    apply ENNReal.le_of_add_le_add_right (a := (1/4 : ℝ≥0∞)) (by finiteness)
    have he : (1/4 : ℝ≥0∞)+1/4=1/2 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num
    rwa [he]
  have hl := (mul_le_mul_right hcut (ENNReal.ofReal (1/(10+1 : ℝ)))).trans
    (criticalCostKernel_two_ge_cut F hF 10 (by norm_num))
  norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 11)] at hl
  rw [← ENNReal.mul_inv (by norm_num) (by norm_num)] at hl
  norm_num at hl ⊢
  exact hl

#print axioms criticalCostKernel_two_ge_one_div_44
end Erdos970.ContinuousBuchstab
