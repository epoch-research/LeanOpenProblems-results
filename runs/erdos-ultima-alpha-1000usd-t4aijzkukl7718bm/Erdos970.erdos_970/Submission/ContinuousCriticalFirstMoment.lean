import Submission.ContinuousBuchstabCriticalMass

/-! A first-moment drift estimate for the continuous critical positive-cost
operator. This concerns only that error model, not Jacobsthal's function. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology ENNReal
set_option maxHeartbeats 1800000

noncomputable def criticalFirstMass (F : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ s : ℝ in Ioi 1, ENNReal.ofReal s * ENNReal.ofReal (criticalWeight s) * F s

lemma critical_first_linterval_le (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ s : ℝ in Ioo 1 (t+1), ENNReal.ofReal s * ENNReal.ofReal (criticalWeight s)) ≤
      ENNReal.ofReal (t+1) * ENNReal.ofReal (t^2/(t+1)) := by
  rw [← criticalWeight_linterval t ht,
    ← lintegral_const_mul _ criticalWeight_measurable.ennreal_ofReal]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hs.2.le) _

lemma critical_linear_linterval (v : ℝ) (hv : 1 ≤ v) :
    (∫⁻ t : ℝ in Ioo 2 (v+1), ENNReal.ofReal (t+1)) =
      ENNReal.ofReal ((v-1)*(v+5)/2) := by
  have hint : IntegrableOn (fun t : ℝ => t+1) (Ioo 2 (v+1)) :=
    ((continuous_id.add continuous_const).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hn : 0 ≤ᵐ[volume.restrict (Ioo 2 (v+1))] (fun t : ℝ => t+1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change 0 ≤ t+1
    linarith [ht.1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hn,
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith : (2 : ℝ) ≤ v+1),
    intervalIntegral.integral_add intervalIntegral.intervalIntegrable_id
      intervalIntegral.intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  congr 1
  ring

lemma integrated_critical_linear_tail (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ t : ℝ in Ioi 2, ENNReal.ofReal (t+1) * (∫⁻ v : ℝ in Ioi (t-1), G v)) =
      ∫⁻ v : ℝ in Ioi 1, ENNReal.ofReal ((v-1)*(v+5)/2) * G v := by
  have he : (∫⁻ t : ℝ in Ioi 2, ENNReal.ofReal (t+1) * (∫⁻ v : ℝ in Ioi (t-1), G v)) =
      ∫⁻ t : ℝ in Ioi 2, ENNReal.ofReal (t+1) *
        (∫⁻ v : ℝ in Ioi 1, if t < v+1 then G v else 0) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [ltail_triangle G t (mem_Ioi.mp ht).le]
  rw [he, triangular_lintegral (fun t : ℝ => ENNReal.ofReal (t+1)) G
    ((measurable_id.add_const 1).ennreal_ofReal) hG 2 1]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [critical_linear_linterval v (mem_Ioi.mp hv).le]

lemma critical_first_coefficient (v : ℝ) (hv : 1 < v) :
    ENNReal.ofReal ((v-1)*(v+5)/2) * ENNReal.ofReal (criticalCoefficient v) =
      (1/2 : ℝ≥0∞) * (ENNReal.ofReal v * ENNReal.ofReal (criticalWeight v)) +
        (5/2 : ℝ≥0∞) * ENNReal.ofReal (criticalWeight v) := by
  have hv0 : 0 < v := by linarith
  have hw := criticalWeight_nonneg v hv.le
  have hv1 : 0 ≤ v-1 := by linarith
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (v-1)*(v+5)/2)]
  have he : ((v-1)*(v+5)/2) * criticalCoefficient v =
      (1/2 : ℝ)*(v*criticalWeight v) + (5/2 : ℝ)*criticalWeight v := by
    unfold criticalCoefficient criticalWeight
    field_simp
    ring
  rw [he, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5/2),
    ENNReal.ofReal_mul hv0.le]
  norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Mass has inward drift: its first moment contracts by one half, up to
five halves of the invariant mass. No finite-mass hypothesis is needed
for the inequality, since all terms are nonnegative extended integrals. -/
theorem criticalFirstMass_kernel_le (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    criticalFirstMass (criticalCostKernel F) ≤
      (1/2 : ℝ≥0∞)*criticalFirstMass F + (5/2 : ℝ≥0∞)*criticalMass F := by
  let A : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (criticalCoefficient t)
  let G : ℝ → ℝ≥0∞ := fun v => A v * F v
  let H : ℝ → ℝ≥0∞ := fun t => A t * (∫⁻ v : ℝ in Ioi (t-1), G v)
  have hA : Measurable A := criticalCoefficient_measurable.ennreal_ofReal
  have hG : Measurable G := hA.mul hF
  have hH : Measurable H := hA.mul (measurable_ltail G hG)
  have hw : Measurable (fun s : ℝ => ENNReal.ofReal s * ENNReal.ofReal (criticalWeight s)) :=
    measurable_id.ennreal_ofReal.mul criticalWeight_measurable.ennreal_ofReal
  have hstep : criticalFirstMass (criticalCostKernel F) ≤
      ∫⁻ t : ℝ in Ioi 2, ENNReal.ofReal (t+1) * (∫⁻ v : ℝ in Ioi (t-1), G v) := by
    unfold criticalFirstMass
    simp_rw [criticalCostKernel_triangle]
    rw [triangular_lintegral _ _ hw hH 1 2]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := by linarith [mem_Ioi.mp ht]
    have hh := mul_le_mul_left (critical_first_linterval_le t ht0.le) (H t)
    have he : (ENNReal.ofReal (t+1) * ENNReal.ofReal (t^2/(t+1))) * H t =
        ENNReal.ofReal (t+1) * (∫⁻ v : ℝ in Ioi (t-1), G v) := by
      dsimp only [H, A]
      rw [mul_assoc, ← mul_assoc (ENNReal.ofReal (t^2/(t+1))),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ t^2/(t+1))]
      have hid : t^2/(t+1)*criticalCoefficient t = 1 := by
        unfold criticalCoefficient
        field_simp
      rw [hid, ENNReal.ofReal_one, one_mul]
    rwa [he] at hh
  rw [integrated_critical_linear_tail G hG] at hstep
  apply hstep.trans_eq
  have he : (∫⁻ v : ℝ in Ioi 1, ENNReal.ofReal ((v-1)*(v+5)/2) * G v) =
      ∫⁻ v : ℝ in Ioi 1,
        (1/2 : ℝ≥0∞)*(ENNReal.ofReal v * ENNReal.ofReal (criticalWeight v) * F v) +
          (5/2 : ℝ≥0∞)*(ENNReal.ofReal (criticalWeight v) * F v) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only [G, A]
    rw [← mul_assoc, critical_first_coefficient v (mem_Ioi.mp hv), add_mul]
    simp only [mul_assoc]
  rw [he, lintegral_add_left (measurable_const.mul (hw.mul hF)),
    lintegral_const_mul _ (hw.mul hF),
    lintegral_const_mul _ (criticalWeight_measurable.ennreal_ofReal.mul hF)]
  rfl

#print axioms criticalFirstMass_kernel_le
end Erdos970.ContinuousBuchstab
