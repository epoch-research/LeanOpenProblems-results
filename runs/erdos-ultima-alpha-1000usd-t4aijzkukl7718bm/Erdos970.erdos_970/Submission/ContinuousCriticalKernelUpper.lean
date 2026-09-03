import Submission.ContinuousCriticalNoSupersolution

/-! Pointwise upper bounds for the critical continuous cost kernel. These
bounds concern the continuous model, not the arithmetic sieve remainder. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology ENNReal
set_option maxHeartbeats 1800000

lemma criticalCoefficient_antitone {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    criticalCoefficient t ≤ criticalCoefficient a := by
  have ht : 0 < t := ha.trans_le hat
  have h1 := one_div_le_one_div_of_le ha hat
  have h2 := one_div_le_one_div_of_le (sq_pos_of_pos ha) (pow_le_pow_left₀ ha.le hat 2)
  have htne := ht.ne'
  have hane := ha.ne'
  have he (v : ℝ) (hv : v ≠ 0) : criticalCoefficient v = 1/v+1/v^2 := by
    unfold criticalCoefficient
    field_simp
  rw [he t htne, he a hane]
  exact add_le_add h1 h2

lemma criticalCoefficient_pos (t : ℝ) (ht : 0 < t) : 0 < criticalCoefficient t := by
  unfold criticalCoefficient
  positivity

lemma criticalCostKernel_swap (F : ℝ → ℝ≥0∞) (hF : Measurable F) (s : ℝ) :
    criticalCostKernel F s = ∫⁻ v : ℝ in Ioi 1,
      (∫⁻ t : ℝ in Ioo (max 2 (s-1)) (v+1),
        ENNReal.ofReal (criticalCoefficient t)) *
          (ENNReal.ofReal (criticalCoefficient v) * F v) := by
  let A : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (criticalCoefficient t)
  let G : ℝ → ℝ≥0∞ := fun v => A v * F v
  have hA : Measurable A := criticalCoefficient_measurable.ennreal_ofReal
  have hG : Measurable G := hA.mul hF
  have he : criticalCostKernel F s = ∫⁻ t : ℝ in Ioi (max 2 (s-1)),
      A t * (∫⁻ v : ℝ in Ioi 1, if t < v+1 then G v else 0) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [ltail_triangle G t ((le_max_left _ _).trans (mem_Ioi.mp ht).le)]
  rw [he, triangular_lintegral A G hA hG (max 2 (s-1)) 1]

lemma critical_coefficient_linterval_upper (a v : ℝ) (ha : 2 ≤ a) (hv : 1 < v) :
    (∫⁻ t : ℝ in Ioo a (v+1), ENNReal.ofReal (criticalCoefficient t)) ≤
      ENNReal.ofReal (criticalCoefficient a) * ENNReal.ofReal (v-1) := by
  have ha0 : 0 < a := by linarith
  have hh : (∫⁻ t : ℝ in Ioo a (v+1), ENNReal.ofReal (criticalCoefficient t)) ≤
      ∫⁻ _t : ℝ in Ioo a (v+1), ENNReal.ofReal (criticalCoefficient a) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact ENNReal.ofReal_le_ofReal (criticalCoefficient_antitone ha0 ht.1.le)
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo] at hh
  exact hh.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal (by linarith : v+1-a ≤ v-1)) _)

/-- The transition density relative to the invariant mass is bounded at every
fixed level. No total-mass finiteness assumption is needed for this inequality. -/
theorem criticalCostKernel_le_coefficient_mass (F : ℝ → ℝ≥0∞)
    (hF : Measurable F) (s : ℝ) :
    criticalCostKernel F s ≤
      ENNReal.ofReal (criticalCoefficient (max 2 (s-1))) * criticalMass F := by
  rw [criticalCostKernel_swap F hF s, criticalMass,
    ← lintegral_const_mul _ (criticalWeight_measurable.ennreal_ofReal.mul hF)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv1 : 1 < v := mem_Ioi.mp hv
  have hv0 : v ≠ 0 := by linarith
  have he : ENNReal.ofReal (v-1) * ENNReal.ofReal (criticalCoefficient v) =
      ENNReal.ofReal (criticalWeight v) := by
    rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ v-1)]
    congr 1
    unfold criticalCoefficient criticalWeight
    field_simp
    ring
  have hh := mul_le_mul_left
    (critical_coefficient_linterval_upper (max 2 (s-1)) v (le_max_left _ _) hv1)
    (ENNReal.ofReal (criticalCoefficient v) * F v)
  simpa only [mul_assoc, ← mul_assoc (ENNReal.ofReal (v-1)), he] using hh

/-- In particular the whole kernel is bounded by three quarters of the input
mass, uniformly in the real level s. -/
theorem criticalCostKernel_le_three_fourths_mass (F : ℝ → ℝ≥0∞)
    (hF : Measurable F) (s : ℝ) :
    criticalCostKernel F s ≤ (3/4 : ℝ≥0∞) * criticalMass F := by
  have hc := criticalCoefficient_antitone (by norm_num : (0 : ℝ) < 2)
    (le_max_left 2 (s-1))
  have hh := mul_le_mul_left (ENNReal.ofReal_le_ofReal hc) (criticalMass F)
  have he : ENNReal.ofReal (criticalCoefficient 2) = (3/4 : ℝ≥0∞) := by
    norm_num [criticalCoefficient, ENNReal.ofReal_div_of_pos]
  rw [he] at hh
  exact (criticalCostKernel_le_coefficient_mass F hF s).trans hh

/-- Together with the earlier lower bound this shows linear, rather than
superlinear, pointwise growth for the compact-source potential at level two. -/
theorem criticalCompactPotential_two_upper (n : ℕ) :
    criticalCompactPotential (n+1) 2 ≤ (3/8 : ℝ≥0∞)*n := by
  have hh := criticalCostKernel_le_three_fourths_mass
    (criticalCompactPotential n) (criticalCompactPotential_measurable n) 2
  rw [criticalCompactPotential_mass] at hh
  have he : (3/4 : ℝ≥0∞)*((n : ℝ≥0∞)/2) = (3/8 : ℝ≥0∞)*n := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat]
    ring
  simpa only [criticalCompactPotential, criticalCompactSource,
    indicator_of_notMem (show (2 : ℝ) ∉ Ioo 1 2 by simp), zero_add, he] using hh

#print axioms criticalCostKernel_le_coefficient_mass
#print axioms criticalCostKernel_le_three_fourths_mass
#print axioms criticalCompactPotential_two_upper
end Erdos970.ContinuousBuchstab
