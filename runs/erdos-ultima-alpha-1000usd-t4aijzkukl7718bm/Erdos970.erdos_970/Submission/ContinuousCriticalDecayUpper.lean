import Submission.ContinuousCriticalLinearUpper

/-! First-moment and level-decaying upper bounds for the critical continuous
cost iteration. These do not estimate the actual arithmetic sieve error. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology ENNReal
set_option maxHeartbeats 1800000

lemma criticalFirstMass_mono {F G : ℝ → ℝ≥0∞}
    (h : ∀ s : ℝ, 1 < s → F s ≤ G s) : criticalFirstMass F ≤ criticalFirstMass G := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact mul_le_mul_right (h s (mem_Ioi.mp hs)) _

lemma criticalCostIteration_mass_upper_coarse (S B : ℝ → ℝ≥0∞)
    (hS : Measurable S) (hB : Measurable B) (n : ℕ) :
    criticalMass (criticalCostIteration S B n) ≤
      ((n : ℝ≥0∞)+1)*(criticalMass B+criticalMass S) := by
  apply (criticalCostIteration_mass_upper S B hS hB n).trans
  rw [mul_add]
  exact add_le_add le_rfl (mul_le_mul_left (le_add_right (le_refl (n : ℝ≥0∞))) _)

lemma critical_half_mix (J T : ℝ≥0∞) :
    (1/2 : ℝ≥0∞)*(2*J+5*T)+(5/2 : ℝ≥0∞)*T ≤ 2*J+5*T := by
  have htwo : (1/2 : ℝ≥0∞)*2 = 1 := by
    norm_num [ENNReal.inv_mul_cancel]
  have hfive : (1/2 : ℝ≥0∞)*5+5/2=5 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num
  rw [mul_add, ← mul_assoc, htwo, one_mul, add_assoc,
    ← mul_assoc, ← add_mul, hfive]
  exact add_le_add (le_mul_of_one_le_left' (by norm_num : (1 : ℝ≥0∞) ≤ 2)) le_rfl

/-- The first moment has a linear bound as well. Finiteness assumptions are
not needed: all inequalities are valid in the nonnegative extended reals. -/
theorem criticalCostIteration_first_upper (S B : ℝ → ℝ≥0∞)
    (hS : Measurable S) (hB : Measurable B) (n : ℕ) :
    criticalFirstMass (criticalCostIteration S B n) ≤ ((n : ℝ≥0∞)+1)*
      (2*(criticalFirstMass B+criticalFirstMass S)+5*(criticalMass B+criticalMass S)) := by
  let J := criticalFirstMass B+criticalFirstMass S
  let T := criticalMass B+criticalMass S
  let W := 2*J+5*T
  have hJW : J ≤ W := by
    exact (le_mul_of_one_le_left' (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (le_add_right le_rfl)
  change criticalFirstMass (criticalCostIteration S B n) ≤ ((n : ℝ≥0∞)+1)*W
  induction n with
  | zero =>
    simpa only [criticalCostIteration, Nat.cast_zero, zero_add, one_mul] using
      (show criticalFirstMass B ≤ J from le_add_right le_rfl).trans hJW
  | succ n ih =>
    have hm := criticalFirstMass_mono (F := criticalCostIteration S B (n+1))
      (G := fun s => B s+(S s+criticalCostKernel (criticalCostIteration S B n) s))
      (fun s _ => by
        rw [criticalCostIteration_fixed_obstacle]
        exact max_le_add_of_nonneg (zero_le _) (zero_le _))
    rw [criticalFirstMass_add _ _ hB, criticalFirstMass_add _ _ hS] at hm
    have hd := criticalFirstMass_kernel_le (criticalCostIteration S B n)
      (criticalCostIteration_measurable S B hS hB n)
    have hi := add_le_add (mul_le_mul_right ih (1/2 : ℝ≥0∞))
      (mul_le_mul_right (criticalCostIteration_mass_upper_coarse S B hS hB n) (5/2 : ℝ≥0∞))
    have he : (1/2 : ℝ≥0∞)*(((n : ℝ≥0∞)+1)*W)+
        (5/2 : ℝ≥0∞)*(((n : ℝ≥0∞)+1)*T) =
          ((n : ℝ≥0∞)+1)*((1/2 : ℝ≥0∞)*W+(5/2 : ℝ≥0∞)*T) := by ring
    change _ ≤ (1/2 : ℝ≥0∞)*(((n : ℝ≥0∞)+1)*W)+
      (5/2 : ℝ≥0∞)*(((n : ℝ≥0∞)+1)*T) at hi
    rw [he] at hi
    have hk := (hd.trans hi).trans (mul_le_mul_right (critical_half_mix J T) ((n : ℝ≥0∞)+1))
    have hh := hm.trans (add_le_add le_rfl (add_le_add le_rfl hk))
    have hb : criticalFirstMass B+(criticalFirstMass S+((n : ℝ≥0∞)+1)*W) ≤
        W+((n : ℝ≥0∞)+1)*W := by
      rw [← add_assoc]
      exact add_le_add hJW le_rfl
    apply (hh.trans hb).trans_eq
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    ring

/-- A sharper level bound charges the first moment instead of the total mass.
The transition can only receive mass from v>max(2,s-1)-1. -/
theorem criticalCostKernel_le_coefficient_firstMass (F : ℝ → ℝ≥0∞)
    (hF : Measurable F) (s : ℝ) :
    criticalCostKernel F s ≤
      ENNReal.ofReal (criticalCoefficient (max 2 (s-1))/(max 2 (s-1)-1)) * criticalFirstMass F := by
  let a : ℝ := max 2 (s-1)
  have ha : 2 ≤ a := le_max_left _ _
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a-1 := by linarith
  have hc := criticalCoefficient_pos a ha0
  rw [criticalCostKernel_swap F hF s, criticalFirstMass,
    ← lintegral_const_mul _ (show Measurable (fun v : ℝ =>
      ENNReal.ofReal v*ENNReal.ofReal (criticalWeight v)*F v) from
        (measurable_id.ennreal_ofReal.mul criticalWeight_measurable.ennreal_ofReal).mul hF)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv1 : 1 < v := mem_Ioi.mp hv
  have hv0 : v ≠ 0 := by linarith
  change (∫⁻ t : ℝ in Ioo a (v+1), ENNReal.ofReal (criticalCoefficient t)) *
    (ENNReal.ofReal (criticalCoefficient v)*F v) ≤
      ENNReal.ofReal (criticalCoefficient a/(a-1)) *
        (ENNReal.ofReal v*ENNReal.ofReal (criticalWeight v)*F v)
  by_cases hAv : a-1 ≤ v
  · have he : ENNReal.ofReal (v-1)*ENNReal.ofReal (criticalCoefficient v) =
        ENNReal.ofReal (criticalWeight v) := by
      rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ v-1)]
      congr 1
      unfold criticalCoefficient criticalWeight
      field_simp
      ring
    have hh := mul_le_mul_left (critical_coefficient_linterval_upper a v ha hv1)
      (ENNReal.ofReal (criticalCoefficient v)*F v)
    have hh' : (∫⁻ t : ℝ in Ioo a (v+1), ENNReal.ofReal (criticalCoefficient t)) *
        (ENNReal.ofReal (criticalCoefficient v)*F v) ≤
          ENNReal.ofReal (criticalCoefficient a)*(ENNReal.ofReal (criticalWeight v)*F v) := by
      simpa only [mul_assoc, ← mul_assoc (ENNReal.ofReal (v-1)), he] using hh
    apply hh'.trans
    have hr : criticalCoefficient a ≤ criticalCoefficient a/(a-1)*v := by
      have hh := mul_le_mul_of_nonneg_left hAv (div_nonneg hc.le ha1.le)
      have he : criticalCoefficient a/(a-1)*(a-1) = criticalCoefficient a := div_mul_cancel₀ _ ha1.ne'
      rwa [he] at hh
    have heN : ENNReal.ofReal (criticalCoefficient a) ≤
        ENNReal.ofReal (criticalCoefficient a/(a-1))*ENNReal.ofReal v := by
      rw [← ENNReal.ofReal_mul (div_nonneg hc.le ha1.le)]
      exact ENNReal.ofReal_le_ofReal hr
    simpa only [mul_assoc] using mul_le_mul_left heN (ENNReal.ofReal (criticalWeight v)*F v)
  · have hempty : Ioo a (v+1) = ∅ := Ioo_eq_empty_of_le (by linarith)
    simp only [hempty, Measure.restrict_empty, lintegral_zero_measure, zero_mul, zero_le]

lemma critical_coefficient_first_le_inv_square (s : ℝ) (hs : 1 < s) :
    criticalCoefficient (max 2 (s-1))/(max 2 (s-1)-1) ≤ 16/s^2 := by
  let a : ℝ := max 2 (s-1)
  have ha : 2 ≤ a := le_max_left _ _
  have hsA : s ≤ 2*a := by have := le_max_right 2 (s-1); dsimp [a] at *; linarith
  have hs0 : 0 < s := by linarith
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a-1 := by linarith
  have hsq : s^2 ≤ 4*a^2 := by nlinarith [pow_le_pow_left₀ hs0.le hsA 2]
  have h1 := mul_le_mul_of_nonneg_left hsq (show 0 ≤ a+1 by linarith)
  have h2 := mul_le_mul_of_nonneg_left (show a+1 ≤ 4*(a-1) by linarith)
    (show 0 ≤ 4*a^2 by positivity)
  have he : criticalCoefficient a/(a-1) = (a+1)/(a^2*(a-1)) := by
    unfold criticalCoefficient
    rw [div_div]
  change criticalCoefficient a/(a-1) ≤ _
  rw [he]
  apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos ha0) ha1) (sq_pos_of_pos hs0)).mpr
  nlinarith only [h1,h2]

/-- The level decay and linear first-moment bounds can now be used together.
This still concerns only the continuous model. -/
theorem criticalCostKernel_le_inv_square_firstMass (F : ℝ → ℝ≥0∞)
    (hF : Measurable F) (s : ℝ) (hs : 1 < s) :
    criticalCostKernel F s ≤ ENNReal.ofReal (16/s^2)*criticalFirstMass F :=
  (criticalCostKernel_le_coefficient_firstMass F hF s).trans
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal (critical_coefficient_first_le_inv_square s hs)) _)

/-- Combined linear-depth and inverse-square-level bound, still retaining
the outer maximum, initial profile, source, and both input moments. -/
theorem criticalCostIteration_pointwise_decay_upper (S B : ℝ → ℝ≥0∞)
    (hS : Measurable S) (hB : Measurable B) (n : ℕ) (s : ℝ) (hs : 1 < s) :
    criticalCostIteration S B (n+1) s ≤ max (B s)
      (S s+ENNReal.ofReal (16/s^2)*(((n : ℝ≥0∞)+1)*
        (2*(criticalFirstMass B+criticalFirstMass S)+5*(criticalMass B+criticalMass S)))) := by
  rw [criticalCostIteration_fixed_obstacle]
  apply max_le_max le_rfl
  apply add_le_add le_rfl
  exact (criticalCostKernel_le_inv_square_firstMass _
    (criticalCostIteration_measurable S B hS hB n) s hs).trans
    (mul_le_mul_right (criticalCostIteration_first_upper S B hS hB n) _)

#print axioms criticalCostIteration_first_upper
#print axioms criticalCostKernel_le_coefficient_firstMass
#print axioms criticalCostIteration_pointwise_decay_upper
#print axioms criticalCostKernel_le_inv_square_firstMass
end Erdos970.ContinuousBuchstab
