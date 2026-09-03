import Submission.ContinuousCriticalPotential

/-! The continuous critical positive-cost obstruction without any finite-mass
assumption. It applies to pointwise supersolutions for that model only; it is
not a lower bound on the arithmetic sieve error or a Jacobsthal disproof. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology ENNReal
set_option maxHeartbeats 1800000

lemma criticalCostKernel_const_mul (F : ℝ → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ⊤) (s : ℝ) :
    criticalCostKernel (fun v => c * F v) s = c * criticalCostKernel F s := by
  unfold criticalCostKernel
  have he (t : ℝ) :
      (∫⁻ v : ℝ in Ioi (t-1), ENNReal.ofReal (criticalCoefficient v) * (c * F v)) =
        c * (∫⁻ v : ℝ in Ioi (t-1), ENNReal.ofReal (criticalCoefficient v) * F v) := by
    simp_rw [mul_left_comm (ENNReal.ofReal (criticalCoefficient _)) c]
    exact lintegral_const_mul' c _ hc
  simp_rw [he, mul_left_comm (ENNReal.ofReal (criticalCoefficient _)) c]
  exact lintegral_const_mul' c _ hc

lemma compact_source_le_of_positive (S : ℝ → ℝ≥0∞) (c : ℝ≥0∞)
    (hS : ∀ s : ℝ, 1 < s → s < 2 → c ≤ S s) (s : ℝ) :
    c * criticalCompactSource s ≤ S s := by
  classical
  by_cases hs : s ∈ Ioo (1 : ℝ) 2
  · simpa only [criticalCompactSource, indicator_of_mem hs, mul_one] using hS s hs.1 hs.2
  · simp only [criticalCompactSource, indicator_of_notMem hs, mul_zero, zero_le]

/-- A source bounded below by a positive constant on (1,2) forces every
supersolution to have infinite value at 2, even if its total mass is infinite. -/
theorem positive_source_supersolution_two_top (S F : ℝ → ℝ≥0∞) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcfin : c ≠ ⊤)
    (hS : ∀ s : ℝ, 1 < s → s < 2 → c ≤ S s)
    (hF : ∀ s : ℝ, 1 < s → S s + criticalCostKernel F s ≤ F s) :
    F 2 = ⊤ := by
  have hcinv : c⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hc0
  let H : ℝ → ℝ≥0∞ := fun s => c⁻¹ * F s
  have hH : ∀ s : ℝ, 1 < s → criticalCompactSource s + criticalCostKernel H s ≤ H s := by
    intro s hs
    have hh := (add_le_add_left (compact_source_le_of_positive S c hS s) _).trans (hF s hs)
    have hm := mul_le_mul_right hh c⁻¹
    rw [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hcfin, one_mul,
      ← criticalCostKernel_const_mul F c⁻¹ hcinv s] at hm
    exact hm
  have hh := criticalCompactSource_supersolution_two_top H hH
  change c⁻¹ * F 2 = ⊤ at hh
  rcases ENNReal.mul_eq_top.mp hh with hh | hh
  · exact hh.2
  · exact False.elim (hcinv hh.1)

/-- In particular an exponentially decaying positive source cannot be absorbed
by any everywhere finite real-valued critical error profile. No integrability
assumption on that profile has been inserted. -/
theorem no_real_exponential_critical_supersolution (F : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a) :
    ¬∀ s : ℝ, 1 < s → ENNReal.ofReal (exp (-a*s)) +
      criticalCostKernel (fun v => ENNReal.ofReal (F v)) s ≤ ENNReal.ofReal (F s) := by
  intro hF
  have hh := positive_source_supersolution_two_top
    (fun s => ENNReal.ofReal (exp (-a*s))) (fun s => ENNReal.ofReal (F s))
    (ENNReal.ofReal (exp (-2*a)))
    (ENNReal.ofReal_ne_zero_iff.mpr (exp_pos _)) ENNReal.ofReal_ne_top
    (fun s hs hs2 => ENNReal.ofReal_le_ofReal (exp_le_exp.mpr (by nlinarith))) hF
  exact ENNReal.ofReal_ne_top hh

/-- The outer maximum of the complete model recurrence cannot avoid the
compact-source potential. -/
lemma scaled_compactPotential_le_iteration (S B : ℝ → ℝ≥0∞) (c : ℝ≥0∞) (hcfin : c ≠ ⊤)
    (hS : ∀ s : ℝ, 1 < s → s < 2 → c ≤ S s) (n : ℕ) :
    ∀ s : ℝ, 1 < s → c * criticalCompactPotential n s ≤ criticalCostIteration S B n s := by
  induction n with
  | zero => intro s hs; simp only [criticalCompactPotential, mul_zero, zero_le]
  | succ n ih =>
    intro s hs
    have hk := criticalCostKernel_mono ih s
    rw [criticalCostKernel_const_mul _ c hcfin s] at hk
    have hh := add_le_add (compact_source_le_of_positive S c hS s) hk
    have he : c * criticalCompactPotential (n+1) s =
        c * criticalCompactSource s + c * criticalCostKernel (criticalCompactPotential n) s := by
      simp only [criticalCompactPotential, mul_add]
    rw [he]
    exact hh.trans (le_max_right _ _)

/-- Linear pointwise growth in the full positive model, with its outer maximum
retained. This does not assert growth of the actual arithmetic error. -/
theorem criticalCostIteration_two_growth (S B : ℝ → ℝ≥0∞) (c : ℝ≥0∞) (hcfin : c ≠ ⊤)
    (hS : ∀ s : ℝ, 1 < s → s < 2 → c ≤ S s) (n : ℕ) :
    c * ((n : ℝ≥0∞)/44) ≤ criticalCostIteration S B (n+1) 2 :=
  (mul_le_mul_right (criticalCompactPotential_two_growth n) c).trans
    (scaled_compactPotential_le_iteration S B c hcfin hS (n+1) 2 (by norm_num))

#print axioms positive_source_supersolution_two_top
#print axioms no_real_exponential_critical_supersolution
#print axioms criticalCostIteration_two_growth
end Erdos970.ContinuousBuchstab
