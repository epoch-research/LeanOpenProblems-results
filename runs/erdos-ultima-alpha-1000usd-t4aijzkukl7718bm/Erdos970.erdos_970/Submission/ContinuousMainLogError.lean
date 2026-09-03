import Submission.ContinuousCriticalNoSupersolution

/-! The continuous propagation operator for a normalized main-term error
with one inverse logarithm is conjugate to the critical cost operator.
This is an analytic-model identity, not a finite-prime transfer theorem
and not a proof or disproof of the Jacobsthal conjecture. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology ENNReal
set_option maxHeartbeats 1600000

/-- A half-step multiplies a child inverse-logarithmic error by `(t+1)/s`.
Together with the main-term measure `dt/s`, this gives this two-step
operator. The lower-node square cutoff is retained. -/
noncomputable def mainLogErrorKernel (H : ℝ → ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1/s^2) *
    ∫⁻ t : ℝ in Ioi (max 2 (s-1)), ENNReal.ofReal ((t+1)/t^2) *
      (∫⁻ v : ℝ in Ioi (t-1), ENNReal.ofReal (v+1)*H v)

noncomputable def mainErrorScale (H : ℝ → ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (s^2)*H s

lemma criticalCoefficient_scale (v : ℝ) (hv : 0 < v) :
    ENNReal.ofReal (criticalCoefficient v)*ENNReal.ofReal (v^2) =
      ENNReal.ofReal (v+1) := by
  rw [← ENNReal.ofReal_mul (by dsimp [criticalCoefficient]; positivity)]
  congr 1
  unfold criticalCoefficient
  exact div_mul_cancel₀ _ (sq_pos_of_pos hv).ne'

lemma square_inverse_scale (s : ℝ) (hs : s ≠ 0) :
    ENNReal.ofReal (s^2)*ENNReal.ofReal (1/s^2)=1 := by
  rw [← ENNReal.ofReal_mul (sq_nonneg s)]
  have he : s^2*(1/s^2)=(1 : ℝ) := by field_simp
  rw [he,ENNReal.ofReal_one]

/-- Exact conjugacy. In particular, contraction of the unweighted main
operator does not imply contraction of its inverse-logarithmic errors. -/
theorem mainLogErrorKernel_conjugate (H : ℝ → ℝ≥0∞) (s : ℝ) (hs : s ≠ 0) :
    mainErrorScale (mainLogErrorKernel H) s =
      criticalCostKernel (mainErrorScale H) s := by
  unfold mainErrorScale mainLogErrorKernel
  rw [← mul_assoc,square_inverse_scale s hs,one_mul]
  unfold criticalCostKernel
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  apply congrArg (ENNReal.ofReal ((t+1)/t^2) * ·)
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  have ht2 : (2 : ℝ) < t := (le_max_left _ _).trans_lt (mem_Ioi.mp ht)
  have hv0 : 0 < v := by linarith only [ht2,mem_Ioi.mp hv]
  rw [← mul_assoc,criticalCoefficient_scale v hv0]

/-- Conjugating a source-plus-kernel supersolution retains the source. -/
lemma mainLogError_supersolution_scale (S H : ℝ → ℝ≥0∞)
    (hH : ∀ s : ℝ, 1 < s → S s+mainLogErrorKernel H s ≤ H s) :
    ∀ s : ℝ, 1 < s → mainErrorScale S s+
      criticalCostKernel (mainErrorScale H) s ≤ mainErrorScale H s := by
  intro s hs
  have hh := mul_le_mul_right (hH s hs) (ENNReal.ofReal (s^2))
  rw [mul_add] at hh
  change mainErrorScale S s+mainErrorScale (mainLogErrorKernel H) s ≤ _ at hh
  rw [mainLogErrorKernel_conjugate H s (by linarith)] at hh
  exact hh

/-- A source bounded below on (1,2) forces any supersolution of the
inverse-log main-error model to be infinite at level two. No finite-mass
or measurability condition on the prospective supersolution is assumed. -/
theorem positive_mainLogError_supersolution_two_top (S H : ℝ → ℝ≥0∞)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcfin : c ≠ ⊤)
    (hS : ∀ s : ℝ, 1 < s → s < 2 → c ≤ S s)
    (hH : ∀ s : ℝ, 1 < s → S s+mainLogErrorKernel H s ≤ H s) :
    H 2 = ⊤ := by
  have hS' : ∀ s : ℝ, 1 < s → s < 2 → c ≤ mainErrorScale S s := by
    intro s hs hs2
    have hsq : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (s^2) := by
      simpa only [ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ s^2 by nlinarith)
    have hh : S s ≤ mainErrorScale S s := by
      simpa only [one_mul,mainErrorScale] using
        mul_le_mul hsq (le_refl (S s)) (zero_le _) (zero_le _)
    exact (hS s hs hs2).trans hh
  have hh := positive_source_supersolution_two_top (mainErrorScale S) (mainErrorScale H)
    c hc0 hcfin hS' (mainLogError_supersolution_scale S H hH)
  change ENNReal.ofReal ((2 : ℝ)^2)*H 2=⊤ at hh
  rcases ENNReal.mul_eq_top.mp hh with hh | hh
  · exact hh.2
  · exact False.elim (ENNReal.ofReal_ne_top hh.1)

/-- A positive exponential quadrature-error allowance cannot be absorbed
by a finite real-valued, depth-independent envelope for this model. -/
theorem no_real_exponential_mainLogError_supersolution (H : ℝ → ℝ)
    (a : ℝ) (ha : 0 ≤ a) :
    ¬∀ s : ℝ, 1 < s → ENNReal.ofReal (exp (-a*s))+
      mainLogErrorKernel (fun v => ENNReal.ofReal (H v)) s ≤ ENNReal.ofReal (H s) := by
  intro hH
  have hh := positive_mainLogError_supersolution_two_top
    (fun s => ENNReal.ofReal (exp (-a*s))) (fun s => ENNReal.ofReal (H s))
    (ENNReal.ofReal (exp (-2*a)))
    (ENNReal.ofReal_ne_zero_iff.mpr (exp_pos _)) ENNReal.ofReal_ne_top
    (fun s hs hs2 => ENNReal.ofReal_le_ofReal (exp_le_exp.mpr (by nlinarith))) hH
  exact ENNReal.ofReal_ne_top hh

#print axioms mainLogErrorKernel_conjugate
#print axioms positive_mainLogError_supersolution_two_top
#print axioms no_real_exponential_mainLogError_supersolution
end Erdos970.ContinuousBuchstab
