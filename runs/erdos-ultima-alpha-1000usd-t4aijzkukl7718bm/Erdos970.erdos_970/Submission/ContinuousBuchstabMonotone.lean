import Submission.ContinuousBuchstabPositivity

/-! Monotonicity of the continuous profiles, for finite-sector transfer. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
set_option maxHeartbeats 1000000

lemma tailIntegral_nonneg_on (f : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ t : ℝ, a ≤ t → 0 ≤ f t) (hab : a ≤ b) : 0 ≤ tailIntegral f b := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact hf t (hab.trans (mem_Ioi.mp ht).le)

lemma tailIntegral_antitoneOn_of_integrable (f : ℝ → ℝ) (a : ℝ)
    (hi : IntegrableOn f (Ioi a)) (hf : ∀ t : ℝ, a ≤ t → 0 ≤ f t) :
    AntitoneOn (tailIntegral f) (Ici a) := by
  intro x hx y hy hxy
  apply setIntegral_mono_set (hi.mono_set (Ioi_subset_Ioi (mem_Ici.mp hx)))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hf t ((mem_Ici.mp hx).trans (mem_Ioi.mp ht).le)
  · exact Eventually.of_forall (fun t ht => by
      change x < t
      change y < t at ht
      linarith only [ht,hxy])

lemma kernel_antitoneOn (u : ℝ → ℝ) (hu : Measurable u) (C : ℝ)
    (hbound : ∀ t : ℝ, 1 ≤ t → |u t| ≤ C*exp (-t))
    (hpos : ∀ t : ℝ, 1 ≤ t → 0 ≤ u t) : AntitoneOn (kernel u) (Ici 1) := by
  let f : ℝ → ℝ := fun t => tailIntegral u (t-1)/t
  have hf : ∀ t : ℝ, 2 ≤ t → 0 ≤ f t := by
    intro t ht
    exact div_nonneg (tailIntegral_nonneg_on u 1 (t-1) hpos (by linarith)) (by linarith)
  have hmono := tailIntegral_antitoneOn_of_integrable f 2
    (integrable_kernel_integrand u hu C 2 hbound le_rfl) hf
  intro x hx y hy hxy
  have hx1 := mem_Ici.mp hx
  have hy1 := mem_Ici.mp hy
  have hcut : max 2 (x-1) ≤ max 2 (y-1) := max_le_max_left _ (by linarith)
  have hm := hmono (le_max_left 2 (x-1)) (le_max_left 2 (y-1)) hcut
  have hp := tailIntegral_nonneg_on f 2 (max 2 (x-1)) hf (le_max_left _ _)
  have hh := (div_le_div_of_nonneg_right hm (by linarith : 0 ≤ y)).trans
    (div_le_div_of_nonneg_left hp (by linarith : 0 < x) hxy)
  exact hh

lemma forcing_antitoneOn : AntitoneOn forcing (Ici 1) := by
  intro x hx y hy hxy
  have hx1 := mem_Ici.mp hx
  have hy1 := mem_Ici.mp hy
  have hm : max (3-y) 0 ≤ max (3-x) 0 := max_le_max_right _ (by linarith)
  exact (div_le_div_of_nonneg_right hm (by linarith : 0 ≤ y)).trans
    (div_le_div_of_nonneg_left (le_max_right _ _) (by linarith : 0 < x) hxy)

lemma upperEnvelope_antitoneOn (n : ℕ) : AntitoneOn (upperEnvelope n) (Ici 1) := by
  cases n with
  | zero =>
      intro x hx y hy hxy
      exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg hxy)) (by norm_num)
  | succ n =>
      have hk := kernel_antitoneOn (upperEnvelope n) (measurable_upperEnvelope n) 2000
        (upperEnvelope_exp_bound n) (upperEnvelope_nonneg n)
      intro x hx y hy hxy
      exact add_le_add (forcing_antitoneOn hx hy hxy) (hk hx hy hxy)

lemma lowerProfile_monotoneOn (n : ℕ) : MonotoneOn (lowerProfile n) (Ici 2) := by
  have ht := tailIntegral_antitoneOn_of_integrable (upperEnvelope n) 1
    (upperEnvelope_integrable n) (upperEnvelope_nonneg n)
  intro x hx y hy hxy
  have hx2 := mem_Ici.mp hx
  have hy2 := mem_Ici.mp hy
  have hm := ht (show x-1 ∈ Ici (1 : ℝ) by change 1 ≤ x-1; linarith)
    (show y-1 ∈ Ici (1 : ℝ) by change 1 ≤ y-1; linarith) (by linarith : x-1 ≤ y-1)
  have hp := tailIntegral_nonneg_on (upperEnvelope n) 1 (x-1) (upperEnvelope_nonneg n) (by linarith)
  have hh := (div_le_div_of_nonneg_right hm (by linarith : 0 ≤ y)).trans
    (div_le_div_of_nonneg_left hp (by linarith : 0 < x) hxy)
  exact sub_le_sub_left hh 1

#print axioms upperEnvelope_antitoneOn
#print axioms lowerProfile_monotoneOn
end Erdos970.ContinuousBuchstab
