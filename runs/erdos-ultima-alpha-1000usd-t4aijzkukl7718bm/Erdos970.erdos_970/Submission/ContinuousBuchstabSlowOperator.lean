import Submission.ContinuousBuchstabSlowKernel
import Submission.ContinuousBuchstabDeficit

/-! Integrability and linearity of the continuous Buchstab operator for
slow exponential envelopes. These are analytic model estimates only. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 1800000

lemma integrable_of_slow_envelope (u : ℝ → ℝ) (hu : Measurable u) (C a : ℝ)
    (hbound : ∀ s : ℝ, 1 ≤ s → |u s| ≤ C*exp ((-2/3 : ℝ)*s)) (ha : 1 ≤ a) :
    IntegrableOn u (Ioi a) := by
  apply ((integrableOn_exp_mul_Ioi (by norm_num : (-2/3 : ℝ) < 0) a).const_mul C).mono'
    hu.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  simpa only [Real.norm_eq_abs] using hbound s (ha.trans (mem_Ioi.mp hs).le)

lemma integral_slow_exp (a : ℝ) :
    (∫ t : ℝ in Ioi a, exp ((-2/3 : ℝ)*t))=(3/2 : ℝ)*exp ((-2/3 : ℝ)*a) := by
  rw [integral_exp_mul_Ioi (by norm_num : (-2/3 : ℝ) < 0)]
  ring

lemma abs_tailIntegral_slow_le (u : ℝ → ℝ) (hu : Measurable u) (C a : ℝ)
    (hbound : ∀ s : ℝ, 1 ≤ s → |u s| ≤ C*exp ((-2/3 : ℝ)*s)) (ha : 1 ≤ a) :
    |tailIntegral u a| ≤ (3*C/2)*exp ((-2/3 : ℝ)*a) := by
  have hi := integrable_of_slow_envelope u hu C a hbound ha
  have hm := setIntegral_mono_on hi.norm
    ((integrableOn_exp_mul_Ioi (by norm_num : (-2/3 : ℝ) < 0) a).const_mul C)
    measurableSet_Ioi (fun s hs => by
      simpa only [Real.norm_eq_abs] using hbound s (ha.trans (mem_Ioi.mp hs).le))
  rw [integral_const_mul,integral_slow_exp] at hm
  have hh := (norm_integral_le_integral_norm u).trans hm
  simpa only [Real.norm_eq_abs,tailIntegral] using hh.trans_eq (by ring)

lemma abs_kernel_slow_integrand_le (u : ℝ → ℝ) (hu : Measurable u) (C t : ℝ)
    (hbound : ∀ s : ℝ, 1 ≤ s → |u s| ≤ C*exp ((-2/3 : ℝ)*s)) (ht : 2 ≤ t) :
    |tailIntegral u (t-1)/t| ≤ (3*C/2*exp (2/3))* (exp ((-2/3 : ℝ)*t)/t) := by
  have ht0 : 0 < t := by linarith
  rw [abs_div,abs_of_pos ht0]
  have hh := div_le_div_of_nonneg_right
    (abs_tailIntegral_slow_le u hu C (t-1) hbound (by linarith)) ht0.le
  have he : exp ((-2/3 : ℝ)*(t-1))=exp (2/3)*exp ((-2/3 : ℝ)*t) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he] at hh
  convert hh using 1 <;> ring

lemma integrable_kernel_slow_integrand (u : ℝ → ℝ) (hu : Measurable u) (C a : ℝ)
    (hbound : ∀ s : ℝ, 1 ≤ s → |u s| ≤ C*exp ((-2/3 : ℝ)*s)) (ha : 2 ≤ a) :
    IntegrableOn (fun t => tailIntegral u (t-1)/t) (Ioi a) := by
  apply ((integrable_slow_exp_div a ha).const_mul (3*C/2*exp (2/3))).mono'
  · exact (((measurable_tailIntegral u hu).comp
      (measurable_id.sub_const 1)).div measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [Real.norm_eq_abs] using
      abs_kernel_slow_integrand_le u hu C t hbound (ha.trans (mem_Ioi.mp ht).le)

lemma kernel_slow_add (u v : ℝ → ℝ) (hu : Measurable u) (hv : Measurable v) (C D : ℝ)
    (huB : ∀ s : ℝ, 1 ≤ s → |u s| ≤ C*exp ((-2/3 : ℝ)*s))
    (hvB : ∀ s : ℝ, 1 ≤ s → |v s| ≤ D*exp ((-2/3 : ℝ)*s)) (s : ℝ) :
    kernel (fun t => u t+v t) s=kernel u s+kernel v s := by
  let a := max 2 (s-1)
  have ha : 2 ≤ a := le_max_left _ _
  have he : (∫ t in Ioi a, (∫ z in Ioi (t-1), u z+v z)/t) =
      ∫ t in Ioi a, tailIntegral u (t-1)/t+tailIntegral v (t-1)/t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht1 : 1 ≤ t-1 := by linarith only [ha,mem_Ioi.mp ht]
    dsimp only
    rw [integral_add (integrable_of_slow_envelope u hu C (t-1) huB ht1)
      (integrable_of_slow_envelope v hv D (t-1) hvB ht1),add_div]
    rfl
  unfold kernel
  change (∫ t in Ioi a, (∫ z in Ioi (t-1), u z+v z)/t)/s = _
  rw [he,integral_add (integrable_kernel_slow_integrand u hu C a huB ha)
    (integrable_kernel_slow_integrand v hv D a hvB ha),add_div]
  rfl

lemma kernel_const_mul_unrestricted (u : ℝ → ℝ) (c s : ℝ) :
    kernel (fun t => c*u t) s=c*kernel u s := by
  unfold kernel
  simp_rw [integral_const_mul,mul_div_assoc]
  rw [integral_const_mul]
  ring

noncomputable def augmentedUpper (H : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  upperEnvelope n s+H*(19/20 : ℝ)^n*exp ((-2/3 : ℝ)*s)

lemma augmentedUpper_measurable (H : ℝ) (n : ℕ) : Measurable (augmentedUpper H n) := by
  exact (measurable_upperEnvelope n).add (by fun_prop)

lemma augmentedUpper_nonneg (H : ℝ) (hH : 0 ≤ H) (n : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    0 ≤ augmentedUpper H n s :=
  add_nonneg (upperEnvelope_nonneg n s hs) (by positivity)

lemma augmentedUpper_antitone (H : ℝ) (hH : 0 ≤ H) (n : ℕ) :
    AntitoneOn (augmentedUpper H n) (Ici 1) := by
  intro s hs t ht hst
  have hmono := exp_le_exp.mpr (mul_le_mul_of_nonpos_left hst (by norm_num : (-2/3 : ℝ) ≤ 0))
  exact add_le_add (upperEnvelope_antitoneOn n hs ht hst)
    (mul_le_mul_of_nonneg_left hmono (by positivity))

lemma upperEnvelope_slow_bound (n : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    |upperEnvelope n s| ≤ 2000*exp ((-2/3 : ℝ)*s) := by
  apply (upperEnvelope_exp_bound n s hs).trans
  exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith only [hs])) (by norm_num)

lemma augmentedUpper_slow_bound (H : ℝ) (hH : 0 ≤ H) (n : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    |augmentedUpper H n s| ≤ (2000+H*(19/20 : ℝ)^n)*exp ((-2/3 : ℝ)*s) := by
  rw [abs_of_nonneg (augmentedUpper_nonneg H hH n s hs)]
  have hh := (le_abs_self (upperEnvelope n s)).trans (upperEnvelope_slow_bound n s hs)
  dsimp only [augmentedUpper]
  nlinarith only [hh]

lemma augmentedUpper_integrable (H : ℝ) (hH : 0 ≤ H) (n : ℕ) :
    IntegrableOn (augmentedUpper H n) (Ioi 1) :=
  integrable_of_slow_envelope _ (augmentedUpper_measurable H n) _ 1
    (augmentedUpper_slow_bound H hH n) le_rfl

/-- The augmented envelopes form a two-step supersolution with geometric
decay of the additional slow initial allowance. -/
theorem augmentedUpper_next (H : ℝ) (hH : 0 ≤ H) (n : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    forcing s+kernel (augmentedUpper H n) s ≤ augmentedUpper H (n+1) s := by
  have hslow : ∀ t : ℝ, 1 ≤ t →
      |H*(19/20 : ℝ)^n*exp ((-2/3 : ℝ)*t)| ≤
        (H*(19/20 : ℝ)^n)*exp ((-2/3 : ℝ)*t) := by
    intro t ht
    rw [abs_of_nonneg (by positivity)]
  change forcing s+kernel (fun t => upperEnvelope n t+H*(19/20 : ℝ)^n*exp ((-2/3 : ℝ)*t)) s ≤ _
  rw [kernel_slow_add _ _ (measurable_upperEnvelope n)
    (by fun_prop) 2000 (H*(19/20 : ℝ)^n) (upperEnvelope_slow_bound n) hslow,
    kernel_const_mul_unrestricted]
  have hk := mul_le_mul_of_nonneg_left (kernel_slow_exp_le s hs)
    (show 0 ≤ H*(19/20 : ℝ)^n by positivity)
  change forcing s+(kernel (upperEnvelope n) s+_) ≤
    (forcing s+kernel (upperEnvelope n) s)+H*(19/20 : ℝ)^(n+1)*exp ((-2/3 : ℝ)*s)
  rw [pow_succ]
  nlinarith only [hk]

#print axioms kernel_slow_add
#print axioms augmentedUpper_next
end Erdos970.ContinuousBuchstab
