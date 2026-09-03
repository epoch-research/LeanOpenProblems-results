import Submission.ContinuousBuchstabKernel

/-! Measurability, linearity, and exponential-envelope estimates for the
continuous Buchstab operator. No prime-sum transfer is asserted. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 1000000

noncomputable def tailIntegral (u : ℝ → ℝ) (a : ℝ) : ℝ := ∫ v in Ioi a, u v

lemma measurable_tailIntegral (u : ℝ → ℝ) (hu : Measurable u) :
    Measurable (tailIntegral u) := by
  classical
  have hm : Measurable (fun z : ℝ × ℝ => if z.1 < z.2 then u z.2 else 0) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      (hu.comp measurable_snd) measurable_const
  have hh := (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  convert hh using 1
  funext a
  exact (integral_indicator (f := u) measurableSet_Ioi).symm

lemma measurable_kernel (u : ℝ → ℝ) (hu : Measurable u) : Measurable (kernel u) := by
  have h1 : Measurable (fun t : ℝ => tailIntegral u (t-1)/t) :=
    ((measurable_tailIntegral u hu).comp (measurable_id.sub_const 1)).div measurable_id
  exact ((measurable_tailIntegral _ h1).comp
    (measurable_const.max (measurable_id.sub_const 1))).div measurable_id

lemma integrable_of_exp_envelope (u : ℝ → ℝ) (hu : Measurable u) (C a : ℝ)
    (hbound : ∀ s : ℝ, 1 ≤ s → |u s| ≤ C*exp (-s)) (ha : 1 ≤ a) :
    IntegrableOn u (Ioi a) := by
  apply ((integrableOn_exp_neg_Ioi a).const_mul C).mono' hu.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  simpa only [Real.norm_eq_abs] using hbound s (ha.trans (mem_Ioi.mp hs).le)

lemma abs_tailIntegral_le (u : ℝ → ℝ) (hu : Measurable u) (C a : ℝ)
    (hbound : ∀ s : ℝ, 1 ≤ s → |u s| ≤ C*exp (-s)) (ha : 1 ≤ a) :
    |tailIntegral u a| ≤ C*exp (-a) := by
  have hi := integrable_of_exp_envelope u hu C a hbound ha
  have hm := setIntegral_mono_on hi.norm ((integrableOn_exp_neg_Ioi a).const_mul C)
    measurableSet_Ioi (fun s hs => by
      simpa only [Real.norm_eq_abs] using hbound s (ha.trans (mem_Ioi.mp hs).le))
  rw [integral_const_mul, integral_exp_neg_Ioi] at hm
  exact (norm_integral_le_integral_norm u).trans hm

lemma abs_kernel_integrand_le (u : ℝ → ℝ) (hu : Measurable u) (C t : ℝ)
    (hbound : ∀ s : ℝ, 1 ≤ s → |u s| ≤ C*exp (-s)) (ht : 2 ≤ t) :
    |tailIntegral u (t-1)/t| ≤ (C*exp 1)*(exp (-t)/t) := by
  have ht0 : 0 < t := by linarith
  rw [abs_div, abs_of_pos ht0]
  have hh := div_le_div_of_nonneg_right
    (abs_tailIntegral_le u hu C (t-1) hbound (by linarith)) ht0.le
  have he : exp (-(t-1)) = exp 1*exp (-t) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he] at hh
  convert hh using 1 <;> ring

lemma integrable_kernel_integrand (u : ℝ → ℝ) (hu : Measurable u) (C a : ℝ)
    (hbound : ∀ s : ℝ, 1 ≤ s → |u s| ≤ C*exp (-s)) (ha : 2 ≤ a) :
    IntegrableOn (fun t => tailIntegral u (t-1)/t) (Ioi a) := by
  apply ((integrable_exp_div a ha).const_mul (C*exp 1)).mono'
  · exact (((measurable_tailIntegral u hu).comp
      (measurable_id.sub_const 1)).div measurable_id).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [Real.norm_eq_abs] using
      abs_kernel_integrand_le u hu C t hbound (ha.trans (mem_Ioi.mp ht).le)

lemma kernel_abs_le (u : ℝ → ℝ) (hu : Measurable u) (C s : ℝ)
    (hbound : ∀ v : ℝ, 1 ≤ v → |u v| ≤ C*exp (-v)) (hs : 1 ≤ s) :
    |kernel u s| ≤ C*kernel (fun v => exp (-v)) s := by
  let a := max 2 (s-1)
  have ha : 2 ≤ a := le_max_left _ _
  have hi := integrable_kernel_integrand u hu C a hbound ha
  have hm := setIntegral_mono_on hi.norm ((integrable_exp_div a ha).const_mul (C*exp 1))
    measurableSet_Ioi (fun t ht => by
      simpa only [Real.norm_eq_abs] using
        abs_kernel_integrand_le u hu C t hbound (ha.trans (mem_Ioi.mp ht).le))
  rw [integral_const_mul] at hm
  have hn := (norm_integral_le_integral_norm (fun t => tailIntegral u (t-1)/t)).trans hm
  have hh := div_le_div_of_nonneg_right hn (show 0 ≤ s by linarith)
  rw [kernel_exp_eq]
  unfold kernel
  rw [abs_div, abs_of_pos (show 0 < s by linarith)]
  convert hh using 1 <;> simp only [Real.norm_eq_abs, tailIntegral, a] <;> ring

/-- The full exponential-envelope contraction, including signed inputs. -/
theorem kernel_abs_le_exp (u : ℝ → ℝ) (hu : Measurable u) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ v : ℝ, 1 ≤ v → |u v| ≤ C*exp (-v)) (s : ℝ) (hs : 1 ≤ s) :
    |kernel u s| ≤ (C*(19/20))*exp (-s) := by
  have hh := (kernel_abs_le u hu C s hbound hs).trans
    (mul_le_mul_of_nonneg_left (kernel_exp_le s hs) hC)
  simpa only [mul_assoc] using hh

lemma kernel_nonneg (u : ℝ → ℝ) (hu : ∀ v : ℝ, 1 ≤ v → 0 ≤ u v)
    (s : ℝ) (hs : 1 ≤ s) : 0 ≤ kernel u s := by
  unfold kernel
  apply div_nonneg _ (by linarith)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht2 : 2 < t := (le_max_left _ _).trans_lt (mem_Ioi.mp ht)
  apply div_nonneg _ (by linarith)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact hu v (by linarith [mem_Ioi.mp hv])

lemma kernel_sub (u v : ℝ → ℝ) (hu : Measurable u) (hv : Measurable v) (C D : ℝ)
    (huB : ∀ s : ℝ, 1 ≤ s → |u s| ≤ C*exp (-s))
    (hvB : ∀ s : ℝ, 1 ≤ s → |v s| ≤ D*exp (-s)) (s : ℝ) :
    kernel (fun t => u t-v t) s = kernel u s-kernel v s := by
  let a := max 2 (s-1)
  have ha : 2 ≤ a := le_max_left _ _
  have he : (∫ t in Ioi a, (∫ z in Ioi (t-1), u z-v z)/t) =
      ∫ t in Ioi a, tailIntegral u (t-1)/t-tailIntegral v (t-1)/t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht1 : 1 ≤ t-1 := by linarith [mem_Ioi.mp ht]
    dsimp only
    rw [integral_sub (integrable_of_exp_envelope u hu C (t-1) huB ht1)
      (integrable_of_exp_envelope v hv D (t-1) hvB ht1), sub_div]
    rfl
  change (∫ t in Ioi a, (∫ z in Ioi (t-1), u z-v z)/t)/s = _
  rw [he, integral_sub (integrable_kernel_integrand u hu C a huB ha)
    (integrable_kernel_integrand v hv D a hvB ha), sub_div]
  rfl

lemma kernel_mono (u v : ℝ → ℝ) (hu : Measurable u) (hv : Measurable v) (C D : ℝ)
    (huB : ∀ s : ℝ, 1 ≤ s → |u s| ≤ C*exp (-s))
    (hvB : ∀ s : ℝ, 1 ≤ s → |v s| ≤ D*exp (-s))
    (h : ∀ t : ℝ, 1 ≤ t → u t ≤ v t) (s : ℝ) (hs : 1 ≤ s) :
    kernel u s ≤ kernel v s := by
  have hh := kernel_nonneg (fun t => v t-u t) (fun t ht => sub_nonneg.mpr (h t ht)) s hs
  rw [kernel_sub v u hv hu D C hvB huB] at hh
  linarith only [hh]

#print axioms kernel_abs_le_exp
#print axioms kernel_mono
end Erdos970.ContinuousBuchstab
