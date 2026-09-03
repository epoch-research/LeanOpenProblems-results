import Submission.ContinuousBuchstabOperator

/-! Fubini identities for the continuous Buchstab kernel, with absolute
integrability supplied explicitly. These identities concern only the model. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 1000000

lemma integrable_triangle_constant (a b c : ℝ) :
    IntegrableOn (fun s : ℝ => if s < b then c else 0) (Ioi a) := by
  classical
  change Integrable ((Iio b).indicator (fun _ : ℝ => c)) (volume.restrict (Ioi a))
  rw [integrable_indicator_iff measurableSet_Iio]
  change Integrable (fun _ : ℝ => c) ((volume.restrict (Ioi a)).restrict (Iio b))
  rw [Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
  exact integrableOn_const (by rw [volume_Ioo]; exact ENNReal.ofReal_ne_top)

lemma integral_triangle_constant (a b c : ℝ) (hab : a ≤ b) :
    (∫ s : ℝ in Ioi a, if s < b then c else 0) = (b-a)*c := by
  classical
  change (∫ s : ℝ in Ioi a, (Iio b).indicator (fun _ : ℝ => c) s) = _
  rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    Iio_inter_Ioi, setIntegral_const, measureReal_def, volume_Ioo,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul]

lemma integral_triangle_slice (f : ℝ → ℝ) (b c s : ℝ) :
    (∫ t : ℝ in Ioi c, if s < t+b then f t else 0) =
      tailIntegral f (max c (s-b)) := by
  classical
  have he : (fun t : ℝ => if s < t+b then f t else 0) =
      (Ioi (s-b)).indicator f := by
    funext t
    simp only [indicator_apply, mem_Ioi, sub_lt_iff_lt_add]
  rw [he, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioi, max_comm]
  rfl

/-- Weighted triangle identity. The sole integrability hypothesis is precisely
what is required by Fubini after the finite inner interval is evaluated. -/
theorem integral_tail_max (f : ℝ → ℝ) (hf : Measurable f) (a b c : ℝ)
    (habc : a ≤ c+b)
    (hweight : IntegrableOn (fun t => (t+b-a)*f t) (Ioi c)) :
    (∫ s : ℝ in Ioi a, tailIntegral f (max c (s-b))) =
      ∫ t : ℝ in Ioi c, (t+b-a)*f t := by
  classical
  let F : ℝ × ℝ → ℝ := fun z => if z.1 < z.2+b then f z.2 else 0
  have hF : Measurable F := Measurable.ite
    (measurableSet_lt measurable_fst (measurable_snd.add_const b))
    (hf.comp measurable_snd) measurable_const
  have hslice (t : ℝ) : IntegrableOn (fun s => F (s,t)) (Ioi a) :=
    integrable_triangle_constant a (t+b) (f t)
  have hnorm (t : ℝ) (ht : c < t) :
      (∫ s : ℝ in Ioi a, ‖F (s,t)‖) = ‖(t+b-a)*f t‖ := by
    have he : (fun s : ℝ => ‖F (s,t)‖) =
        (fun s => if s < t+b then |f t| else 0) := by
      funext s
      dsimp [F]
      split_ifs <;> simp [Real.norm_eq_abs]
    rw [he, integral_triangle_constant a (t+b) (|f t|) (by linarith),
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (show 0 ≤ t+b-a by linarith)]
  have hi : Integrable F ((volume.restrict (Ioi a)).prod (volume.restrict (Ioi c))) := by
    apply (integrable_prod_iff' hF.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall hslice, ?_⟩
    apply hweight.norm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hnorm t (mem_Ioi.mp ht)).symm
  have hs := integral_integral_swap (f := fun s t => F (s,t)) hi
  calc
    _ = ∫ s : ℝ in Ioi a, ∫ t : ℝ in Ioi c, F (s,t) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun s => (integral_triangle_slice f b c s).symm)
    _ = ∫ t : ℝ in Ioi c, ∫ s : ℝ in Ioi a, F (s,t) := hs
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact integral_triangle_constant a (t+b) (f t) (by linarith [mem_Ioi.mp ht])

lemma integrable_linear_exp :
    IntegrableOn (fun t : ℝ => t*exp (-t)) (Ioi 1) := by
  apply ((integrable_shifted_majorant 1).const_mul 32).mono'
  · exact (measurable_id.mul (Real.measurable_exp.comp measurable_neg)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := by linarith [mem_Ioi.mp ht]
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos ht0 (exp_pos _))]
    have hp : t ≤ (t-1)^2-6*(t-1)+16 := by nlinarith [sq_nonneg (t-9/2)]
    nlinarith only [mul_le_mul_of_nonneg_right hp (exp_pos (-t)).le]

lemma integral_linear_exp_le : (∫ t : ℝ in Ioi 1, t*exp (-t)) ≤ 12 := by
  have hh := setIntegral_mono_on integrable_linear_exp
    ((integrable_shifted_majorant 1).const_mul 32) measurableSet_Ioi (fun t _ => by
      have hp : t ≤ (t-1)^2-6*(t-1)+16 := by nlinarith [sq_nonneg (t-9/2)]
      nlinarith only [mul_le_mul_of_nonneg_right hp (exp_pos (-t)).le])
  rw [integral_const_mul, integral_shifted_majorant] at hh
  have he : exp (-(1 : ℝ)) ≤ 1 := exp_le_one_iff.mpr (by norm_num)
  linarith

lemma integrable_weighted_envelope (u : ℝ → ℝ) (hu : Measurable u) (C : ℝ)
    (hbound : ∀ t : ℝ, 1 ≤ t → |u t| ≤ C*exp (-t)) :
    IntegrableOn (fun t => t*u t) (Ioi 1) := by
  apply (integrable_linear_exp.const_mul C).mono'
  · exact (measurable_id.mul hu).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := by linarith [mem_Ioi.mp ht]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht0]
    have hh := mul_le_mul_of_nonneg_left (hbound t (mem_Ioi.mp ht).le) ht0
    convert hh using 1 <;> ring

/-- Multiplication by the outer variable cancels both kernel denominators
under Fubini. The resulting weight is exactly v-1, with no approximation. -/
theorem kernel_first_moment (u : ℝ → ℝ) (hu : Measurable u) (C : ℝ)
    (hbound : ∀ t : ℝ, 1 ≤ t → |u t| ≤ C*exp (-t)) :
    (∫ s : ℝ in Ioi 1, s*kernel u s) = ∫ v : ℝ in Ioi 1, (v-1)*u v := by
  let f : ℝ → ℝ := fun t => tailIntegral u (t-1)/t
  have hf : Measurable f := ((measurable_tailIntegral u hu).comp
    (measurable_id.sub_const 1)).div measurable_id
  have htail : IntegrableOn (fun t => tailIntegral u (t-1)) (Ioi 2) := by
    apply ((integrableOn_exp_neg_Ioi 2).const_mul (C*exp 1)).mono'
    · exact ((measurable_tailIntegral u hu).comp
        (measurable_id.sub_const 1)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hh := abs_tailIntegral_le u hu C (t-1) hbound (by linarith [mem_Ioi.mp ht])
      have he : exp (-(t-1)) = exp 1*exp (-t) := by
        rw [← exp_add]; congr 1; ring
      simpa only [Real.norm_eq_abs, he, mul_assoc] using hh
  have hfweight : IntegrableOn (fun t => (t+1-1)*f t) (Ioi 2) := by
    apply htail.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : t ≠ 0 := by linarith [mem_Ioi.mp ht]
    dsimp only [f]
    field_simp
    ring
  have huweight : IntegrableOn (fun t => (t+1-2)*u t) (Ioi 1) := by
    have hh := (integrable_weighted_envelope u hu C hbound).sub
      (integrable_of_exp_envelope u hu C 1 hbound le_rfl)
    change Integrable (fun t => (t+1-2)*u t) (volume.restrict (Ioi 1))
    apply hh.congr
    exact Eventually.of_forall (fun t => by dsimp; ring)
  calc
    _ = ∫ s : ℝ in Ioi 1, tailIntegral f (max 2 (s-1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      have hs0 : s ≠ 0 := by linarith [mem_Ioi.mp hs]
      dsimp [kernel, tailIntegral, f]
      field_simp
    _ = ∫ t : ℝ in Ioi 2, (t+1-1)*f t :=
      integral_tail_max f hf 1 1 2 (by norm_num) hfweight
    _ = ∫ t : ℝ in Ioi 2, tailIntegral u (max 1 (t-1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : t ≠ 0 := by linarith [mem_Ioi.mp ht]
      dsimp only
      rw [max_eq_right (by linarith [mem_Ioi.mp ht] : 1 ≤ t-1)]
      dsimp [f]
      field_simp
      ring
    _ = ∫ v : ℝ in Ioi 1, (v+1-2)*u v :=
      integral_tail_max u hu 2 1 1 (by norm_num) huweight
    _ = _ := by congr 1; funext v; ring

#print axioms integral_tail_max
#print axioms kernel_first_moment
end Erdos970.ContinuousBuchstab
