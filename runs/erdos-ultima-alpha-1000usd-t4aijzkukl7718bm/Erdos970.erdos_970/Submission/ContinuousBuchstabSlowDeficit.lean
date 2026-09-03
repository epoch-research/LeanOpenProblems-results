import Submission.ContinuousBuchstabSlowOperator

/-! Clipped deficits for general slowly exponentially dominated profiles.
The compact square-cutoff contribution is retained exactly. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 1800000

noncomputable def slowDeficit (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t < 2 then 1 else min 1 (tailIntegral u (t-1)/t)

lemma slowDeficit_measurable (u : ℝ → ℝ) (hu : Measurable u) : Measurable (slowDeficit u) := by
  apply Measurable.ite measurableSet_Iio measurable_const
  exact measurable_const.min (((measurable_tailIntegral u hu).comp
    (measurable_id.sub_const 1)).div measurable_id)

lemma slowDeficit_le_one (u : ℝ → ℝ) (t : ℝ) : slowDeficit u t ≤ 1 := by
  unfold slowDeficit
  split_ifs
  · rfl
  · exact min_le_left _ _

lemma slowDeficit_nonneg (u : ℝ → ℝ) (hu : ∀ t, 1 ≤ t → 0 ≤ u t) (t : ℝ) :
    0 ≤ slowDeficit u t := by
  unfold slowDeficit
  split_ifs with ht
  · norm_num
  · exact le_min (by norm_num)
      (div_nonneg (tailIntegral_nonneg_on u 1 (t-1) hu (by linarith)) (by linarith))

lemma slowDeficit_antitone (u : ℝ → ℝ) (hfi : IntegrableOn u (Ioi 1))
    (hu : ∀ t, 1 ≤ t → 0 ≤ u t) : AntitoneOn (slowDeficit u) (Ici 0) := by
  have htail := tailIntegral_antitoneOn_of_integrable u 1 hfi hu
  intro x hx y hy hxy
  by_cases hx2 : x < 2
  · rw [show slowDeficit u x=1 by simp only [slowDeficit,if_pos hx2]]
    exact slowDeficit_le_one u y
  · have hy2 : ¬y < 2 := by linarith
    simp only [slowDeficit,if_neg hx2,if_neg hy2]
    apply min_le_min le_rfl
    have hm := htail (show 1 ≤ x-1 by linarith) (show 1 ≤ y-1 by linarith)
      (by linarith : x-1 ≤ y-1)
    have hp := tailIntegral_nonneg_on u 1 (x-1) hu (by linarith)
    exact (div_le_div_of_nonneg_right hm (by linarith : 0 ≤ y)).trans
      (div_le_div_of_nonneg_left hp (by linarith : 0 < x) hxy)

lemma slowDeficit_le_integrand (u : ℝ → ℝ) (t : ℝ) (ht : 2 ≤ t) :
    slowDeficit u t ≤ tailIntegral u (t-1)/t := by
  rw [slowDeficit,if_neg (not_lt_of_ge ht)]
  exact min_le_right _ _

lemma slowDeficit_exp_tail (u : ℝ → ℝ) (hu : Measurable u) (C : ℝ) (hC : 0 ≤ C)
    (hu0 : ∀ t, 1 ≤ t → 0 ≤ u t)
    (huB : ∀ t, 1 ≤ t → |u t| ≤ C*exp ((-2/3 : ℝ)*t)) (t : ℝ) (ht : 2 ≤ t) :
    |slowDeficit u t| ≤ (3*C/2*exp (2/3))*exp ((-2/3 : ℝ)*t) := by
  rw [abs_of_nonneg (slowDeficit_nonneg u hu0 t)]
  have hh := abs_kernel_slow_integrand_le u hu C t huB ht
  have hd := (slowDeficit_le_integrand u t ht).trans (le_abs_self _)
  have hm : exp ((-2/3 : ℝ)*t)/t ≤ exp ((-2/3 : ℝ)*t) := by
    apply (div_le_iff₀ (by linarith : 0 < t)).mpr
    nlinarith only [ht,exp_pos ((-2/3 : ℝ)*t)]
  exact (hd.trans hh).trans (mul_le_mul_of_nonneg_left hm (by positivity))

lemma slowDeficit_integrable (u : ℝ → ℝ) (hu : Measurable u) (C : ℝ) (hC : 0 ≤ C)
    (hu0 : ∀ t, 1 ≤ t → 0 ≤ u t)
    (huB : ∀ t, 1 ≤ t → |u t| ≤ C*exp ((-2/3 : ℝ)*t)) :
    IntegrableOn (slowDeficit u) (Ioi 0) := by
  have hleft : IntegrableOn (slowDeficit u) (Ioc 0 2) := by
    apply (integrableOn_const (C := (1 : ℝ)) (μ := volume) (s := Ioc 0 2)
      (by rw [volume_Ioc]; exact ENNReal.ofReal_ne_top)).mono' (slowDeficit_measurable u hu).aestronglyMeasurable
    exact Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (slowDeficit_nonneg u hu0 t)]
      exact slowDeficit_le_one u t)
  have hright : IntegrableOn (slowDeficit u) (Ioi 2) := by
    apply ((integrableOn_exp_mul_Ioi (by norm_num : (-2/3 : ℝ) < 0) 2).const_mul
      (3*C/2*exp (2/3))).mono' (slowDeficit_measurable u hu).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [Real.norm_eq_abs] using slowDeficit_exp_tail u hu C hC hu0 huB t (mem_Ioi.mp ht).le
  simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 2)] using hleft.union hright

/-- The full deficit tail, including levels below two, is at most the
forcing term plus the two-step continuous kernel. -/
theorem slowDeficit_tail_le (u : ℝ → ℝ) (hu : Measurable u) (C : ℝ) (hC : 0 ≤ C)
    (hu0 : ∀ t, 1 ≤ t → 0 ≤ u t)
    (huB : ∀ t, 1 ≤ t → |u t| ≤ C*exp ((-2/3 : ℝ)*t))
    (s : ℝ) (hs : 1 ≤ s) :
    tailIntegral (slowDeficit u) (s-1)/s ≤ forcing s+kernel u s := by
  let a := s-1
  let b := max 2 a
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hab : a ≤ b := le_max_right _ _
  have hb2 : 2 ≤ b := le_max_left _ _
  have hia := (slowDeficit_integrable u hu C hC hu0 huB).mono_set (Ioi_subset_Ioi ha)
  have hleft := hia.mono_set (show Ioc a b ⊆ Ioi a from fun _ h => h.1)
  have hright := hia.mono_set (Ioi_subset_Ioi hab)
  have he : tailIntegral (slowDeficit u) a =
      (∫ t : ℝ in Ioc a b, slowDeficit u t)+tailIntegral (slowDeficit u) b := by
    unfold tailIntegral
    rw [← Ioc_union_Ioi_eq_Ioi hab,setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hleft hright]
  have hfirst := setIntegral_mono_on hleft
    (integrableOn_const (C := (1 : ℝ)) (μ := volume) (s := Ioc a b)
      (by rw [volume_Ioc]; exact ENNReal.ofReal_ne_top)) measurableSet_Ioc
    (fun t _ => slowDeficit_le_one u t)
  rw [setIntegral_const,measureReal_def,volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab),smul_eq_mul,mul_one] at hfirst
  have hsecond := setIntegral_mono_on hright
    (integrable_kernel_slow_integrand u hu C b huB hb2) measurableSet_Ioi
    (fun t ht => slowDeficit_le_integrand u t (hb2.trans (mem_Ioi.mp ht).le))
  have htotal : tailIntegral (slowDeficit u) a ≤
      b-a+∫ t : ℝ in Ioi b, tailIntegral u (t-1)/t := by
    rw [he]
    exact add_le_add hfirst hsecond
  have hba : b-a=max (3-s) 0 := by
    dsimp [b,a]
    rw [← max_sub_sub_right,sub_self]
    congr 1
    ring
  have hh := div_le_div_of_nonneg_right htotal (show 0 ≤ s by linarith)
  rw [hba,add_div] at hh
  exact hh

lemma augmentedUpper_tail_bound (H : ℝ) (hH : 0 ≤ H) (n : ℕ) (s : ℝ) (hs : 2 ≤ s) :
    tailIntegral (augmentedUpper H n) (s-1) ≤ 2+(24000+2*H)*(19/20 : ℝ)^n := by
  have hs1 : 1 ≤ s-1 := by linarith
  have h1 := (upperEnvelope_integrable n).mono_set (Ioi_subset_Ioi hs1)
  have h2 := (integrableOn_exp_mul_Ioi (by norm_num : (-2/3 : ℝ) < 0) (s-1)).const_mul
    (H*(19/20 : ℝ)^n)
  have ht := (tailIntegral_upperEnvelope_le_mass n s hs).trans (mass_bounds n).2
  have he : exp ((-2/3 : ℝ)*(s-1)) ≤ 1 := exp_le_one_iff.mpr (by linarith only [hs])
  have hp := mul_le_mul_of_nonneg_left he (show 0 ≤ H*(19/20 : ℝ)^n*(3/2) by positivity)
  change (∫ t : ℝ in Ioi (s-1), upperEnvelope n t+H*(19/20 : ℝ)^n*exp ((-2/3 : ℝ)*t)) ≤ _
  rw [integral_add h1 h2,integral_const_mul,integral_slow_exp]
  change tailIntegral (upperEnvelope n) (s-1)+_ ≤ _
  have hHp : 0 ≤ H*(19/20 : ℝ)^n := by positivity
  nlinarith only [ht,hp,hHp]

#print axioms slowDeficit_tail_le
#print axioms augmentedUpper_tail_bound
end Erdos970.ContinuousBuchstab
