import Submission.ContinuousBuchstabRectangles

/-! The clipped lower-deficit profile used in actual prime-sum transfer. The
square cutoff is retained, and its complete tail is bounded by the next upper
envelope, not identified with it. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
set_option maxHeartbeats 1000000

noncomputable def deficitProfile (n : ℕ) (t : ℝ) : ℝ :=
  if t < 2 then 1 else min 1 (tailIntegral (upperEnvelope n) (t-1)/t)

lemma measurable_deficitProfile (n : ℕ) : Measurable (deficitProfile n) := by
  apply Measurable.ite measurableSet_Iio measurable_const
  exact measurable_const.min (((measurable_tailIntegral _ (measurable_upperEnvelope n)).comp
    (measurable_id.sub_const 1)).div measurable_id)

lemma deficitProfile_le_one (n : ℕ) (t : ℝ) : deficitProfile n t ≤ 1 := by
  unfold deficitProfile
  split_ifs
  · rfl
  · exact min_le_left _ _

lemma deficitProfile_nonneg (n : ℕ) (t : ℝ) : 0 ≤ deficitProfile n t := by
  unfold deficitProfile
  split_ifs with ht
  · norm_num
  · apply le_min (by norm_num)
    have ht2 : 2 ≤ t := le_of_not_gt ht
    exact div_nonneg (tailIntegral_nonneg_on (upperEnvelope n) 1 (t-1)
      (upperEnvelope_nonneg n) (by linarith)) (by linarith)

lemma deficitProfile_eq_one_sub_max (n : ℕ) (t : ℝ) (ht : 2 ≤ t) :
    deficitProfile n t = 1-max 0 (lowerProfile n t) := by
  rw [deficitProfile,if_neg (not_lt_of_ge ht),lowerProfile]
  by_cases h : tailIntegral (upperEnvelope n) (t-1)/t ≤ 1
  · rw [min_eq_right h,max_eq_right (by linarith)]
    ring
  · rw [min_eq_left (by linarith),max_eq_left (by linarith)]
    ring

lemma deficitProfile_antitoneOn (n : ℕ) : AntitoneOn (deficitProfile n) (Ici 0) := by
  intro x hx y hy hxy
  by_cases hx2 : x < 2
  · rw [show deficitProfile n x=1 by simp [deficitProfile,hx2]]
    exact deficitProfile_le_one n y
  · have hx2' : 2 ≤ x := le_of_not_gt hx2
    have hy2 : 2 ≤ y := hx2'.trans hxy
    rw [deficitProfile_eq_one_sub_max n x hx2',deficitProfile_eq_one_sub_max n y hy2]
    exact sub_le_sub_left (max_le_max_left 0 ((lowerProfile_monotoneOn n) hx2' hy2 hxy)) 1

lemma deficitProfile_le_integrand (n : ℕ) (t : ℝ) (ht : 2 ≤ t) :
    deficitProfile n t ≤ tailIntegral (upperEnvelope n) (t-1)/t := by
  rw [deficitProfile,if_neg (not_lt_of_ge ht)]
  exact min_le_right _ _

lemma deficitProfile_exp_tail (n : ℕ) (t : ℝ) (ht : 2 ≤ t) :
    |deficitProfile n t| ≤ (2000*exp 1)*exp (-t) := by
  rw [abs_of_nonneg (deficitProfile_nonneg n t)]
  have hh := abs_kernel_integrand_le (upperEnvelope n) (measurable_upperEnvelope n) 2000 t
    (upperEnvelope_exp_bound n) ht
  have hd := (deficitProfile_le_integrand n t ht).trans (le_abs_self _)
  have ht0 : 0 < t := by linarith
  have hm : exp (-t)/t ≤ exp (-t) := by
    apply (div_le_iff₀ ht0).mpr
    nlinarith only [ht,exp_pos (-t)]
  exact (hd.trans hh).trans (mul_le_mul_of_nonneg_left hm (by positivity))

lemma deficitProfile_integrable (n : ℕ) : IntegrableOn (deficitProfile n) (Ioi 0) := by
  have hleft : IntegrableOn (deficitProfile n) (Ioc 0 2) := by
    apply (integrableOn_const (C := (1 : ℝ)) (μ := volume) (s := Ioc 0 2)
      (by rw [volume_Ioc]; exact ENNReal.ofReal_ne_top)).mono' (measurable_deficitProfile n).aestronglyMeasurable
    exact Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (deficitProfile_nonneg n t)]
      exact deficitProfile_le_one n t)
  have hright : IntegrableOn (deficitProfile n) (Ioi 2) := by
    apply ((integrableOn_exp_neg_Ioi 2).const_mul (2000*exp 1)).mono'
      (measurable_deficitProfile n).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simpa only [Real.norm_eq_abs] using deficitProfile_exp_tail n t (mem_Ioi.mp ht).le
  simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 2)] using hleft.union hright

/-- The entire clipped deficit tail is bounded by the next upper envelope.
The compact part has length max(3-s,0); the rest is the actual kernel integral. -/
theorem deficit_tail_le_upperEnvelope (n : ℕ) (s : ℝ) (hs : 1 ≤ s) :
    tailIntegral (deficitProfile n) (s-1)/s ≤ upperEnvelope (n+1) s := by
  let a := s-1
  let b := max 2 a
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hab : a ≤ b := le_max_right _ _
  have hb2 : 2 ≤ b := le_max_left _ _
  have hia := (deficitProfile_integrable n).mono_set (Ioi_subset_Ioi ha)
  have hleft := hia.mono_set (show Ioc a b ⊆ Ioi a from fun _ h => h.1)
  have hright := hia.mono_set (Ioi_subset_Ioi hab)
  have he : tailIntegral (deficitProfile n) a =
      (∫ t : ℝ in Ioc a b, deficitProfile n t)+tailIntegral (deficitProfile n) b := by
    unfold tailIntegral
    rw [← Ioc_union_Ioi_eq_Ioi hab,setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hleft hright]
  have hfirst := setIntegral_mono_on hleft
    (integrableOn_const (C := (1 : ℝ)) (μ := volume) (s := Ioc a b)
      (by rw [volume_Ioc]; exact ENNReal.ofReal_ne_top)) measurableSet_Ioc
    (fun t _ => deficitProfile_le_one n t)
  rw [setIntegral_const,measureReal_def,volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab),smul_eq_mul,mul_one] at hfirst
  have hsecond := setIntegral_mono_on hright
    (integrable_kernel_integrand (upperEnvelope n) (measurable_upperEnvelope n) 2000 b
      (upperEnvelope_exp_bound n) hb2) measurableSet_Ioi
    (fun t ht => deficitProfile_le_integrand n t (hb2.trans (mem_Ioi.mp ht).le))
  have htotal : tailIntegral (deficitProfile n) a ≤
      b-a+∫ t : ℝ in Ioi b, tailIntegral (upperEnvelope n) (t-1)/t := by
    rw [he]
    exact add_le_add hfirst hsecond
  have hba : b-a = max (3-s) 0 := by
    dsimp [b,a]
    rw [← max_sub_sub_right,sub_self]
    congr 1
    ring
  have hs0 : 0 < s := by linarith
  have hh := div_le_div_of_nonneg_right htotal hs0.le
  rw [hba,add_div] at hh
  exact hh

#print axioms deficitProfile_antitoneOn
#print axioms deficitProfile_integrable
#print axioms deficit_tail_le_upperEnvelope
end Erdos970.ContinuousBuchstab
