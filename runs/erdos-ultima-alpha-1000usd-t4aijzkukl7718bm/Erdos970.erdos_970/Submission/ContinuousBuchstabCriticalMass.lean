import Submission.ContinuousBuchstabSlowKernel

/-! An invariant positive mass for the continuous two-step cost operator at
inverse-log-square scale. This is an obstruction for a continuous error
supersolution, not a result about the Jacobsthal conjecture. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology ENNReal
set_option maxHeartbeats 1600000

noncomputable def criticalWeight (s : ℝ) : ℝ := 1-1/s^2
noncomputable def criticalCoefficient (s : ℝ) : ℝ := (s+1)/s^2

lemma criticalWeight_nonneg (s : ℝ) (hs : 1 ≤ s) : 0 ≤ criticalWeight s := by
  unfold criticalWeight
  have hs0 : 0 < s := by linarith
  have hh : 1/s^2 ≤ (1 : ℝ) := (div_le_one (sq_pos_of_pos hs0)).mpr (by nlinarith)
  linarith

lemma criticalWeight_measurable : Measurable criticalWeight := by
  unfold criticalWeight
  fun_prop

lemma criticalCoefficient_measurable : Measurable criticalCoefficient := by
  unfold criticalCoefficient
  fun_prop

lemma criticalWeight_continuousOn (b : ℝ) : ContinuousOn criticalWeight (Icc 1 b) := by
  unfold criticalWeight
  exact continuousOn_const.sub (continuousOn_const.div (continuousOn_id.pow 2)
    (fun s hs => pow_ne_zero _ (by linarith [hs.1] : s ≠ 0)))

lemma criticalWeight_primitive (s : ℝ) (hs : s ≠ 0) :
    HasDerivAt (fun x : ℝ => x+1/x) (criticalWeight s) s := by
  have hh := (hasDerivAt_id s).add ((hasDerivAt_const s (1 : ℝ)).div (hasDerivAt_id s) hs)
  convert hh using 1 <;> dsimp [criticalWeight] <;> ring

lemma criticalWeight_interval (t : ℝ) (ht : 0 ≤ t) :
    (∫ s : ℝ in Ioo 1 (t+1), criticalWeight s) = t^2/(t+1) := by
  have hle : (1 : ℝ) ≤ t+1 := by linarith
  have hint : IntervalIntegrable criticalWeight volume 1 (t+1) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hle]
    exact criticalWeight_continuousOn (t+1)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s : ℝ => s+1/s)
    (f' := criticalWeight) (a := 1) (b := t+1) (by
      intro s hs
      rw [uIcc_of_le hle] at hs
      exact criticalWeight_primitive s (by linarith [hs.1])) hint
  rw [intervalIntegral.integral_of_le hle,integral_Ioc_eq_integral_Ioo] at hh
  rw [hh]
  have ht1 : t+1 ≠ 0 := by linarith
  field_simp
  ring

lemma criticalWeight_linterval (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ s : ℝ in Ioo 1 (t+1), ENNReal.ofReal (criticalWeight s)) =
      ENNReal.ofReal (t^2/(t+1)) := by
  have hi := ((criticalWeight_continuousOn (t+1)).integrableOn_Icc (μ := volume)).mono_set Ioo_subset_Icc_self
  have hn : 0 ≤ᵐ[volume.restrict (Ioo 1 (t+1))] criticalWeight := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact criticalWeight_nonneg s hs.1.le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,criticalWeight_interval t ht]

/-- Tonelli on a triangular region, with no finiteness assumptions. -/
lemma triangular_lintegral (w H : ℝ → ℝ≥0∞) (hw : Measurable w) (hH : Measurable H)
    (a b : ℝ) :
    (∫⁻ s : ℝ in Ioi a, w s*(∫⁻ t : ℝ in Ioi b, if s < t+1 then H t else 0)) =
      ∫⁻ t : ℝ in Ioi b, (∫⁻ s : ℝ in Ioo a (t+1), w s)*H t := by
  classical
  have hm : Measurable (fun z : ℝ × ℝ => if z.1 < z.2+1 then w z.1*H z.2 else 0) :=
    Measurable.ite (measurableSet_lt measurable_fst (measurable_snd.add_const 1))
      ((hw.comp measurable_fst).mul (hH.comp measurable_snd)) measurable_const
  have hex (s : ℝ) : w s*(∫⁻ t : ℝ in Ioi b, if s < t+1 then H t else 0) =
      ∫⁻ t : ℝ in Ioi b, if s < t+1 then w s*H t else 0 := by
    have hmeas : Measurable (fun t : ℝ => if s < t+1 then H t else 0) :=
      Measurable.ite (measurableSet_lt measurable_const (measurable_id.add_const 1)) hH measurable_const
    rw [← lintegral_const_mul _ hmeas]
    apply lintegral_congr
    intro t
    split_ifs <;> simp
  simp_rw [hex]
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro t
  have he : (fun s : ℝ => if s < t+1 then w s*H t else 0) =
      (Iio (t+1)).indicator (fun s => w s*H t) := by ext s; simp [indicator]
  rw [he,lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
  have hset : Iio (t+1) ∩ Ioi a = Ioo a (t+1) := by ext s; simp only [mem_inter_iff,mem_Iio,mem_Ioi,mem_Ioo]; tauto
  rw [hset,lintegral_mul_const _ hw]

noncomputable def criticalCostKernel (F : ℝ → ℝ≥0∞) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ t : ℝ in Ioi (max 2 (s-1)), ENNReal.ofReal (criticalCoefficient t)*
    (∫⁻ v : ℝ in Ioi (t-1), ENNReal.ofReal (criticalCoefficient v)*F v)

noncomputable def criticalMass (F : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ s : ℝ in Ioi 1, ENNReal.ofReal (criticalWeight s)*F s

lemma measurable_ltail (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    Measurable (fun t : ℝ => ∫⁻ v : ℝ in Ioi (t-1), H v) := by
  have hm : Measurable (fun z : ℝ × ℝ => if z.1-1 < z.2 then H z.2 else 0) :=
    Measurable.ite (measurableSet_lt (measurable_fst.sub_const 1) measurable_snd)
      (hH.comp measurable_snd) measurable_const
  have hm' : Measurable (Function.uncurry (fun t v : ℝ => if t-1 < v then H v else 0)) := hm
  convert hm'.lintegral_prod_right (ν := volume) using 1
  funext t
  exact (lintegral_indicator measurableSet_Ioi H).symm

lemma criticalCostKernel_triangle (F : ℝ → ℝ≥0∞) (s : ℝ) :
    criticalCostKernel F s = ∫⁻ t : ℝ in Ioi 2, if s < t+1 then
      ENNReal.ofReal (criticalCoefficient t)*
        (∫⁻ v : ℝ in Ioi (t-1), ENNReal.ofReal (criticalCoefficient v)*F v) else 0 := by
  classical
  have he : (fun t : ℝ => if s < t+1 then ENNReal.ofReal (criticalCoefficient t)*
        (∫⁻ v : ℝ in Ioi (t-1), ENNReal.ofReal (criticalCoefficient v)*F v) else 0) =
      (Ioi (s-1)).indicator (fun t => ENNReal.ofReal (criticalCoefficient t)*
        (∫⁻ v : ℝ in Ioi (t-1), ENNReal.ofReal (criticalCoefficient v)*F v)) := by
    ext t
    have hh : s < t+1 ↔ s-1 < t := by constructor <;> intro h <;> linarith
    simp only [indicator,mem_Ioi,hh]
  rw [he,lintegral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi (s-1) ∩ Ioi (2 : ℝ) = Ioi (max 2 (s-1)) := by
    ext t
    simp only [mem_inter_iff,mem_Ioi,max_lt_iff]
    tauto
  rw [hset]
  rfl

lemma ltail_triangle (G : ℝ → ℝ≥0∞) (t : ℝ) (ht : 2 ≤ t) :
    (∫⁻ v : ℝ in Ioi (t-1), G v) =
      ∫⁻ v : ℝ in Ioi 1, if t < v+1 then G v else 0 := by
  classical
  have he : (fun v : ℝ => if t < v+1 then G v else 0) =
      (Ioi (t-1)).indicator G := by
    ext v
    have hh : t < v+1 ↔ t-1 < v := by constructor <;> intro h <;> linarith
    simp only [indicator,mem_Ioi,hh]
  rw [he,lintegral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi (t-1) ∩ Ioi (1 : ℝ) = Ioi (t-1) :=
    inter_eq_left.mpr (Ioi_subset_Ioi (by linarith))
  rw [hset]

lemma integrated_ltail (G : ℝ → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ t : ℝ in Ioi 2, ∫⁻ v : ℝ in Ioi (t-1), G v) =
      ∫⁻ v : ℝ in Ioi 1, ENNReal.ofReal (v-1)*G v := by
  have he : (∫⁻ t : ℝ in Ioi 2, ∫⁻ v : ℝ in Ioi (t-1), G v) =
      ∫⁻ t : ℝ in Ioi 2, (1 : ℝ≥0∞)*(∫⁻ v : ℝ in Ioi 1, if t < v+1 then G v else 0) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [one_mul,← ltail_triangle G t (mem_Ioi.mp ht).le]
  rw [he,triangular_lintegral (fun _ => 1) G measurable_const hG 2 1]
  apply lintegral_congr
  intro v
  simp only [lintegral_const,Measure.restrict_apply_univ,one_mul,Real.volume_Ioo]
  congr 2
  ring

/-- The positive weight 1-1/s² is exactly invariant for the critical model.
The identity holds even for infinite mass; no unproved integrability is used. -/
theorem criticalMass_invariant (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    criticalMass (criticalCostKernel F) = criticalMass F := by
  let A : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (criticalCoefficient t)
  let G : ℝ → ℝ≥0∞ := fun t => A t*F t
  have hA : Measurable A := criticalCoefficient_measurable.ennreal_ofReal
  have hG : Measurable G := hA.mul hF
  let H : ℝ → ℝ≥0∞ := fun t => A t*(∫⁻ v : ℝ in Ioi (t-1), G v)
  have hH : Measurable H := hA.mul (measurable_ltail G hG)
  unfold criticalMass
  simp_rw [criticalCostKernel_triangle]
  rw [triangular_lintegral _ _ criticalWeight_measurable.ennreal_ofReal hH 1 2]
  have he : (∫⁻ t : ℝ in Ioi 2, (∫⁻ s : ℝ in Ioo 1 (t+1), ENNReal.ofReal (criticalWeight s))*H t) =
      ∫⁻ t : ℝ in Ioi 2, ∫⁻ v : ℝ in Ioi (t-1), G v := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := by linarith [mem_Ioi.mp ht]
    dsimp only
    rw [criticalWeight_linterval t ht0.le]
    dsimp only [H,A]
    rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity : 0 ≤ t^2/(t+1))]
    have hh : t^2/(t+1)*criticalCoefficient t=1 := by
      unfold criticalCoefficient
      field_simp
    rw [hh,ENNReal.ofReal_one,one_mul]
  change (∫⁻ t : ℝ in Ioi 2, (∫⁻ s : ℝ in Ioo 1 (t+1), ENNReal.ofReal (criticalWeight s))*H t) = _
  rw [he,integrated_ltail G hG]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro v hv
  have hv1 : 1 < v := mem_Ioi.mp hv
  have hv0 : 0 < v := by linarith
  dsimp only [G,A]
  rw [← mul_assoc,← ENNReal.ofReal_mul (by linarith : 0 ≤ v-1)]
  have hh : (v-1)*criticalCoefficient v=criticalWeight v := by
    unfold criticalCoefficient criticalWeight
    field_simp
    ring
  rw [hh]

/-- A finite, nonzero critical mass rules out a pointwise strict contraction. -/
theorem no_finite_mass_critical_contraction (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (hpos : criticalMass F ≠ 0) (hfin : criticalMass F ≠ ⊤)
    (q : ℝ≥0∞) (hq : q < 1) :
    ¬∀ s : ℝ, 1 < s → criticalCostKernel F s ≤ q*F s := by
  intro hbound
  have hh : criticalMass (criticalCostKernel F) ≤ q*criticalMass F := by
    unfold criticalMass
    rw [← lintegral_const_mul _ (criticalWeight_measurable.ennreal_ofReal.mul hF)]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hb := mul_le_mul_left' (hbound s (mem_Ioi.mp hs)) (ENNReal.ofReal (criticalWeight s))
    simpa only [mul_left_comm] using hb
  rw [criticalMass_invariant F hF] at hh
  have hl := ENNReal.mul_lt_mul_right hpos hfin hq
  rw [mul_one,mul_comm (criticalMass F)] at hl
  exact (not_lt_of_ge hh) hl


lemma criticalCostKernel_measurable (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    Measurable (criticalCostKernel F) := by
  let H : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (criticalCoefficient t)*
    (∫⁻ v : ℝ in Ioi (t-1), ENNReal.ofReal (criticalCoefficient v)*F v)
  have hH : Measurable H := criticalCoefficient_measurable.ennreal_ofReal.mul
    (measurable_ltail _ (criticalCoefficient_measurable.ennreal_ofReal.mul hF))
  have hm : Measurable (Function.uncurry (fun s t : ℝ => if s < t+1 then H t else 0)) :=
    Measurable.ite (measurableSet_lt measurable_fst (measurable_snd.add_const 1))
      (hH.comp measurable_snd) measurable_const
  have hh := hm.lintegral_prod_right (ν := volume.restrict (Ioi 2))
  convert hh using 1
  funext s
  exact criticalCostKernel_triangle F s

lemma criticalMass_mono {F G : ℝ → ℝ≥0∞} (h : ∀ s : ℝ, 1 < s → F s ≤ G s) :
    criticalMass F ≤ criticalMass G := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact mul_le_mul_right (h s (mem_Ioi.mp hs)) _

lemma criticalMass_add (F G : ℝ → ℝ≥0∞) (hF : Measurable F) :
    criticalMass (fun s => F s+G s) = criticalMass F+criticalMass G := by
  unfold criticalMass
  simp_rw [mul_add]
  exact lintegral_add_left (criticalWeight_measurable.ennreal_ofReal.mul hF) _

/-- Even a noncontractive supersolution cannot absorb a positive-mass source
while retaining finite critical mass. -/
theorem no_finite_mass_critical_supersolution (S F : ℝ → ℝ≥0∞)
    (hS : Measurable S) (hF : Measurable F)
    (hSpos : criticalMass S ≠ 0) (hFfin : criticalMass F ≠ ⊤) :
    ¬∀ s : ℝ, 1 < s → S s+criticalCostKernel F s ≤ F s := by
  intro hbound
  have hh := criticalMass_mono hbound
  rw [criticalMass_add _ _ hS,criticalMass_invariant F hF] at hh
  have hl := ENNReal.lt_add_right hFfin hSpos
  rw [add_comm] at hl
  exact (not_lt_of_ge hh) hl

noncomputable def criticalCostIteration (S B : ℝ → ℝ≥0∞) : ℕ → ℝ → ℝ≥0∞
  | 0 => B
  | n+1 => fun s => max (criticalCostIteration S B n s)
      (S s+criticalCostKernel (criticalCostIteration S B n) s)

lemma criticalCostIteration_measurable (S B : ℝ → ℝ≥0∞)
    (hS : Measurable S) (hB : Measurable B) (n : ℕ) :
    Measurable (criticalCostIteration S B n) := by
  induction n with
  | zero => exact hB
  | succ n ih => exact ih.max (hS.add (criticalCostKernel_measurable _ ih))

/-- The complete positive model recurrence, including its outer maximum,
accumulates at least one source mass at every depth. -/
theorem criticalCostIteration_mass_growth (S B : ℝ → ℝ≥0∞)
    (hS : Measurable S) (hB : Measurable B) (n : ℕ) :
    (n : ℝ≥0∞)*criticalMass S+criticalMass B ≤
      criticalMass (criticalCostIteration S B n) := by
  induction n with
  | zero => simp [criticalCostIteration]
  | succ n ih =>
    have hm := criticalMass_mono (F := fun s => S s+criticalCostKernel (criticalCostIteration S B n) s)
      (G := criticalCostIteration S B (n+1)) (fun s _ => le_max_right _ _)
    rw [criticalMass_add _ _ hS,criticalMass_invariant _
      (criticalCostIteration_measurable S B hS hB n)] at hm
    have hh := (add_le_add (le_refl (criticalMass S)) ih).trans hm
    convert hh using 1
    simp only [Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    simp only [add_assoc,add_comm,add_left_comm]

#print axioms no_finite_mass_critical_supersolution
#print axioms criticalCostIteration_mass_growth

#print axioms criticalMass_invariant
#print axioms no_finite_mass_critical_contraction
end Erdos970.ContinuousBuchstab
