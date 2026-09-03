import Submission.ContinuousCriticalTightness

/-! Linear pointwise growth for a compact positive source in the critical
continuous cost operator. Infinite total mass cannot supply a finite-valued
supersolution for this source. This is not a Jacobsthal disproof. -/
namespace Erdos970.ContinuousBuchstab
open Real Set Filter MeasureTheory
open scoped Topology ENNReal
set_option maxHeartbeats 1800000

noncomputable def criticalCompactSource : ℝ → ℝ≥0∞ := (Ioo 1 2).indicator (fun _ => 1)

lemma criticalCompactSource_measurable : Measurable criticalCompactSource :=
  measurable_const.indicator measurableSet_Ioo

lemma criticalCompactSource_mass : criticalMass criticalCompactSource = 1/2 := by
  classical
  unfold criticalMass criticalCompactSource
  have he : (fun s : ℝ => ENNReal.ofReal (criticalWeight s) * (Ioo 1 2).indicator (fun _ => 1) s) =
      (Ioo 1 2).indicator (fun s => ENNReal.ofReal (criticalWeight s)) := by
    funext s
    by_cases hs : s ∈ Ioo (1 : ℝ) 2 <;> simp [hs]
  rw [he, lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.mpr (show Ioo (1 : ℝ) 2 ⊆ Ioi 1 from fun _ h => h.1)]
  have hh := criticalWeight_linterval 1 (by norm_num)
  norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  simpa using hh

lemma criticalCompactSource_first_le_one : criticalFirstMass criticalCompactSource ≤ 1 := by
  classical
  have hh : criticalFirstMass criticalCompactSource ≤ (2 : ℝ≥0∞)*criticalMass criticalCompactSource := by
    unfold criticalFirstMass criticalMass
    rw [← lintegral_const_mul _ (criticalWeight_measurable.ennreal_ofReal.mul criticalCompactSource_measurable)]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    by_cases hs2 : s ∈ Ioo (1 : ℝ) 2
    · have h : ENNReal.ofReal s ≤ (2 : ℝ≥0∞) := by
        simpa using ENNReal.ofReal_le_ofReal hs2.2.le
      simpa only [mul_assoc] using mul_le_mul_left h
        (ENNReal.ofReal (criticalWeight s) * criticalCompactSource s)
    · simp [criticalCompactSource, hs2]
  rw [criticalCompactSource_mass] at hh
  norm_num only [one_div] at hh
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)] at hh
  exact hh

lemma criticalFirstMass_add (F G : ℝ → ℝ≥0∞) (hF : Measurable F) :
    criticalFirstMass (fun s => F s + G s) = criticalFirstMass F + criticalFirstMass G := by
  unfold criticalFirstMass
  simp_rw [mul_add]
  exact lintegral_add_left ((measurable_id.ennreal_ofReal.mul criticalWeight_measurable.ennreal_ofReal).mul hF) _

lemma criticalCostKernel_mono {F G : ℝ → ℝ≥0∞}
    (h : ∀ s : ℝ, 1 < s → F s ≤ G s) (s : ℝ) :
    criticalCostKernel F s ≤ criticalCostKernel G s := by
  unfold criticalCostKernel
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  apply mul_le_mul_right
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  apply mul_le_mul_right
  apply h
  have ht2 : (2 : ℝ) < t := (le_max_left _ _).trans_lt (mem_Ioi.mp ht)
  linarith [mem_Ioi.mp hv]

noncomputable def criticalCompactPotential : ℕ → ℝ → ℝ≥0∞
  | 0 => fun _ => 0
  | n+1 => fun s => criticalCompactSource s + criticalCostKernel (criticalCompactPotential n) s

lemma criticalCompactPotential_measurable (n : ℕ) : Measurable (criticalCompactPotential n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact criticalCompactSource_measurable.add (criticalCostKernel_measurable _ ih)

lemma criticalCompactPotential_mass (n : ℕ) : criticalMass (criticalCompactPotential n) = (n : ℝ≥0∞)/2 := by
  induction n with
  | zero => simp [criticalCompactPotential, criticalMass]
  | succ n ih =>
    change criticalMass (fun s => criticalCompactSource s + criticalCostKernel (criticalCompactPotential n) s) = _
    rw [criticalMass_add _ _ criticalCompactSource_measurable, criticalCompactSource_mass,
      criticalMass_invariant _ (criticalCompactPotential_measurable n), ih,
      ENNReal.div_add_div_same]
    simp only [Nat.cast_add, Nat.cast_one, add_comm]

lemma criticalCompactPotential_first_le (n : ℕ) :
    criticalFirstMass (criticalCompactPotential n) ≤ (5/2 : ℝ≥0∞)*n := by
  induction n with
  | zero => simp [criticalCompactPotential, criticalFirstMass]
  | succ n ih =>
    change criticalFirstMass (fun s => criticalCompactSource s + criticalCostKernel (criticalCompactPotential n) s) ≤ _
    rw [criticalFirstMass_add _ _ criticalCompactSource_measurable]
    have hh := criticalFirstMass_kernel_le _ (criticalCompactPotential_measurable n)
    rw [criticalCompactPotential_mass] at hh
    have hi := (mul_le_mul_right ih (1/2 : ℝ≥0∞))
    have hb := hh.trans (add_le_add_left hi _)
    apply (add_le_add criticalCompactSource_first_le_one hb).trans
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
      ENNReal.toReal_one, ENNReal.toReal_ofNat]
    push_cast
    linarith


lemma criticalCompactPotential_cut_lower (n : ℕ) :
    (n : ℝ≥0∞)/4 ≤ criticalCutMass (criticalCompactPotential n) 10 := by
  have hh := criticalMass_le_cut_add_first _ (criticalCompactPotential_measurable n) 10 (by norm_num)
  rw [criticalCompactPotential_mass] at hh
  have hc := mul_le_mul_right (criticalCompactPotential_first_le n) (ENNReal.ofReal (1/(10 : ℝ)))
  have ha : ENNReal.ofReal (1/(10 : ℝ)) * ((5/2 : ℝ≥0∞)*n) = (n : ℝ≥0∞)/4 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1/10),
      ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
    ring
  rw [ha] at hc
  have hb := hh.trans (add_le_add_right hc _)
  apply ENNReal.le_of_add_le_add_right (a := (n : ℝ≥0∞)/4) (by finiteness)
  have he : (n : ℝ≥0∞)/4+n/4=n/2 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
    ring
  rwa [he]

/-- The compact-source potential grows at least linearly at level two,
not merely after integration over all levels. -/
theorem criticalCompactPotential_two_growth (n : ℕ) :
    (n : ℝ≥0∞)/44 ≤ criticalCompactPotential (n+1) 2 := by
  have hh := (mul_le_mul_right (criticalCompactPotential_cut_lower n)
    (ENNReal.ofReal (1/(10+1 : ℝ)))).trans
    (criticalCostKernel_two_ge_cut _ (criticalCompactPotential_measurable n) 10 (by norm_num))
  have he : ENNReal.ofReal (1/(10+1 : ℝ))*((n : ℝ≥0∞)/4) = (n : ℝ≥0∞)/44 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1/(10+1))]
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_ofNat]
    ring
  rw [he] at hh
  exact hh.trans (le_add_left le_rfl)

lemma criticalCompactPotential_le_supersolution (F : ℝ → ℝ≥0∞)
    (hF : ∀ s : ℝ, 1 < s → criticalCompactSource s + criticalCostKernel F s ≤ F s)
    (n : ℕ) : ∀ s : ℝ, 1 < s → criticalCompactPotential n s ≤ F s := by
  induction n with
  | zero => intro s hs; exact zero_le _
  | succ n ih =>
    intro s hs
    exact (add_le_add_right (criticalCostKernel_mono ih s) _).trans (hF s hs)

/-- No integrability or finite-total-mass assumption is made on the proposed
supersolution. A nonnegative source on (1,2) forces an infinite value at 2. -/
theorem criticalCompactSource_supersolution_two_top (F : ℝ → ℝ≥0∞)
    (hF : ∀ s : ℝ, 1 < s → criticalCompactSource s + criticalCostKernel F s ≤ F s) :
    F 2 = ⊤ := by
  have hh : ∀ n : ℕ, (n : ℝ≥0∞)/44 ≤ F 2 := fun n =>
    (criticalCompactPotential_two_growth n).trans
      (criticalCompactPotential_le_supersolution F hF (n+1) 2 (by norm_num))
  have hi : (⨆ n : ℕ, (n : ℝ≥0∞)/44) ≤ F 2 := iSup_le hh
  rw [← ENNReal.iSup_div, ENNReal.iSup_natCast] at hi
  norm_num [ENNReal.top_div] at hi
  exact hi

theorem no_finite_criticalCompactSource_supersolution (F : ℝ → ℝ≥0∞) (hfin : F 2 ≠ ⊤) :
    ¬∀ s : ℝ, 1 < s → criticalCompactSource s + criticalCostKernel F s ≤ F s := by
  exact fun h => hfin (criticalCompactSource_supersolution_two_top F h)

#print axioms criticalCompactPotential_two_growth
#print axioms no_finite_criticalCompactSource_supersolution
end Erdos970.ContinuousBuchstab
