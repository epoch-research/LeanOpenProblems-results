import FormalConjecturesUtil

/-! Moving archimedean phases can be asymptotically invariant under every fixed
positive multiplier, uniformly in their argument, while their adjacent imaginary
correlation on a dyadic interval stays positive. This is an obstruction to a
proposed general dilation argument, NOT a counterexample to Erdős 371. -/

namespace Erdos371RecurringlyStableMovingPhase

open Filter Finset
open scoped Topology

noncomputable def phase (t n : ℕ) : Circle := Circle.exp ((t : ℝ)*Real.log n)

lemma phase_eq_pow (t n : ℕ) : phase t n = (Circle.exp (Real.log n))^t := by
  induction t with
  | zero => simp [phase]
  | succ t ih =>
    simp only [phase, Nat.cast_add, Nat.cast_one, add_mul, one_mul, Circle.exp_add,
      pow_succ]
    rw [show Circle.exp ((t : ℝ)*Real.log n) = (Circle.exp (Real.log n))^t from ih]

lemma phase_mul (t : ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    phase t (a*b) = phase t a * phase t b := by
  simp only [phase, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr ha)
    (Nat.cast_ne_zero.mpr hb), mul_add, Circle.exp_add]

lemma multiplier_error (t : ℕ) {a n : ℕ} (ha : a ≠ 0) (hn : n ≠ 0) :
    ‖(phase t (a*n) : ℂ) - phase t n‖ = ‖(phase t a : ℂ)-1‖ := by
  rw [phase_mul t ha hn, Circle.coe_mul]
  have he : (phase t a : ℂ)*(phase t n : ℂ)-(phase t n : ℂ) =
      ((phase t a : ℂ)-1)*(phase t n : ℂ) := by ring
  rw [he, norm_mul, Circle.norm_coe, mul_one]

/-- Compact-group recurrence chooses one unbounded sequence of integer
frequencies returning to one at ALL fixed positive integers simultaneously. -/
theorem exists_recurrent_frequencies :
    ∃ t : ℕ → ℕ, StrictMono t ∧ (∀ j, 0 < t j) ∧
      ∀ a : ℕ, Tendsto (fun j => phase (t j) a) atTop (𝓝 1) := by
  let z : ℕ → Circle := fun a => Circle.exp (Real.log a)
  obtain ⟨u, hu, hlim⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq
    (mapClusterPt_one_atTop_pow z)
  refine ⟨fun j => u (j+1), hu.comp (strictMono_nat_of_lt_succ (by omega)), ?_, ?_⟩
  · intro j
    have hh := hu.id_le (j+1)
    exact lt_of_lt_of_le (Nat.succ_pos j) hh
  · intro a
    have hh := (hlim.apply_nhds a).comp (tendsto_add_atTop_nat 1)
    simpa [phase_eq_pow, z, Function.comp_def] using hh

lemma log_increment_bounds {n : ℕ} (hn : 0 < n) :
    1 / ((n : ℝ)+1) ≤ Real.log ((n : ℝ)+1)-Real.log n ∧
      Real.log ((n : ℝ)+1)-Real.log n ≤ 1/(n : ℝ) := by
  have hnr : (0 : ℝ)<n := Nat.cast_pos.mpr hn
  have hns : (0 : ℝ)<(n : ℝ)+1 := by positivity
  constructor
  · have hh := Real.log_le_sub_one_of_pos (div_pos hnr hns)
    rw [Real.log_div hnr.ne' hns.ne'] at hh
    have he : (n : ℝ)/((n : ℝ)+1)-1 = -(1/((n : ℝ)+1)) := by field_simp; ring
    rw [he] at hh
    linarith
  · have hh := Real.log_le_sub_one_of_pos (div_pos hns hnr)
    rw [Real.log_div hns.ne' hnr.ne'] at hh
    have he : ((n : ℝ)+1)/(n : ℝ)-1 = 1/(n : ℝ) := by field_simp; ring
    rwa [he] at hh

lemma angle_bounds {t n : ℕ} (ht : 0<t) (htn : t ≤ n) (hnt : n ≤ 2*t) :
    1/3 ≤ (t : ℝ)*(Real.log ((n : ℝ)+1)-Real.log n) ∧
      (t : ℝ)*(Real.log ((n : ℝ)+1)-Real.log n) ≤ 1 := by
  have hn : 0<n := ht.trans_le htn
  obtain ⟨hl, hu⟩ := log_increment_bounds hn
  have htr : (0 : ℝ)<t := Nat.cast_pos.mpr ht
  have hnr : (0 : ℝ)<n := Nat.cast_pos.mpr hn
  have htnr : (t : ℝ) ≤ n := Nat.cast_le.mpr htn
  have hntr : (n : ℝ) ≤ 2*t := by exact_mod_cast hnt
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  constructor
  · have hh : (1/3 : ℝ) ≤ (t : ℝ)/((n : ℝ)+1) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ)<(n : ℝ)+1)).mpr
      linarith
    exact hh.trans (by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hl htr.le)
  · have hh : (t : ℝ)/(n : ℝ) ≤ 1 := (div_le_one hnr).mpr htnr
    exact (show (t : ℝ)*(Real.log ((n : ℝ)+1)-Real.log n) ≤ (t : ℝ)/(n : ℝ)
      from by simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hu htr.le).trans hh

noncomputable def adjacentIm (t n : ℕ) : ℝ :=
  (((phase t (n+1) / phase t n : Circle) : ℂ)).im

lemma adjacentIm_eq (t n : ℕ) : adjacentIm t n =
    Real.sin ((t : ℝ)*(Real.log ((n : ℝ)+1)-Real.log n)) := by
  unfold adjacentIm phase
  rw [← Circle.exp_sub]
  have he : (t : ℝ)*Real.log (n+1 : ℕ) - (t : ℝ)*Real.log n =
      (t : ℝ)*(Real.log ((n : ℝ)+1)-Real.log n) := by push_cast; ring
  rw [he, Circle.coe_exp, Complex.exp_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, Real.exp_zero,
    one_mul, mul_one, add_zero]

lemma adjacentIm_lower {t n : ℕ} (ht : 0<t) (htn : t ≤ n) (hnt : n ≤ 2*t) :
    Real.sin (1/3) ≤ adjacentIm t n := by
  rw [adjacentIm_eq]
  obtain ⟨hl, hu⟩ := angle_bounds ht htn hnt
  apply Real.sin_le_sin_of_le_of_le_pi_div_two _ _ hl
  · linarith [Real.pi_pos]
  · linarith [Real.pi_gt_three]

lemma positive_constant : 0 < Real.sin (1/3 : ℝ) :=
  Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.pi_gt_three])

noncomputable def blockMean (t : ℕ) : ℝ :=
  (∑ n ∈ Ico t (2*t), adjacentIm t n) / t

lemma blockMean_lower {t : ℕ} (ht : 0<t) : Real.sin (1/3) ≤ blockMean t := by
  have hh : ∑ n ∈ Ico t (2*t), Real.sin (1/3) ≤
      ∑ n ∈ Ico t (2*t), adjacentIm t n := by
    apply sum_le_sum
    intro n hn
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hn
    exact adjacentIm_lower ht hlo hhi.le
  have hc : (Ico t (2*t)).card = t := by simp; omega
  simp only [sum_const, hc, nsmul_eq_mul] at hh
  unfold blockMean
  apply (le_div_iff₀ (Nat.cast_pos.mpr ht)).mpr
  simpa only [mul_comm] using hh

/-- All fixed-multiplier errors can vanish uniformly in the input while the
imaginary adjacent correlation has a strictly positive lower bound. The
frequency changes with the counting range; this is not a theorem about P. -/
theorem stable_moving_phase_obstruction :
    ∃ t : ℕ → ℕ, StrictMono t ∧ (∀ j, 0<t j) ∧
      (∀ a : ℕ, a ≠ 0 →
        Tendsto (fun j => ‖(phase (t j) a : ℂ)-1‖) atTop (𝓝 0)) ∧
      (∀ j, Real.sin (1/3) ≤ blockMean (t j)) ∧
      ¬ Tendsto (fun j => blockMean (t j)) atTop (𝓝 0) := by
  obtain ⟨t, ht, htpos, hlim⟩ := exists_recurrent_frequencies
  refine ⟨t, ht, htpos, ?_, fun j => blockMean_lower (htpos j), ?_⟩
  · intro a ha
    have hh : Tendsto (fun j => (phase (t j) a : ℂ)) atTop (𝓝 (1 : ℂ)) :=
      continuous_subtype_val.continuousAt.tendsto.comp (hlim a)
    simpa using (hh.sub_const 1).norm
  · intro hzero
    have hh := ge_of_tendsto hzero (Eventually.of_forall fun j => blockMean_lower (htpos j))
    exact (not_le_of_gt positive_constant) hh

end Erdos371RecurringlyStableMovingPhase

#print axioms Erdos371RecurringlyStableMovingPhase.stable_moving_phase_obstruction
