import Submission.NonBetweenHarmonicVariation

/-!
Relative harmonic balance on the non-between subevent. The denominator is
its own divergent harmonic mass, not the number of integers and not the
harmonic mass of the whole interval. The fixed-dyadic-window mass is bounded,
so this does not supply the unnormalized dyadic cancellation needed in Spec.
-/

namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

noncomputable def nonBetweenHarmonicMass (N : ℕ) : ℝ :=
  ∑ n ∈ range N, |nonBetweenHarmonicTerm n|

noncomputable def nonBetweenRiseHarmonicMass (N : ℕ) : ℝ :=
  ∑ n ∈ range N, if ¬ factorBetween (n+1) ∧
    Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac (n+2) then 1/(n+1 : ℝ) else 0

noncomputable def nonBetweenFallHarmonicMass (N : ℕ) : ℝ :=
  ∑ n ∈ range N, if ¬ factorBetween (n+1) ∧
    Nat.maxPrimeFac (n+2) < Nat.maxPrimeFac (n+1) then 1/(n+1 : ℝ) else 0


lemma nonBetweenHarmonicMass_eq_event (N : ℕ) :
    nonBetweenHarmonicMass N =
      ∑ n ∈ range N, if ¬ factorBetween (n+1) then 1/(n+1 : ℝ) else 0 := by
  apply sum_congr rfl
  intro n _
  have hf : |factorSign (n+1)| = 1 := by
    unfold factorSign predicateSign
    split_ifs <;> norm_num
  by_cases hb : factorBetween (n+1)
  · simp [nonBetweenHarmonicTerm, hb]
  · simp only [nonBetweenHarmonicTerm, hb, if_false, not_false_eq_true, if_true,
      abs_div, hf, abs_of_pos (show (0 : ℝ)<n+1 by positivity)]

lemma nonBetween_positive_term (n : ℕ) :
    max (nonBetweenHarmonicTerm n) 0 =
      if ¬ factorBetween (n+1) ∧ Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac (n+2)
        then 1/(n+1 : ℝ) else 0 := by
  have hn : (-1 : ℝ)/(n+1 : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  by_cases hb : factorBetween (n+1)
  · simp [nonBetweenHarmonicTerm, hb]
  · by_cases hr : Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac (n+2)
    · simp [nonBetweenHarmonicTerm, factorSign, predicateSign, hb, hr,
        Nat.add_assoc]
      positivity
    · simp [nonBetweenHarmonicTerm, factorSign, predicateSign, hb, hr,
        Nat.add_assoc, max_eq_right hn]

lemma nonBetween_negative_term (n : ℕ) :
    max (-nonBetweenHarmonicTerm n) 0 =
      if ¬ factorBetween (n+1) ∧ Nat.maxPrimeFac (n+2) < Nat.maxPrimeFac (n+1)
        then 1/(n+1 : ℝ) else 0 := by
  have hne : Nat.maxPrimeFac (n+2) ≠ Nat.maxPrimeFac (n+1) :=
    consecutive_maxPrimeFac_ne (n+1)
  by_cases hb : factorBetween (n+1)
  · simp [nonBetweenHarmonicTerm, hb]
  · by_cases hr : Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac (n+2)
    · have hf : ¬ Nat.maxPrimeFac (n+2) < Nat.maxPrimeFac (n+1) := by omega
      simp [nonBetweenHarmonicTerm, factorSign, predicateSign, hb, hr, hf,
        Nat.add_assoc]
      positivity
    · have hf : Nat.maxPrimeFac (n+2) < Nat.maxPrimeFac (n+1) := by omega
      simp [nonBetweenHarmonicTerm, factorSign, predicateSign, hb, hr, hf,
        Nat.add_assoc, neg_div]
      positivity

lemma nonBetweenRiseHarmonicMass_eq_positive (N : ℕ) :
    nonBetweenRiseHarmonicMass N = ∑ n ∈ range N, max (nonBetweenHarmonicTerm n) 0 := by
  simp_rw [nonBetween_positive_term]
  rfl

lemma nonBetweenFallHarmonicMass_eq_negative (N : ℕ) :
    nonBetweenFallHarmonicMass N = ∑ n ∈ range N, max (-nonBetweenHarmonicTerm n) 0 := by
  simp_rw [nonBetween_negative_term]
  rfl

lemma nonBetween_mass_twice_rise (N : ℕ) :
    nonBetweenHarmonicMass N = 2*nonBetweenRiseHarmonicMass N-nonBetweenHarmonicSum N := by
  rw [nonBetweenRiseHarmonicMass_eq_positive]
  exact nonBetween_abs_sum_eq_positive N

lemma nonBetween_mass_twice_fall (N : ℕ) :
    nonBetweenHarmonicMass N = 2*nonBetweenFallHarmonicMass N+nonBetweenHarmonicSum N := by
  rw [nonBetweenFallHarmonicMass_eq_negative]
  exact nonBetween_abs_sum_eq_negative N

lemma nonBetweenHarmonicMass_nonneg (N : ℕ) : 0 ≤ nonBetweenHarmonicMass N :=
  sum_nonneg fun _ _ => abs_nonneg _

lemma nonBetweenHarmonicMass_mono : Monotone nonBetweenHarmonicMass := by
  intro A B hAB
  exact sum_le_sum_of_subset_of_nonneg (range_mono hAB) (fun _ _ _ => abs_nonneg _)

theorem nonBetweenHarmonicMass_tendsto_atTop : Tendsto nonBetweenHarmonicMass atTop atTop :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun _ => abs_nonneg _)).mp
    not_summable_abs_nonBetweenHarmonicTerm

/-- The finite error is divided by the mass of this subevent, not by N. -/
lemma nonBetween_rise_fraction_error (N : ℕ) (hN : 0 < nonBetweenHarmonicMass N) :
    |nonBetweenRiseHarmonicMass N/nonBetweenHarmonicMass N-1/2| ≤
      3/(2*nonBetweenHarmonicMass N) := by
  have he : nonBetweenRiseHarmonicMass N/nonBetweenHarmonicMass N-1/2 =
      nonBetweenHarmonicSum N/(2*nonBetweenHarmonicMass N) := by
    have hm := nonBetween_mass_twice_rise N
    field_simp
    linarith
  rw [he, abs_div, abs_of_pos (mul_pos (by norm_num) hN)]
  exact div_le_div_of_nonneg_right (nonBetweenHarmonicSum_bound N) (by positivity)

lemma nonBetween_fall_fraction_error (N : ℕ) (hN : 0 < nonBetweenHarmonicMass N) :
    |nonBetweenFallHarmonicMass N/nonBetweenHarmonicMass N-1/2| ≤
      3/(2*nonBetweenHarmonicMass N) := by
  have he : nonBetweenFallHarmonicMass N/nonBetweenHarmonicMass N-1/2 =
      -nonBetweenHarmonicSum N/(2*nonBetweenHarmonicMass N) := by
    have hm := nonBetween_mass_twice_fall N
    field_simp
    linarith
  rw [he, abs_div, abs_neg, abs_of_pos (mul_pos (by norm_num) hN)]
  exact div_le_div_of_nonneg_right (nonBetweenHarmonicSum_bound N) (by positivity)

/-- Half of the non-between event's harmonic mass comes from rises. This is
NOT the natural density one-half statement of Erdős 371. -/
theorem nonBetween_relative_harmonic_rises_half :
    Tendsto (fun N => nonBetweenRiseHarmonicMass N/nonBetweenHarmonicMass N)
      atTop (𝓝 (1/2)) := by
  have ht : Tendsto (fun N => (3 : ℝ)/(2*nonBetweenHarmonicMass N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (nonBetweenHarmonicMass_tendsto_atTop.const_mul_atTop
      (by norm_num : (0 : ℝ)<2))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [nonBetweenHarmonicMass_tendsto_atTop.eventually_gt_atTop 0,
    ht.eventually_lt_const hε] with N hN htN
  rw [Real.dist_eq]
  exact (nonBetween_rise_fraction_error N hN).trans_lt htN

theorem nonBetween_relative_harmonic_falls_half :
    Tendsto (fun N => nonBetweenFallHarmonicMass N/nonBetweenHarmonicMass N)
      atTop (𝓝 (1/2)) := by
  have ht : Tendsto (fun N => (3 : ℝ)/(2*nonBetweenHarmonicMass N)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (nonBetweenHarmonicMass_tendsto_atTop.const_mul_atTop
      (by norm_num : (0 : ℝ)<2))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [nonBetweenHarmonicMass_tendsto_atTop.eventually_gt_atTop 0,
    ht.eventually_lt_const hε] with N hN htN
  rw [Real.dist_eq]
  exact (nonBetween_fall_fraction_error N hN).trans_lt htN

lemma nonBetween_rise_window_fraction_error (A B : ℕ)
    (hM : 0 < nonBetweenHarmonicMass B-nonBetweenHarmonicMass A) :
    |(nonBetweenRiseHarmonicMass B-nonBetweenRiseHarmonicMass A)/
        (nonBetweenHarmonicMass B-nonBetweenHarmonicMass A)-1/2| ≤
      3/(nonBetweenHarmonicMass B-nonBetweenHarmonicMass A) := by
  have he : (nonBetweenRiseHarmonicMass B-nonBetweenRiseHarmonicMass A)/
        (nonBetweenHarmonicMass B-nonBetweenHarmonicMass A)-1/2 =
      (nonBetweenHarmonicSum B-nonBetweenHarmonicSum A)/
        (2*(nonBetweenHarmonicMass B-nonBetweenHarmonicMass A)) := by
    have hA := nonBetween_mass_twice_rise A
    have hB := nonBetween_mass_twice_rise B
    field_simp
    nlinarith
  have hb : |nonBetweenHarmonicSum B-nonBetweenHarmonicSum A| ≤ 6 :=
    (abs_sub _ _).trans (by linarith [nonBetweenHarmonicSum_bound A,
      nonBetweenHarmonicSum_bound B])
  rw [he, abs_div, abs_of_pos (mul_pos (by norm_num) hM)]
  have h := div_le_div_of_nonneg_right hb
    (show 0 ≤ 2*(nonBetweenHarmonicMass B-nonBetweenHarmonicMass A) by positivity)
  exact h.trans_eq (by field_simp; ring)

/-- Uniform relative balance in any windows whose intrinsic non-between
harmonic mass diverges. No short-window assertion is hidden in this premise. -/
theorem nonBetween_relative_window_rises_half (A B : ℕ → ℕ)
    (hM : Tendsto (fun j => nonBetweenHarmonicMass (B j)-nonBetweenHarmonicMass (A j))
      atTop atTop) :
    Tendsto (fun j => (nonBetweenRiseHarmonicMass (B j)-nonBetweenRiseHarmonicMass (A j))/
      (nonBetweenHarmonicMass (B j)-nonBetweenHarmonicMass (A j))) atTop (𝓝 (1/2)) := by
  have ht : Tendsto (fun j => (3 : ℝ)/
      (nonBetweenHarmonicMass (B j)-nonBetweenHarmonicMass (A j))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hM
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hM.eventually_gt_atTop 0, ht.eventually_lt_const hε] with j hj htj
  rw [Real.dist_eq]
  exact (nonBetween_rise_window_fraction_error (A j) (B j) hj).trans_lt htj

lemma abs_nonBetweenHarmonicTerm_le (n : ℕ) :
    |nonBetweenHarmonicTerm n| ≤ 1/(n+1 : ℝ) := by
  have hf : |factorSign (n+1)| = 1 := by
    unfold factorSign predicateSign
    split_ifs <;> norm_num
  unfold nonBetweenHarmonicTerm
  split_ifs
  · simp only [abs_zero]
    positivity
  · rw [abs_div, hf, abs_of_pos (show (0 : ℝ)<n+1 by positivity)]

/-- In particular, fixed dyadic windows cannot meet the preceding growing-
mass hypothesis. Their intrinsic mass is bounded by one. -/
theorem nonBetween_dyadic_window_mass_le_one (N : ℕ) :
    nonBetweenHarmonicMass (2*N)-nonBetweenHarmonicMass N ≤ 1 := by
  by_cases hN : N=0
  · subst N
    simp
  have hNr : (0 : ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have he : nonBetweenHarmonicMass (2*N)-nonBetweenHarmonicMass N =
      ∑ n ∈ range N, |nonBetweenHarmonicTerm (N+n)| := by
    unfold nonBetweenHarmonicMass
    rw [show 2*N=N+N by omega, sum_range_add]
    ring
  rw [he]
  calc
    _ ≤ ∑ _ ∈ range N, (1 : ℝ)/N := by
      apply sum_le_sum
      intro n _
      apply (abs_nonBetweenHarmonicTerm_le (N+n)).trans
      apply one_div_le_one_div_of_le hNr
      push_cast
      linarith [show (0 : ℝ)≤n by positivity]
    _ = 1 := by simp [hNr.ne']


/-- No choice of growing or sparse endpoints changes this obstruction to
applying the relative-window theorem to fixed dyadic windows. -/
lemma nonBetween_dyadic_mass_not_tendsto_atTop (N : ℕ → ℕ) :
    ¬ Tendsto (fun j => nonBetweenHarmonicMass (2*N j)-nonBetweenHarmonicMass (N j))
      atTop atTop := by
  intro h
  obtain ⟨j,hj⟩ := (h.eventually_gt_atTop (1 : ℝ)).exists
  exact hj.not_ge (nonBetween_dyadic_window_mass_le_one (N j))

#print axioms nonBetween_relative_harmonic_rises_half
#print axioms nonBetween_relative_harmonic_falls_half
#print axioms nonBetween_relative_window_rises_half
#print axioms nonBetween_dyadic_window_mass_le_one

end Erdos371
