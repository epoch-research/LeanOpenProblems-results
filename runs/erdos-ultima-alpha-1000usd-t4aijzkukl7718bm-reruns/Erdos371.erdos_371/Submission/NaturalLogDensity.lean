import FormalConjecturesUtil

/-! A proof that natural density implies logarithmic density, without using
`Set.HasDensity.hasLogDensity`, which is a `proof_wanted` declaration in the
imported utilities. This file does not prove a density for prime-factor ascents. -/

namespace Erdos371NaturalLogDensity

open Finset Filter Asymptotics
open scoped Topology

lemma log_nat_atTop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma harmonic_atTop : Tendsto (fun n : ℕ => (harmonic n : ℝ)) atTop atTop := by
  simpa using Real.tendsto_harmonic_sub_log.add_atTop log_nat_atTop

lemma harmonic_log_ratio :
    Tendsto (fun n : ℕ => (harmonic n : ℝ) / Real.log n) atTop (𝓝 1) := by
  have h := (Real.tendsto_harmonic_sub_log.div_atTop log_nat_atTop).add_const 1
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [log_nat_atTop.eventually_ne_atTop 0] with n hn
  field_simp
  ring

lemma harmonic_real_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ k ∈ range N, ((k : ℝ) + 1)⁻¹ := by
  simp [harmonic]

noncomputable def tailWeight (N : ℕ) : ℝ :=
  ∑ k ∈ range N, ((k : ℝ) + 2)⁻¹

lemma tailWeight_eq (N : ℕ) : tailWeight N = (harmonic (N+1) : ℝ) - 1 := by
  rw [harmonic_real_sum, sum_range_succ']
  simp [tailWeight, Nat.cast_add, Nat.cast_one, add_assoc, show (1 : ℝ)+1=2 by norm_num]

lemma tailWeight_atTop : Tendsto tailWeight atTop atTop := by
  have h := (harmonic_atTop.comp (tendsto_add_atTop_nat 1)).atTop_add
    (tendsto_const_nhds (x := (-1 : ℝ)))
  simpa only [Function.comp_def, ← tailWeight_eq, ← sub_eq_add_neg] using h

lemma tailWeight_log_ratio :
    Tendsto (fun N : ℕ => tailWeight N / Real.log N) atTop (𝓝 1) := by
  have hi : Tendsto (fun N : ℕ => ((N : ℝ)+1)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add
      (tendsto_const_nhds (x := (1 : ℝ))))
  have h := (harmonic_log_ratio.add (hi.div_atTop log_nat_atTop)).sub
    ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop log_nat_atTop)
  simpa [tailWeight_eq, harmonic_succ, add_div, sub_div] using h

/-- A convenient finite summation-by-parts identity. -/
lemma reciprocal_sum_by_parts (f : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ range N, f k / ((k : ℝ)+1) =
      (∑ k ∈ range N, f k) / ((N : ℝ)+1) +
      ∑ k ∈ range N, ((∑ j ∈ range (k+1), f j) / ((k : ℝ)+1)) /
        ((k : ℝ)+2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, sum_range_succ, ih]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [sum_range_succ]
    have h1 : (N : ℝ)+1 ≠ 0 := by positivity
    have h2 : (N : ℝ)+1+1 ≠ 0 := by positivity
    have h3 : (N : ℝ)+2 ≠ 0 := by positivity
    field_simp
    ring

/-- Cesàro convergence to zero implies convergence of the logarithmic means. -/
theorem logarithmic_mean_zero_of_cesaro_zero (f : ℕ → ℝ)
    (h : Tendsto (fun N : ℕ => (∑ k ∈ range N, f k) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ k ∈ range N, f k / ((k : ℝ)+1)) /
      Real.log N) atTop (𝓝 0) := by
  have hb : Tendsto (fun N : ℕ => (∑ k ∈ range N, f k) / ((N : ℝ)+1))
      atTop (𝓝 0) := by
    have hh := h.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
    simp only [zero_mul] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have hu : Tendsto (fun k : ℕ => (∑ j ∈ range (k+1), f j) / ((k : ℝ)+1))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h.comp (tendsto_add_atTop_nat 1)
  have ho : (fun k : ℕ => ((∑ j ∈ range (k+1), f j) / ((k : ℝ)+1)) /
      ((k : ℝ)+2)) =o[atTop] (fun k : ℕ => ((k : ℝ)+2)⁻¹) := by
    simpa only [one_mul, div_eq_mul_inv] using
      ((isLittleO_one_iff ℝ).mpr hu).mul_isBigO
        (isBigO_refl (fun k : ℕ => ((k : ℝ)+2)⁻¹) atTop)
  have hs := (ho.sum_range (by intro k; positivity) tailWeight_atTop).tendsto_div_nhds_zero
  have hw : Tendsto (fun N : ℕ =>
      (∑ k ∈ range N, ((∑ j ∈ range (k+1), f j) / ((k : ℝ)+1)) /
        ((k : ℝ)+2)) / Real.log N) atTop (𝓝 0) := by
    have hh := hs.mul tailWeight_log_ratio
    simp only [zero_mul] at hh
    apply hh.congr'
    filter_upwards [tailWeight_atTop.eventually_ne_atTop 0] with N hN
    change _ / tailWeight N * (tailWeight N / Real.log N) = _
    rw [div_mul_div_cancel₀ hN]
  have hh := (hb.div_atTop log_nat_atTop).add hw
  simpa only [zero_add, reciprocal_sum_by_parts, add_div] using hh

/-- A general form of the natural-to-logarithmic averaging implication. -/
theorem logarithmic_mean_of_cesaro (f : ℕ → ℝ) (d : ℝ)
    (h : Tendsto (fun N : ℕ => (∑ k ∈ range N, f k) / N) atTop (𝓝 d)) :
    Tendsto (fun N : ℕ => (∑ k ∈ range N, f k / ((k : ℝ)+1)) /
      Real.log N) atTop (𝓝 d) := by
  have hc : Tendsto (fun N : ℕ => (∑ k ∈ range N, (f k-d)) / N)
      atTop (𝓝 0) := by
    have hh := h.sub_const d
    simp only [sub_self] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    field_simp
  have hh := (logarithmic_mean_zero_of_cesaro_zero (fun k => f k-d) hc).add
    (harmonic_log_ratio.const_mul d)
  simp only [mul_one, zero_add] at hh
  apply hh.congr
  intro N
  simp only [harmonic_real_sum, div_eq_mul_inv, sub_mul, sum_sub_distrib,
    ← mul_sum]
  ring

/-- An axiom-audited replacement for the imported placeholder. -/
theorem hasLogDensity_of_hasDensity {S : Set ℕ} {d : ℝ}
    (h : S.HasDensity d) : S.HasLogDensity d := by
  classical
  let f : ℕ → ℝ := fun n => if n ∈ S then 1 else 0
  have he (N : ℕ) : (∑ k ∈ range N, f k) / N = S.partialDensity Set.univ N := by
    have he : S ∩ Set.Iio N = ↑((range N).filter fun k => k ∈ S) := by
      ext k
      simp [and_comm]
    simp only [f, sum_boole, Set.partialDensity, Set.inter_univ, Set.univ_inter,
      Nat.ncard_Iio, he, Set.ncard_coe_finset]
  have hf : Tendsto (fun N : ℕ => (∑ k ∈ range N, f k) / N) atTop (𝓝 d) := by
    simpa only [he] using h
  have hr : Tendsto (fun N : ℕ => ((N : ℝ)+1) / N) atTop (𝓝 1) := by
    have hh := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have hshift : Tendsto (fun N : ℕ => (∑ k ∈ range N, f (k+1)) / N)
      atTop (𝓝 d) := by
    have hh := ((hf.comp (tendsto_add_atTop_nat 1)).mul hr).sub
      ((tendsto_const_nhds (x := f 0)).div_atTop tendsto_natCast_atTop_atTop)
    simp only [mul_one, sub_zero] at hh
    apply hh.congr
    intro N
    simp only [Function.comp_def, sum_range_succ', Nat.cast_add, Nat.cast_one]
    have hn : (N : ℝ)+1 ≠ 0 := by positivity
    field_simp
    ring
  have hl := logarithmic_mean_of_cesaro (fun k => f (k+1)) d hshift
  change Tendsto (fun N : ℕ =>
    ∑ k ∈ (Iic N).filter (fun k => k ∈ S), (k : ℝ)⁻¹ / Real.log N) atTop (𝓝 d)
  apply hl.congr
  intro N
  rw [← sum_div, sum_filter]
  have hi : Iic N = range (N+1) := by ext k; simp
  rw [hi, sum_range_succ']
  simp only [Nat.cast_zero, inv_zero, ite_self, add_zero]
  congr 1
  apply sum_congr rfl
  intro k hk
  simp [f, div_eq_mul_inv]

end Erdos371NaturalLogDensity

#print axioms Erdos371NaturalLogDensity.logarithmic_mean_zero_of_cesaro_zero
#print axioms Erdos371NaturalLogDensity.logarithmic_mean_of_cesaro
#print axioms Erdos371NaturalLogDensity.hasLogDensity_of_hasDensity
