import FormalConjecturesUtil

/-!
# An exact fractional relaxation of Erdős Problem 66

This file constructs a decreasing fractional profile with harmonic self-convolution.
It does not round that profile to a set of natural numbers.
-/

namespace Erdos66Fractional
open AdditiveCombinatorics

noncomputable def stepMass : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 / (((n : ℝ) + 1) * (n + 2)) +
      ∑ i : Fin n, stepMass (i.val + 1) * stepMass (n - i.val)) / 2
termination_by n => n

noncomputable def kernelCoeff (n : ℕ) : ℝ := if n = 0 then 0 else 1 / ((n : ℝ) * (n + 1))

@[simp] lemma stepMass_zero : stepMass 0 = 0 := by rw [stepMass]

lemma stepMass_succ (n : ℕ) : stepMass (n + 1) =
    (1 / (((n : ℝ) + 1) * (n + 2)) +
      ∑ i : Fin n, stepMass (i.val + 1) * stepMass (n - i.val)) / 2 := by
  rw [stepMass]

lemma stepMass_nonneg (n : ℕ) : 0 ≤ stepMass n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [stepMass_succ]
      apply div_nonneg _ (by norm_num)
      apply add_nonneg (by positivity)
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (ih _ (by have := i.isLt; omega)) (ih _ (by omega))

lemma convolution_zero_boundary (s : ℕ → ℝ) (hs : s 0 = 0) (n : ℕ) :
    sumConv s s (n + 1) = ∑ i : Fin n, s (i.val + 1) * s (n - i.val) := by
  unfold sumConv
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, hs, mul_zero, add_zero]
  rw [Finset.sum_range_succ']
  simp only [hs, zero_mul, add_zero, Nat.sub_zero]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dif_pos (Finset.mem_range.mp hi)]
  simp only [Nat.add_sub_add_right]

lemma stepMass_recurrence (n : ℕ) :
    2 * stepMass n = kernelCoeff n + sumConv stepMass stepMass n := by
  cases n with
  | zero => simp [sumConv, kernelCoeff]
  | succ n =>
    rw [stepMass_succ, convolution_zero_boundary stepMass stepMass_zero]
    simp only [kernelCoeff, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
      Nat.cast_add, Nat.cast_one]
    ring

lemma kernelCoeff_partial (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), kernelCoeff n) = 1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp [kernelCoeff]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [kernelCoeff, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
      Nat.cast_add, Nat.cast_one]
    have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (N : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring

lemma cumulative_convolution_bound (s : ℕ → ℝ) (hs0 : s 0 = 0)
    (hs : ∀ n, 0 ≤ s n) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), sumConv s s n) ≤ (∑ i ∈ Finset.range N, s i) ^ 2 := by
  classical
  let B := (Finset.range N).product (Finset.range N)
  have hbound (n : ℕ) (hn : n ≤ N) : sumConv s s n ≤
      ∑ p ∈ B, if p.1 + p.2 = n then s p.1 * s p.2 else 0 := by
    let D := (Finset.antidiagonal n).filter (fun p ↦ p.1 < N ∧ p.2 < N)
    have heq : sumConv s s n = ∑ p ∈ D, s p.1 * s p.2 := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p hp hnot
      have hsum := Finset.mem_antidiagonal.mp hp
      have hbad : ¬(p.1 < N ∧ p.2 < N) := by
        intro h
        exact hnot (Finset.mem_filter.mpr ⟨hp, h⟩)
      have hz : p.1 = 0 ∨ p.2 = 0 := by omega
      rcases hz with hz | hz <;> simp [hz, hs0]
    rw [heq, ← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp, hpN⟩ := Finset.mem_filter.mp hp
      apply Finset.mem_filter.mpr
      refine ⟨?_, Finset.mem_antidiagonal.mp hp⟩
      simp only [B, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
      exact hpN
    · intro p hp hnot
      exact mul_nonneg (hs p.1) (hs p.2)
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1), ∑ p ∈ B,
        if p.1 + p.2 = n then s p.1 * s p.2 else 0 := by
      apply Finset.sum_le_sum
      intro n hn
      exact hbound n (by have := Finset.mem_range.mp hn; omega)
    _ = ∑ p ∈ B, if p.1 + p.2 ∈ Finset.range (N + 1) then s p.1 * s p.2 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      simp
    _ ≤ ∑ p ∈ B, s p.1 * s p.2 := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs
      · rfl
      · exact mul_nonneg (hs p.1) (hs p.2)
    _ = _ := by
      simp only [B, Finset.product_eq_sprod, Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul, pow_two]

lemma stepMass_partial_le_one (N : ℕ) : (∑ i ∈ Finset.range N, stepMass i) ≤ 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hnonneg : 0 ≤ ∑ i ∈ Finset.range N, stepMass i :=
      Finset.sum_nonneg (fun i hi ↦ stepMass_nonneg i)
    have hsq : (∑ i ∈ Finset.range N, stepMass i) ^ 2 ≤ 1 := by nlinarith
    have hconv := cumulative_convolution_bound stepMass stepMass_zero stepMass_nonneg N
    have he : 2 * (∑ i ∈ Finset.range (N + 1), stepMass i) =
        (1 - 1 / ((N : ℝ) + 1)) + ∑ i ∈ Finset.range (N + 1), sumConv stepMass stepMass i := by
      rw [Finset.mul_sum]
      simp_rw [stepMass_recurrence]
      rw [Finset.sum_add_distrib, kernelCoeff_partial]
    have hinv : 0 ≤ 1 / ((N : ℝ) + 1) := by positivity
    nlinarith

noncomputable def profile (n : ℕ) : ℝ := 1 - ∑ i ∈ Finset.range (n + 1), stepMass i

lemma profile_nonneg (n : ℕ) : 0 ≤ profile n := sub_nonneg.mpr (stepMass_partial_le_one _)

lemma profile_le_one (n : ℕ) : profile n ≤ 1 := by
  apply sub_le_self
  exact Finset.sum_nonneg (fun i hi ↦ stepMass_nonneg i)

@[simp] lemma profile_zero : profile 0 = 1 := by simp [profile]

lemma profile_succ (n : ℕ) : profile (n + 1) = profile n - stepMass (n + 1) := by
  simp only [profile, Finset.sum_range_succ]
  ring

lemma profile_antitone : Antitone profile := by
  apply antitone_nat_of_succ_le
  intro n
  rw [profile_succ]
  exact sub_le_self _ (stepMass_nonneg _)

open PowerSeries

lemma mass_series_equation :
    2 * PowerSeries.mk stepMass = PowerSeries.mk kernelCoeff + (PowerSeries.mk stepMass) ^ 2 := by
  ext n
  simp only [two_mul, map_add, coeff_mk, pow_two, coeff_mul]
  change stepMass n + stepMass n = kernelCoeff n + sumConv stepMass stepMass n
  linarith [stepMass_recurrence n]

lemma profile_first_difference :
    (1 - X) * PowerSeries.mk profile = 1 - PowerSeries.mk stepMass := by
  rw [sub_mul, one_mul]
  ext n
  cases n with
  | zero => simp
  | succ n =>
    simp only [map_sub, coeff_succ_X_mul, coeff_mk, coeff_one, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, if_false, zero_sub]
    rw [profile_succ]
    ring

lemma harmonic_first_difference :
    (1 - X) * PowerSeries.mk (fun n ↦ (harmonic (n + 1) : ℝ)) =
      PowerSeries.mk (fun n ↦ 1 / ((n : ℝ) + 1)) := by
  rw [sub_mul, one_mul]
  ext n
  cases n with
  | zero => norm_num [harmonic]
  | succ n =>
    simp only [map_sub, coeff_succ_X_mul, coeff_mk, harmonic_succ, Rat.cast_add,
      Rat.cast_inv, Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
    ring

lemma reciprocal_first_difference :
    (1 - X) * PowerSeries.mk (fun n ↦ 1 / ((n : ℝ) + 1)) =
      1 - PowerSeries.mk kernelCoeff := by
  rw [sub_mul, one_mul]
  ext n
  cases n with
  | zero => simp [kernelCoeff]
  | succ n =>
    simp only [map_sub, coeff_succ_X_mul, coeff_mk, coeff_one, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, if_false, zero_sub, kernelCoeff, Nat.cast_add, Nat.cast_one]
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring

lemma profile_series_square :
    (PowerSeries.mk profile) ^ 2 = PowerSeries.mk (fun n ↦ (harmonic (n + 1) : ℝ)) := by
  have hne : (1 - X : PowerSeries ℝ) ≠ 0 := by
    intro h
    have hh := congrArg (constantCoeff (R := ℝ)) h
    simpa using hh
  apply mul_left_cancel₀ (pow_ne_zero 2 hne)
  calc
    (1 - X) ^ 2 * (PowerSeries.mk profile) ^ 2 =
        ((1 - X) * PowerSeries.mk profile) ^ 2 := (mul_pow _ _ _).symm
    _ = (1 - PowerSeries.mk stepMass) ^ 2 := by rw [profile_first_difference]
    _ = 1 - PowerSeries.mk kernelCoeff := by
      linear_combination -mass_series_equation
    _ = (1 - X) ^ 2 * PowerSeries.mk (fun n ↦ (harmonic (n + 1) : ℝ)) := by
      rw [pow_two, mul_assoc, harmonic_first_difference, reciprocal_first_difference]

/-- The fractional profile has exactly the desired harmonic convolution. -/
lemma profile_convolution (n : ℕ) :
    sumConv profile profile n = (harmonic (n + 1) : ℝ) := by
  have hh := congrArg (coeff n) profile_series_square
  simpa only [pow_two, coeff_mul, coeff_mk, sumConv] using hh

open Filter
open scoped Topology

lemma harmonic_shift_log_ratio :
    Tendsto (fun n : ℕ ↦ (harmonic (n + 1) : ℝ) / Real.log n) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdiff := Real.tendsto_harmonic_sub_log.add
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simp only [add_zero] at hdiff
  have hh := (hdiff.div_atTop hlog).add_const 1
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hl : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  rw [harmonic_succ]
  push_cast
  field_simp
  ring

lemma profile_log_limit :
    Tendsto (fun n ↦ sumConv profile profile n / Real.log n) atTop (𝓝 1) := by
  simpa only [profile_convolution] using harmonic_shift_log_ratio

/-- A complete solution of the fractional relaxation, not of the set-valued conjecture. -/
theorem exists_fractional_harmonic_profile :
    ∃ p : ℕ → ℝ, (∀ n, 0 ≤ p n ∧ p n ≤ 1) ∧ Antitone p ∧
      (∀ n, sumConv p p n = (harmonic (n + 1) : ℝ)) ∧
      Tendsto (fun n ↦ sumConv p p n / Real.log n) atTop (𝓝 1) := by
  exact ⟨profile, fun n ↦ ⟨profile_nonneg n, profile_le_one n⟩, profile_antitone,
    profile_convolution, profile_log_limit⟩

end Erdos66Fractional
