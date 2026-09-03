import FormalConjecturesUtil
import Submission.CofactorLabels

/-! A cofactor-label energy criterion for Erdős 371. The support estimate is
unconditional; the near-linear signed energy estimate remains a hypothesis. -/

namespace Erdos371CofactorLabelEnergy

open Finset Filter Erdos371CofactorLabels Erdos371Cofactor
open scoped Topology

attribute [local instance] Classical.propDecidable

abbrev sign := Erdos371PrimeDiscrepancy.sign
abbrev total := Erdos371PrimeDiscrepancy.total

def label (n : ℕ) : ℕ := min (cofactor n) (cofactor (n+1))

def group (a N : ℕ) : ℤ := ∑ n ∈ range N, if label n = a then sign n else 0

noncomputable def energy (N : ℕ) : ℝ :=
  ∑ a ∈ labels (N+1), (group a N:ℝ)^2

lemma label_mem {n N : ℕ} (hn : n < N) : label n ∈ labels (N+1) := by
  unfold label
  by_cases h : cofactor n ≤ cofactor (n+1)
  · rw [min_eq_left h]
    exact mem_image.mpr ⟨n, mem_range.mpr (by omega), rfl⟩
  · rw [min_eq_right (le_of_not_ge h)]
    exact mem_image.mpr ⟨n+1, mem_range.mpr (by omega), rfl⟩

lemma total_eq_groups (N : ℕ) : total N = ∑ a ∈ labels (N+1), group a N := by
  unfold group
  rw [sum_comm]
  unfold total Erdos371PrimeDiscrepancy.total
  apply sum_congr rfl
  intro n hn
  simp [label_mem (mem_range.mp hn)]

lemma energy_nonneg (N : ℕ) : 0 ≤ energy N :=
  sum_nonneg (fun _ _ => sq_nonneg _)

lemma total_sq_le (N : ℕ) : (total N:ℝ)^2 ≤ (labels (N+1)).card * energy N := by
  rw [total_eq_groups]
  push_cast
  exact sq_sum_le_card_mul_sum_sq
    (s := labels (N+1)) (f := fun a => (group a N:ℝ))

/-- This criterion does not assert its energy hypothesis. Unlike the support
of prime labels, the cofactor-label support saves every fixed logarithmic
power, so a fixed polylogarithmic energy loss can be absorbed directly. -/
theorem density_half_of_polylog_energy (B : ℕ) {C : ℝ}
    (hE : ∀ᶠ N : ℕ in atTop, energy N ≤ C*N*Real.log (N:ℝ)^B) :
    {n | Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)}.HasDensity (1/2) := by
  apply Erdos371PrimeDiscrepancy.density_half_iff_total_mean_zero.mpr
  have hu : Tendsto (fun N : ℕ =>
      Real.sqrt (C*(((labels (N+1)).card:ℝ)*Real.log (N:ℝ)^B/N)))
      atTop (𝓝 0) := by
    simpa using ((shifted_labels_log_pow_div_tendsto_zero B).const_mul C).sqrt
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun _ => abs_nonneg _
  · filter_upwards [hE, eventually_gt_atTop 0] with N hEN hN
    change |(total N:ℝ)/N| ≤ _
    apply Real.le_sqrt_of_sq_le
    rw [sq_abs, div_pow]
    have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
    calc
      _ ≤ ((labels (N+1)).card:ℝ)*energy N/(N:ℝ)^2 :=
        div_le_div_of_nonneg_right (total_sq_le N) (sq_nonneg _)
      _ ≤ ((labels (N+1)).card:ℝ)*(C*N*Real.log (N:ℝ)^B)/(N:ℝ)^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hEN (by positivity))
          (sq_nonneg _)
      _ = _ := by field_simp

end Erdos371CofactorLabelEnergy

#print axioms Erdos371CofactorLabelEnergy.total_eq_groups
#print axioms Erdos371CofactorLabelEnergy.density_half_of_polylog_energy
