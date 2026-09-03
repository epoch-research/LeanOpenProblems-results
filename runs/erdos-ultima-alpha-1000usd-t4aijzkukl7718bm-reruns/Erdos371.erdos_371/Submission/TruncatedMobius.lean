import FormalConjecturesUtil
import Submission.SeparateAlladi
import Submission.SmoothDensity

/-! Truncation by the least prime factor in the separate Möbius expansion.
This discards only comparisons with a bounded winning prime. -/

namespace Erdos371TruncatedMobius

open Erdos371SeparateAlladi Erdos371PrimeDiscrepancy Erdos371Exploration

set_option autoImplicit false

def signedCut (y n : ℕ) : ℤ := if y < winner n then sign n else 0

def cutTotal (y N : ℕ) : ℝ := ∑ n ∈ Finset.range N, (signedCut y n : ℝ)

lemma roughWeight_max (y k d : ℕ) :
    roughWeight (max y k) d = if y < d.minFac then roughWeight k d else 0 := by
  unfold roughWeight
  simp only [max_lt_iff]
  split_ifs <;> simp_all

lemma truncated_divisor_form {n : ℕ} (hn : 1 < n) (y k : ℕ) :
    (∑ d ∈ n.divisors with y < d.minFac, roughWeight k d) =
      -below (max y k) (P n) := by
  rw [Finset.sum_filter]
  simp_rw [← roughWeight_max]
  exact alladi_divisor_form hn _

lemma cut_separate_expansion {n : ℕ} (hn : 1 < n) (y : ℕ) :
    signedCut y n =
      (∑ d ∈ n.divisors with y < d.minFac, roughWeight (P (n + 1)) d) -
      (∑ d ∈ (n + 1).divisors with y < d.minFac, roughWeight (P n) d) := by
  rw [truncated_divisor_form hn, truncated_divisor_form (by omega : 1 < n + 1)]
  have hne := consecutive_ne n
  by_cases h : P n < P (n + 1)
  · simp only [signedCut, winner, max_eq_right h.le, sign, if_pos h, below, max_lt_iff]
    have hh : ¬P (n + 1) < P n := Nat.not_lt_of_ge h.le
    simp only [hh, and_false, if_false, neg_zero, h, and_true]
    split_ifs <;> norm_num
  · have hh : P (n + 1) < P n := by omega
    simp only [signedCut, winner, max_eq_left hh.le, sign, if_neg h, below, max_lt_iff,
      h, and_false, if_false, neg_zero, hh, and_true]
    split_ifs <;> norm_num

lemma cut_error_int (y n : ℕ) :
    |sign n - signedCut y n| ≤ if P n ≤ y then 1 else 0 := by
  by_cases h : y < winner n
  · simp only [signedCut, if_pos h, sub_self, abs_zero]
    split_ifs <;> norm_num
  · have hn : P n ≤ y := (le_max_left _ _).trans (Nat.le_of_not_gt h)
    simp only [signedCut, if_neg h, sub_zero, if_pos hn]
    unfold sign
    split_ifs <;> norm_num

lemma cut_error_bound (y N : ℕ) :
    |(total N : ℝ) / N - cutTotal y N / N| ≤
      {n | P n ≤ y}.partialDensity Set.univ N := by
  rw [← sub_div, abs_div,
    show |(N : ℝ)| = (N : ℝ) from abs_of_nonneg (Nat.cast_nonneg N),
    bounded_maxPrimeFac_partialDensity]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  unfold total cutTotal
  push_cast
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.range N, |(sign n : ℝ) - (signedCut y n : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range N, (if P n ≤ y then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro n hn
      exact_mod_cast cut_error_int y n
    _ = _ := by simp

open Filter
open scoped Topology

lemma cut_error_tendsto_zero (y : ℕ) :
    Tendsto (fun N : ℕ => (total N : ℝ) / N - cutTotal y N / N) atTop (𝓝 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (bounded_maxPrimeFac_hasDensity_zero y)
  · intro N
    exact abs_nonneg _
  · intro N
    exact cut_error_bound y N

lemma density_half_iff_cut_mean (y : ℕ) :
    {n | P n < P (n + 1)}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => cutTotal y N / N) atTop (𝓝 0) := by
  rw [density_half_iff_total_mean_zero]
  constructor
  · intro h
    have hh := h.sub (cut_error_tendsto_zero y)
    simp only [sub_zero] at hh
    apply hh.congr
    intro N
    ring
  · intro h
    have hh := h.add (cut_error_tendsto_zero y)
    simp only [add_zero] at hh
    apply hh.congr
    intro N
    ring

end Erdos371TruncatedMobius

#print axioms Erdos371TruncatedMobius.cut_separate_expansion
#print axioms Erdos371TruncatedMobius.cut_error_int

#print axioms Erdos371TruncatedMobius.cut_error_tendsto_zero
#print axioms Erdos371TruncatedMobius.density_half_iff_cut_mean
