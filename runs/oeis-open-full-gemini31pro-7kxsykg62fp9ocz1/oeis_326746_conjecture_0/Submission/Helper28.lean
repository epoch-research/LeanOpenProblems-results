import Mathlib
import Submission.Helper10
import Submission.Helper19
import Submission.Helper22
import Submission.Helper23
import Submission.Helper24
import Submission.Helper25
import Submission.Helper26
import Submission.Helper27

open Finset

lemma sum_ite_lower_bound (K C : ℕ) :
  (∑ q ∈ Finset.range K, if S q ≤ C then 0 else 9) =
  9 * K - 9 * (List.range K).countP (fun q => decide (S q ≤ C)) := by
  have H1 : (∑ q ∈ Finset.range K, if S q ≤ C then 0 else 9) +
            (∑ q ∈ Finset.range K, if S q ≤ C then 9 else 0) =
            ∑ q ∈ Finset.range K, 9 := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intros x _
    by_cases h : S x ≤ C
    · simp [h]
    · simp [h]
  have H2 : (∑ q ∈ Finset.range K, 9) = 9 * K := by simp [mul_comm]
  have H3 : (∑ q ∈ Finset.range K, if S q ≤ C then 9 else 0) =
            9 * (List.range K).countP (fun q => decide (S q ≤ C)) := by
    have : (∑ q ∈ Finset.range K, if S q ≤ C then 9 else 0) =
           ∑ q ∈ Finset.range K, 9 * (if decide (S q ≤ C) = true then 1 else 0) := by
      apply sum_congr rfl
      intros x _
      by_cases h : S x ≤ C
      · have hd : decide (S x ≤ C) = true := decide_eq_true h
        rw [if_pos h, if_pos hd]
      · have hd : decide (S x ≤ C) = false := decide_eq_false h
        rw [if_neg h, if_neg (by intro H2; rw [hd] at H2; contradiction)]
    rw [this, ← mul_sum, ← countP_eq_sum_boole K (fun q => decide (S q ≤ C))]
  omega

lemma count_8_ge_bound (N C : ℕ) (hC : 8 ≤ C) :
  (List.range N).countP (fun n => a_helper n == 8) ≥
  9 * (N / 100) - 9 * (List.range (N / 100)).countP (fun q => decide (S q ≤ C)) := by
  have H_eq : (List.range N).countP (fun n => a_helper n == 8) =
              ∑ q ∈ Finset.range (N / 100 + 1), ((List.range N).filter (fun n => n / 100 == q)).countP (fun n => a_helper n == 8) := by
    apply sum_countP_filter
    intros n hn
    simp only [List.mem_range] at hn
    simp only [mem_range]
    have : n / 100 < N / 100 + 1 := by omega
    exact this
  have H_ge : (∑ q ∈ Finset.range (N / 100), ((List.range N).filter (fun n => n / 100 == q)).countP (fun n => a_helper n == 8)) ≤
              ∑ q ∈ Finset.range (N / 100 + 1), ((List.range N).filter (fun n => n / 100 == q)).countP (fun n => a_helper n == 8) := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro x hx
      simp only [mem_range] at hx ⊢
      omega
    · intros _ _ _
      exact Nat.zero_le _
  have H_lower : (∑ q ∈ Finset.range (N / 100), if S q ≤ C then 0 else 9) ≤
                 ∑ q ∈ Finset.range (N / 100), ((List.range N).filter (fun n => n / 100 == q)).countP (fun n => a_helper n == 8) := by
    apply sum_le_sum
    intros q hq
    simp only [mem_range] at hq
    by_cases hqC : S q ≤ C
    · simp [hqC]
    · simp [hqC]
      have hN : 100 * q + 100 ≤ N := by omega
      have hq_gt : S q > C := by omega
      exact count_8_ge_9 N q C hC hq_gt hN
  have H_bound := sum_ite_lower_bound (N / 100) C
  omega
