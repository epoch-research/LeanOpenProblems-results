import Mathlib
import Submission.Helper10
import Submission.Helper19
import Submission.Helper22
import Submission.Helper23
import Submission.Helper24
import Submission.Helper25
import Submission.Helper26

open Finset

lemma countP_eq_sum_boole (K : ℕ) (p : ℕ → Bool) :
  (List.range K).countP p = ∑ q ∈ Finset.range K, if p q = true then 1 else 0 := by
  induction K with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.countP_append, sum_range_succ, ← ih]
    have : (List.countP p [k]) = if p k = true then 1 else 0 := by
      rw [List.countP_cons, List.countP_nil]
      exact zero_add _
    omega

lemma sum_ite_bound (K C : ℕ) :
  (∑ q ∈ Finset.range K, if S q ≤ C then 100 else 1) ≤
  K + 100 * (List.range K).countP (fun q => decide (S q ≤ C)) := by
  have H : (∑ q ∈ Finset.range K, if S q ≤ C then 100 else 1) =
           (∑ q ∈ Finset.range K, if S q ≤ C then 99 else 0) + K := by
    have : (∑ q ∈ Finset.range K, if S q ≤ C then 100 else 1) =
           (∑ q ∈ Finset.range K, ((if S q ≤ C then 99 else 0) + 1)) := by
      apply sum_congr rfl
      intros x _
      by_cases h : S x ≤ C
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
    rw [this, sum_add_distrib]
    have : (∑ q ∈ Finset.range K, 1) = K := by simp
    rw [this]
  have h1 : (∑ q ∈ Finset.range K, if S q ≤ C then 99 else 0) =
            99 * (List.range K).countP (fun q => decide (S q ≤ C)) := by
    have : (∑ q ∈ Finset.range K, if S q ≤ C then 99 else 0) =
           ∑ q ∈ Finset.range K, 99 * (if decide (S q ≤ C) = true then 1 else 0) := by
      apply sum_congr rfl
      intros x _
      by_cases h : S x ≤ C
      · have hd : decide (S x ≤ C) = true := decide_eq_true h
        rw [if_pos h, if_pos hd]
      · have hd : decide (S x ≤ C) = false := decide_eq_false h
        rw [if_neg h, if_neg (by intro H2; rw [hd] at H2; contradiction)]
    rw [this, ← mul_sum, ← countP_eq_sum_boole K (fun q => decide (S q ≤ C))]
  rw [h1] at H
  omega

lemma count_m_le_bound (N C m : ℕ) (hm8 : m ≠ 8) (hC : m ≤ C) (h8 : 8 ≤ C) :
  (List.range N).countP (fun n => a_helper n == m) ≤
  (N / 100 + 1) + 100 * (List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) := by
  have H : (List.range N).countP (fun n => a_helper n == m) =
           ∑ q ∈ Finset.range (N / 100 + 1), ((List.range N).filter (fun n => n / 100 == q)).countP (fun n => a_helper n == m) := by
    apply sum_countP_filter
    intros n hn
    simp only [List.mem_range] at hn
    simp only [mem_range]
    have : n / 100 < N / 100 + 1 := by omega
    exact this
  rw [H]
  have H_le : (∑ q ∈ Finset.range (N / 100 + 1), ((List.range N).filter (fun n => n / 100 == q)).countP (fun n => a_helper n == m)) ≤
              ∑ q ∈ Finset.range (N / 100 + 1), if S q ≤ C then 100 else 1 := by
    apply sum_le_sum
    intros q hq
    exact count_m_le_1 N q C m hm8 hC h8
  have H_bound := sum_ite_bound (N / 100 + 1) C
  omega
