import Submission.Spec
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open Nat Real Finset Int

lemma a_rat_pos (n : ℕ) : 0 < a_rat n := sorry
lemma a_rat_bound (n : ℕ) (hn : 2 ≤ n) : a_rat (n + 1) ≤ (2 / 5 : ℚ) * a_rat n := sorry
lemma sum_a_rat_bound_d (j d : ℕ) (hj : 2 ≤ j) :
    ∑ i ∈ Ico j (j + d), a_rat i ≤ (1 - (2/5:ℚ)^d) * (5 / 3 : ℚ) * a_rat j := sorry

lemma sum_a_rat_strict_bound (j k : ℕ) (hj : 2 ≤ j) (hjk : j ≤ k) :
    ∑ i ∈ Icc (j + 1) k, a_rat i < a_rat j := by
  by_cases h : j + 1 ≤ k
  · have h_eq : Icc (j + 1) k = Ico (j + 1) (j + 1 + (k - j)) := by
      ext x
      simp only [mem_Icc, mem_Ico]
      omega
    rw [h_eq]
    have h1 := sum_a_rat_bound_d (j + 1) (k - j) (by linarith)
    have h2 : a_rat (j + 1) ≤ (2 / 5 : ℚ) * a_rat j := a_rat_bound j hj
    have h_pow_pos : (0 : ℚ) ≤ (2 / 5 : ℚ)^(k - j) := by positivity
    have h_pow_le : (2 / 5 : ℚ)^(k - j) ≤ 1 := by
      have h1 : (2 / 5 : ℚ) ≤ 1 := by norm_num
      have h2 : (2 / 5 : ℚ)^(k - j) ≤ 1^(k - j) := by gcongr
      rw [one_pow] at h2
      exact h2
    have h_pos_coeff : 0 ≤ (1 - (2 / 5 : ℚ)^(k - j)) * (5 / 3 : ℚ) := by linarith
    have h3 : (1 - (2 / 5 : ℚ)^(k - j)) * (5 / 3 : ℚ) * a_rat (j + 1) ≤ (1 - (2 / 5 : ℚ)^(k - j)) * (5 / 3 : ℚ) * ((2 / 5 : ℚ) * a_rat j) := by
      apply mul_le_mul_of_nonneg_left h2 h_pos_coeff
    have hp1 : (1 - (2 / 5 : ℚ)^(k - j)) * (5 / 3 : ℚ) * (2 / 5 : ℚ) ≤ (2 / 3 : ℚ) := by
      calc (1 - (2 / 5 : ℚ)^(k - j)) * (5 / 3 : ℚ) * (2 / 5 : ℚ)
        _ = (1 - (2 / 5 : ℚ)^(k - j)) * (2 / 3 : ℚ) := by ring
        _ ≤ 1 * (2 / 3 : ℚ) := by
          apply mul_le_mul_of_nonneg_right
          · linarith
          · norm_num
        _ = (2 / 3 : ℚ) := by ring
    have h4 : (1 - (2 / 5 : ℚ)^(k - j)) * (5 / 3 : ℚ) * ((2 / 5 : ℚ) * a_rat j) < a_rat j := by
      have hj_pos : 0 < a_rat j := a_rat_pos j
      calc (1 - (2 / 5 : ℚ)^(k - j)) * (5 / 3 : ℚ) * ((2 / 5 : ℚ) * a_rat j)
        _ = (1 - (2 / 5 : ℚ)^(k - j)) * (5 / 3 : ℚ) * (2 / 5 : ℚ) * a_rat j := by ring
        _ ≤ (2 / 3 : ℚ) * a_rat j := by gcongr
        _ < 1 * a_rat j := by
          apply mul_lt_mul_of_pos_right
          · norm_num
          · exact hj_pos
        _ = a_rat j := by ring
    linarith
  · have h_empty : Icc (j + 1) k = ∅ := Icc_eq_empty (by linarith)
    rw [h_empty, sum_empty]
    exact a_rat_pos j

