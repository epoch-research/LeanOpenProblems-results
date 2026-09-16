import Mathlib

import Submission.Helper10
import Submission.Helper18
import Submission.Helper27
import Submission.Helper28
import Submission.Helper29
import Submission.Helper30

open Filter Topology Real

lemma count_a_eq_helper_def2 (N m : ℕ) :
  count_a_eq_helper N m = (List.range N).countP (fun n => a_helper n == m) := by
  dsimp [count_a_eq_helper]
  rfl

lemma isBounded_count_a_eq_helper (m : ℕ) : IsBoundedUnder (· ≤ ·) atTop (fun N : ℕ => (count_a_eq_helper N m : ℝ) / N) := by
  use 1
  rw [Filter.eventually_map]
  apply Eventually.of_forall
  intro N
  by_cases hN : N = 0
  · simp [hN]
  · have : (count_a_eq_helper N m : ℝ) ≤ N := by
      have h1 : count_a_eq_helper N m ≤ N := by
        rw [count_a_eq_helper_def2]
        have hle : List.countP (fun n => a_helper n == m) (List.range N) ≤ (List.range N).length := by exact List.countP_le_length
        simp only [List.length_range] at hle
        exact hle
      exact Nat.cast_le.mpr h1
    have h_pos : (N : ℝ) > 0 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    exact (div_le_one h_pos).mpr this

lemma isCobounded_count_a_eq_helper (m : ℕ) : IsCoboundedUnder (· ≤ ·) atTop (fun N : ℕ => (count_a_eq_helper N m : ℝ) / N) := by
  use 0
  intro a_helper ha
  rw [Filter.eventually_map] at ha
  rcases Filter.nonempty_of_mem ha with ⟨n, hn⟩
  have : (0 : ℝ) ≤ (count_a_eq_helper n m : ℝ) / n := by
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
  exact le_trans this hn

lemma limsup_m_le (m : ℕ) (hm8 : m ≠ 8) :
  limsup (fun N : ℕ => (count_a_eq_helper N m : ℝ) / N) atTop ≤ 1 / 100 := by
  let C := max m 8
  have hC : m ≤ C := le_max_left m 8
  have h8 : 8 ≤ C := le_max_right m 8
  have h_bound : ∀ N : ℕ, (count_a_eq_helper N m : ℝ) / N ≤ (((N / 100 + 1 : ℕ) : ℝ) + 100 * ((List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) : ℕ)) / N := by
    intro N
    by_cases hN : N = 0
    · simp [hN]
    · have hN_pos : (N : ℝ) > 0 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
      apply (div_le_div_iff_of_pos_right hN_pos).mpr
      have hh := count_m_le_bound N C m hm8 hC h8
      have H_eq : (((N / 100 + 1 : ℕ) : ℝ) + 100 * ((List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) : ℕ)) =
                  (((N / 100 + 1) + 100 * (List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) := by
        push_cast [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        rfl
      rw [H_eq, count_a_eq_helper_def2]
      exact Nat.cast_le.mpr hh
  have h_limsup : limsup (fun N : ℕ => (count_a_eq_helper N m : ℝ) / N) atTop ≤
                  limsup (fun N : ℕ => (((N / 100 + 1 : ℕ) : ℝ) + 100 * ((List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) : ℕ)) / N) atTop := by
    apply limsup_le_limsup (Eventually.of_forall h_bound) (isCobounded_count_a_eq_helper m) (tendsto_upper_bound C).isBoundedUnder_le
  have h_lim := tendsto_upper_bound C
  have h_lim_eq : limsup (fun N : ℕ => (((N / 100 + 1 : ℕ) : ℝ) + 100 * ((List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) : ℕ)) / N) atTop = 1 / 100 := by
    exact Filter.Tendsto.limsup_eq h_lim
  rw [h_lim_eq] at h_limsup
  exact h_limsup

lemma limsup_8_ge :
  9 / 100 ≤ limsup (fun N : ℕ => (count_a_eq_helper N 8 : ℝ) / N) atTop := by
  let C := 8
  have h8 : 8 ≤ C := le_refl 8
  have h_bound : ∀ N : ℕ, (9 * ((N / 100 : ℕ) : ℝ) - 9 * ((List.range (N / 100)).countP (fun q => decide (S q ≤ C)) : ℕ)) / N ≤ (count_a_eq_helper N 8 : ℝ) / N := by
    intro N
    by_cases hN : N = 0
    · simp [hN]
    · have hN_pos : (N : ℝ) > 0 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
      apply (div_le_div_iff_of_pos_right hN_pos).mpr
      have h1 : 9 * (N / 100) - 9 * (List.range (N / 100)).countP (fun q => decide (S q ≤ C)) ≤ count_a_eq_helper N 8 := by
        rw [count_a_eq_helper_def2]
        exact count_8_ge_bound N C h8
      have H_eq : 9 * ((N / 100 : ℕ) : ℝ) - 9 * ((List.range (N / 100)).countP (fun q => decide (S q ≤ C)) : ℕ) =
                  ((9 * (N / 100) - 9 * (List.range (N / 100)).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) := by
        have h_le : 9 * (List.range (N / 100)).countP (fun q => decide (S q ≤ C)) ≤ 9 * (N / 100) := by
          apply Nat.mul_le_mul_left
          have hle2 : (List.range (N / 100)).countP (fun q => decide (S q ≤ C)) ≤ (List.range (N / 100)).length := by exact List.countP_le_length
          simp only [List.length_range] at hle2
          exact hle2
        rw [Nat.cast_sub h_le]
        push_cast [Nat.cast_mul]
        rfl
      rw [H_eq]
      exact Nat.cast_le.mpr h1
  have h_limsup : limsup (fun N : ℕ => (9 * ((N / 100 : ℕ) : ℝ) - 9 * ((List.range (N / 100)).countP (fun q => decide (S q ≤ C)) : ℕ)) / N) atTop ≤
                  limsup (fun N : ℕ => (count_a_eq_helper N 8 : ℝ) / N) atTop := by
    apply limsup_le_limsup (Eventually.of_forall h_bound) (tendsto_lower_bound C).isCoboundedUnder_le (isBounded_count_a_eq_helper 8)
  have h_lim := tendsto_lower_bound C
  have h_lim_eq : limsup (fun N : ℕ => (9 * ((N / 100 : ℕ) : ℝ) - 9 * ((List.range (N / 100)).countP (fun q => decide (S q ≤ C)) : ℕ)) / N) atTop = 9 / 100 := by
    exact Filter.Tendsto.limsup_eq h_lim
  rw [h_lim_eq] at h_limsup
  exact h_limsup
