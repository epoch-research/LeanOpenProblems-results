import Mathlib

import Submission.Helper10
import Submission.Helper18
import Submission.Helper25
import Submission.Helper27
import Submission.Helper28
import Submission.Helper29

open Filter Topology Real

lemma countP_mono (p : ℕ → Bool) (n m : ℕ) (h : n ≤ m) :
  (List.range n).countP p ≤ (List.range m).countP p := by
  apply list_countP_le_of_subset_nodup
  · intro x hx
    simp only [List.mem_range] at hx ⊢
    omega
  · exact List.nodup_range

lemma tendsto_W_upper (C : ℕ) :
  Tendsto (fun N : ℕ => (((List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) / N)
    atTop (nhds 0) := by
  have h_lower : ∀ N : ℕ, (0 : ℝ) ≤ (((List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) / N := by
    intro N
    apply div_nonneg
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
  have h_upper : ∀ N : ℕ, N ≥ 1 → (((List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) / N ≤
    (((List.range N).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) / N := by
    intro N hN
    apply div_le_div_of_nonneg_right
    · exact_mod_cast countP_mono _ _ _ (by omega)
    · exact Nat.cast_nonneg _
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
  · exact tendsto_const_nhds
  · exact S_gt_C_tendsto C
  · exact h_lower
  · intro N
    by_cases h : N ≥ 1
    · exact h_upper N h
    · have : N = 0 := by omega
      simp [this]

lemma tendsto_upper_bound (C : ℕ) :
  Tendsto (fun N : ℕ => (((N / 100 + 1 : ℕ) : ℝ) + 100 * ((List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) : ℕ)) / N)
    atTop (nhds (1 / 100)) := by
  have eq : (fun N : ℕ => (((N / 100 + 1 : ℕ) : ℝ) + 100 * ((List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) : ℕ)) / N) =
            (fun N : ℕ => ((N / 100 : ℕ) : ℝ) / N + 1 / N + 100 * ((((List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) / N)) := by
    ext N
    by_cases hN : N = 0
    · simp [hN]
    · have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
      calc (((N / 100 + 1 : ℕ) : ℝ) + 100 * ((List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) : ℕ)) / N
        _ = (((N / 100 : ℕ) : ℝ) + 1 + 100 * ((List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) : ℕ)) / N := by push_cast; rfl
        _ = ((N / 100 : ℕ) : ℝ) / N + 1 / N + 100 * ((((List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) / N) := by ring
  rw [eq]
  have h1 : Tendsto (fun N : ℕ => ((N / 100 : ℕ) : ℝ) / N + 1 / N) atTop (nhds (1 / 100 + 0)) := by
    apply Tendsto.add
    · exact tendsto_div_100
    · exact tendsto_one_div_atTop_nhds_zero_nat
  rw [add_zero] at h1
  have h2 : Tendsto (fun N : ℕ => 100 * ((((List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) / N)) atTop (nhds (100 * 0)) := by
    apply Tendsto.const_mul
    exact tendsto_W_upper C
  rw [mul_zero] at h2
  have h3 : Tendsto (fun N : ℕ => ((N / 100 : ℕ) : ℝ) / N + 1 / N + 100 * ((((List.range (N / 100 + 1)).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) / N)) atTop (nhds (1 / 100 + 0)) := by
    apply Tendsto.add h1 h2
  rw [add_zero] at h3
  exact h3

lemma tendsto_lower_bound (C : ℕ) :
  Tendsto (fun N : ℕ => (9 * ((N / 100 : ℕ) : ℝ) - 9 * ((List.range (N / 100)).countP (fun q => decide (S q ≤ C)) : ℕ)) / N)
    atTop (nhds (9 / 100)) := by
  have eq : (fun N : ℕ => (9 * ((N / 100 : ℕ) : ℝ) - 9 * ((List.range (N / 100)).countP (fun q => decide (S q ≤ C)) : ℕ)) / N) =
            (fun N : ℕ => 9 * (((N / 100 : ℕ) : ℝ) / N) - 9 * ((((List.range (N / 100)).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) / N)) := by
    ext N
    by_cases hN : N = 0
    · simp [hN]
    · have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
      ring
  rw [eq]
  have h1 : Tendsto (fun N : ℕ => 9 * (((N / 100 : ℕ) : ℝ) / N)) atTop (nhds (9 * (1 / 100))) := by
    apply Tendsto.const_mul
    exact tendsto_div_100
  have h_W : Tendsto (fun N : ℕ => (((List.range (N / 100)).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) / N) atTop (nhds 0) := by
    have h_lower : ∀ N : ℕ, (0 : ℝ) ≤ (((List.range (N / 100)).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) / N := by
      intro N
      apply div_nonneg
      · exact Nat.cast_nonneg _
      · exact Nat.cast_nonneg _
    have h_upper : ∀ N : ℕ, (((List.range (N / 100)).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) / N ≤
      (((List.range N).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) / N := by
      intro N
      apply div_le_div_of_nonneg_right
      · exact_mod_cast countP_mono _ _ _ (by omega)
      · exact Nat.cast_nonneg _
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    · exact tendsto_const_nhds
    · exact S_gt_C_tendsto C
    · exact h_lower
    · exact h_upper
  have h2 : Tendsto (fun N : ℕ => 9 * ((((List.range (N / 100)).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) / N)) atTop (nhds (9 * 0)) := by
    apply Tendsto.const_mul
    exact h_W
  have h3 : Tendsto (fun N : ℕ => 9 * (((N / 100 : ℕ) : ℝ) / N) - 9 * ((((List.range (N / 100)).countP (fun q => decide (S q ≤ C)) : ℕ) : ℝ) / N)) atTop (nhds (9 * (1 / 100) - 9 * 0)) := by
    apply Tendsto.sub h1 h2
  have eq_lim : 9 * (1 / 100 : ℝ) - 9 * 0 = 9 / 100 := by ring
  rw [eq_lim] at h3
  exact h3
