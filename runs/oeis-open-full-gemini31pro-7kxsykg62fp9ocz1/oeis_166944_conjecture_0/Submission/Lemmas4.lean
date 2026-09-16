import Submission.Lemmas
import Mathlib

lemma C_add_d (k : ℕ) (hk : 1 ≤ k) : C (k + 1) = C k + d (k + 1) - 1 := by
  have ha : a (k + 1) = C (k + 1) + (k + 1) := a_eq_C_add_n _
  have hak : a k = C k + k := a_eq_C_add_n _
  have hd : d (k + 1) = a (k + 1) - a k := rfl
  have hC_mono : C k ≤ C (k + 1) := C_mono hk
  omega

lemma d_pos (k : ℕ) (hk : 1 ≤ k) : 1 ≤ d (k + 1) := by
  have hd : d (k + 1) = a (k + 1) - a k := rfl
  have hC_mono : C k ≤ C (k + 1) := C_mono hk
  have ha : a (k + 1) = C (k + 1) + (k + 1) := a_eq_C_add_n _
  have hak : a k = C k + k := a_eq_C_add_n _
  omega

lemma n_le_C_prev_add_3 (n : ℕ) (hn : 2 ≤ n) : n ≤ C (n - 1) + 3 := by
  induction n, hn using Nat.le_induction with
  | base =>
    have : C 1 = 1 := rfl
    omega
  | succ k hk ih =>
    have hk1 : 1 ≤ k - 1 := by omega
    have hk2 : 1 ≤ k := by omega
    have hd : 1 ≤ d k := by
      have : k = k - 1 + 1 := by omega
      rw [this]
      exact d_pos (k - 1) hk1
    have hC : C k = C (k - 1) + d k - 1 := by
      have : k = k - 1 + 1 := by omega
      nth_rw 1 [this]
      exact C_add_d (k - 1) hk1
    by_cases h_d_1 : d k = 1
    · rw [h_d_1] at hC
      have : C k = C (k - 1) := by omega
      by_cases h_k : k = C (k - 1) + 3
      · sorry
      · omega
    · have h_d_gt_1 : d k ≥ 2 := by omega
      have : C k ≥ C (k - 1) + 1 := by omega
      omega
