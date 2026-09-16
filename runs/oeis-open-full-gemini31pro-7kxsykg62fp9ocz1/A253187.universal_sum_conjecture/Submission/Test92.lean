import Submission.Spec
open Nat Finset

theorem check_disproof2 : ¬ (
  (∀ n : ℕ, A253187 n > 0) ∧
  ∀ k m, (k, m) ∈ C_pairs →
    ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
      (P_k_first k x) + (P_k_second k y) + (polygonal_num_val m z).toNat = n
) := by
  intro h
  have h_A : ∀ n, A253187 n > 0 := h.1
  have h_C : ∀ k m, (k, m) ∈ C_pairs →
    ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
      (P_k_first k x) + (P_k_second k y) + (polygonal_num_val m z).toNat = n := h.2
  
  have h_C_in : (5, 7) ∈ C_pairs := by simp [C_pairs]
  have h_5_7 := h_C 5 7 h_C_in
  
  have h_5_7_11 := h_5_7 11
  sorry
