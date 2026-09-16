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
  
  have h_C_in : (5, 13) ∈ C_pairs := by simp [C_pairs]
  have h_5_13 := h_C 5 13 h_C_in
  
  have h_5_13_4 := h_5_13 4
  sorry
