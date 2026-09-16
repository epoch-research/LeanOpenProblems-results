import Submission.Spec
open Nat Finset

theorem disproof_check : ¬ (
  (∀ n : ℕ, A253187 n > 0) ∧
  ∀ k m, (k, m) ∈ C_pairs →
    ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
      (P_k_first k x) + (P_k_second k y) + (polygonal_num_val m z).toNat = n
) := by
  intro h
  have h_C : ∀ k m, (k, m) ∈ C_pairs →
    ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
      (P_k_first k x) + (P_k_second k y) + (polygonal_num_val m z).toNat = n := h.2
  have h_in : (6, 5) ∈ C_pairs := by simp [C_pairs]
  have h_val := h_C 6 5 h_in 100
  sorry
