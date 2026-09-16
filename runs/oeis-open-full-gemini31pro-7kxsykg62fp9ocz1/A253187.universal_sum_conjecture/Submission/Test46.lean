import Submission.Spec
open Nat Finset

theorem proof :
  (∀ n : ℕ, A253187 n > 0) ∧
  ∀ k m, (k, m) ∈ C_pairs →
    ∀ n : ℕ, ∃ x y : ℕ, ∃ z : ℤ,
      (P_k_first k x) + (P_k_second k y) + (polygonal_num_val m z).toNat = n := by
  sorry
