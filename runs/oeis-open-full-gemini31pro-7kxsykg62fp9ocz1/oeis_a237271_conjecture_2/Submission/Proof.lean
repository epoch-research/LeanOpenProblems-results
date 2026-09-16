import Submission.Spec
open Nat Finset List

theorem eq_of_adj_divisors {n d_k d_k_succ : ℕ} 
  (h_adj : (d_k, d_k_succ) ∈ List.zip (sorted_divisors_list n) (sorted_divisors_list n).tail) :
  d_k_succ > 2 * d_k ↔ Odd d_k_succ ∧ d_k_succ ≥ 2 * d_k := by
  sorry
