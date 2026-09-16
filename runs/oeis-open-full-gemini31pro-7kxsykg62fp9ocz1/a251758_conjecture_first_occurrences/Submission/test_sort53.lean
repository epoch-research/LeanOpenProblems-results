import Submission.test_sort52
open List

lemma mem_list_divs_loop (n d fuel : ℕ) (low high : List ℕ) (x : ℕ)
  (h_fuel : fuel ≥ n - d + 1) (hd : d > 0) :
  x ∈ list_divs_loop n d fuel low high ↔
  x ∈ low ∨ x ∈ high ∨ (x ≥ d ∧ x ≤ n / d ∧ n % x == 0) := by
  sorry
