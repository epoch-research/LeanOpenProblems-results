import Mathlib
open Nat Finset

lemma S_prime_pow_ge {p k : ℕ} (hk : 0 < k) :
  (k + 1 : ℚ) + (k : ℚ) / (p : ℚ) ≤ ∑ j ∈ range (k + 1), ((j + 1 : ℕ) : ℚ) / (p ^ (k - j) : ℚ) := by
  have h_split : ∑ j ∈ range (k + 1), ((j + 1 : ℕ) : ℚ) / (p ^ (k - j) : ℚ) =
    (∑ j ∈ range (k - 1), ((j + 1 : ℕ) : ℚ) / (p ^ (k - j) : ℚ)) +
    (((k - 1 + 1 : ℕ) : ℚ) / (p ^ (k - (k - 1)) : ℚ)) +
    (((k + 1 : ℕ) : ℚ) / (p ^ (k - k) : ℚ)) := by
    sorry
  sorry
