import Submission.Lemmas6
import Mathlib

lemma d_val2 (n : ℕ) (hn : 2 ≤ n) : d n =
  if n % 2 = 0 then
    Nat.gcd n (C (n - 1) - 1)
  else
    Nat.gcd (n - 2) (C (n - 1) + 1) := by
  have : n = n - 1 + 1 := by omega
  nth_rw 1 [this]
  rw [d_val (by omega)]
  have h1 : (n - 1 + 1) % 2 = 0 ↔ n % 2 = 0 := by omega
  have h2 : n - 1 - 1 = n - 2 := by omega
  have h3 : n - 1 + 1 = n := by omega
  split_ifs with h_even h_even2 h_even3
  · rw [h3]
  · tauto
  · tauto
  · rw [h2]
