import Submission.Spec
open Finset

lemma a000224_if (n : ℕ) (hn : n.Prime) (hodd : n ≠ 2) :
  (n * n) ≡ 1 [MOD A000224 n * (A000224 n - 1)] := by
  have H := A000224_prime_A000224 n hn hodd
  rw [H]
  obtain ⟨k, rfl⟩ := hn.odd_of_ne_two hodd
  have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h2 : (2 * k + 1 - 1) / 2 = k := by omega
  rw [h1, h2]
  have h3 : (2 * k + 1) * (2 * k + 1) = 4 * (k + 1) * k + 1 := by ring
  rw [h3]
  exact Nat.ModEq.add_right_cancel' 0 (by omega)
