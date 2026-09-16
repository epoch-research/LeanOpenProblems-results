import Submission.Lemmas
import Mathlib

lemma d_val2 (n : ℕ) (hn : 2 ≤ n) : d n =
  if n % 2 = 0 then
    Nat.gcd n (C (n - 1) - 1)
  else
    Nat.gcd (n - 2) (C (n - 1) + 1) := by
  have : n = n - 1 + 1 := by omega
  nth_rw 1 [this]
  rw [d_val (by omega)]
  have h1 : (n - 1 + 1) % 2 = n % 2 := by omega
  have h2 : n - 1 - 1 = n - 2 := by omega
  have h3 : n - 1 + 1 = n := by omega
  sorry

lemma C_even (n : ℕ) (hn : 2 ≤ n) : C n % 2 = 0 := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    have h1 : C (k + 1) = C k + d (k + 1) - 1 := by
      have : C (k + 1) + (k + 1) = a (k + 1) := by rw [a_eq_C_add_n]
      have : C k + k = a k := by rw [a_eq_C_add_n]
      have : d (k + 1) = a (k + 1) - a k := rfl
      have : C k ≤ C (k + 1) := C_mono (by omega)
      omega
    rw [h1]
    sorry
