import Mathlib
import Submission.Spec
import Submission.Proof6

open Nat

lemma digits_two_pow_sub_one (m : ℕ) : (Nat.digits 2 (2 ^ m - 1)).sum = m := by
  induction m with
  | zero =>
    have : 2 ^ 0 - 1 = 0 := rfl
    rw [this, Nat.digits_zero, List.sum_nil]
  | succ m ih =>
    have h1 : 2 ^ (m + 1) - 1 = 1 + 2 * (2 ^ m - 1) := by
      have : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      have hpos : 2 ^ m ≥ 1 := by
        have hd : 2 ≥ 1 := by omega
        exact Nat.one_le_pow m 2 hd
      omega
    rw [h1]
    have h_digits : Nat.digits 2 (1 + 2 * (2 ^ m - 1)) = 1 :: Nat.digits 2 (2 ^ m - 1) := by
      exact Nat.digits_add 2 (by decide) 1 (2 ^ m - 1) (by decide) (Or.inl (by decide))
    rw [h_digits, List.sum_cons, ih]
    omega
