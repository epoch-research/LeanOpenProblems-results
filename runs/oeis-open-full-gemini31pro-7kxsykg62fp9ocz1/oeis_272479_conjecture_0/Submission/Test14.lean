import Mathlib

open Nat

lemma sum_le_ofDigits (L : List ℕ) : L.sum ≤ ofDigits 10 L := by
  induction L with
  | nil => simp
  | cons hd tl ih =>
    dsimp [ofDigits]
    calc hd + tl.sum ≤ hd + ofDigits 10 tl := Nat.add_le_add_left ih hd
      _ ≤ hd + 10 * ofDigits 10 tl := by
        apply Nat.add_le_add_left
        calc ofDigits 10 tl = 1 * ofDigits 10 tl := by ring
          _ ≤ 10 * ofDigits 10 tl := Nat.mul_le_mul_right _ (by decide)

lemma digits_sum_le_n (n : ℕ) : (digits 10 n).sum ≤ n := by
  calc (digits 10 n).sum ≤ ofDigits 10 (digits 10 n) := sum_le_ofDigits _
    _ = n := ofDigits_digits 10 n
