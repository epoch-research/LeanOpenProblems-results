import FormalConjectures.Util.ProblemImports
open Nat List Finset

def is_binary_palindrome (k : ℕ) : Bool :=
  (Nat.digits 2 k).reverse == Nat.digits 2 k

#check Nat.digits_ofDigits
#check Nat.ofDigits_replicate_zero
#check Nat.ofDigits_append
#check Nat.ofDigits_eq_foldr
#check List.reverse_replicate
#check Nat.ofDigits_digits

lemma ofDigits_replicate_one_two (m : Nat) : Nat.ofDigits 2 (List.replicate m 1) = 2^m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.replicate_succ]
      simp [Nat.ofDigits, ih]
      have hp : 0 < 2 ^ m := pow_pos (by norm_num : (0:Nat) < 2) m
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, Nat.mul_comm]
      rw [hpow]
      omega

lemma digits_repunits (m : Nat) : Nat.digits 2 (2^m - 1) = List.replicate m 1 := by
  cases m with
  | zero => simp
  | succ m =>
      have hval : Nat.ofDigits 2 (List.replicate (m+1) 1) = 2^(m+1) - 1 := by simpa using ofDigits_replicate_one_two (m+1)
      rw [← hval]
      apply Nat.digits_ofDigits
      · norm_num
      · intro l hl
        simp at hl
        omega
      · simp

example (m : Nat) : is_binary_palindrome (2^m - 1) := by
  rw [is_binary_palindrome, digits_repunits]
  simp
