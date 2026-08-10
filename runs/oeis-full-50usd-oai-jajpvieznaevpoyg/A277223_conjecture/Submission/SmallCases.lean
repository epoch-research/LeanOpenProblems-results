import FormalConjectures.Util.ProblemImports

open Nat Set

private def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum

lemma zmod9 (m : ℕ) : m % 9 = sum_digits_10 m % 9 := by
  simpa [sum_digits_10, Nat.ModEq, Nat.modEq_iff_dvd'] using (Nat.modEq_nine_digits_sum m).symm

#check Nat.modEq_nine_digits_sum
#check Nat.ModEq
#check Nat.ModEq.symm
#check Nat.ModEq.trans
#check Nat.ModEq.mul
#check Nat.ModEq.add
#check Nat.ModEq.of_dvd

-- Try proving if a valid then c*a product digit sum bounded by c*a (submultiplicativity placeholder)
#check Nat.digit_sum_le
#check Nat.sum_le_ofDigits
#check Nat.mul_ofDigits
#check Nat.digits_ofDigits
