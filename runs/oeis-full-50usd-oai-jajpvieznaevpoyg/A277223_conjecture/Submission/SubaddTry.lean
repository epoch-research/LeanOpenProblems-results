import FormalConjectures.Util.ProblemImports

open Nat Set

private def sum_digits_10 (m : ℕ) : ℕ := (Nat.digits 10 m).sum

-- Attempt lemma: sum digits of twice a number is at most twice sum digits.
lemma sum_digits_double_le (m : ℕ) : sum_digits_10 (2*m) ≤ 2 * sum_digits_10 m := by
  -- Maybe follows from Kummer theorem for p=2? no decimal.
  sorry

lemma fixed_mul_two_of_small {m a : ℕ} (ha : a < 5) (hm : a = sum_digits_10 m)
    (hmod : (2*a) % 9 = sum_digits_10 (2*m) % 9) :
    2*a = sum_digits_10 (2*m) := by
  have hle : sum_digits_10 (2*m) ≤ 2*a := by
    calc sum_digits_10 (2*m) ≤ 2*sum_digits_10 m := sum_digits_double_le m
      _ = 2*a := by rw [← hm]
  have h2a : 2*a < 9 := by omega
  have hsmod : sum_digits_10 (2*m) % 9 = (2*a) % 9 := hmod.symm
  have hslt : sum_digits_10 (2*m) < 9 := lt_of_le_of_lt hle h2a
  have hmodself : sum_digits_10 (2*m) % 9 = sum_digits_10 (2*m) := Nat.mod_eq_of_lt hslt
  have hmoda : (2*a) % 9 = 2*a := Nat.mod_eq_of_lt h2a
  omega
