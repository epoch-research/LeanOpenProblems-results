import Mathlib

lemma neg_one_pow_mod (a b : ℕ) (h : a % 2 = b % 2) : (-1 : ℤ)^a = (-1 : ℤ)^b := by
  have H1 : a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
  have H2 : b = 2 * (b / 2) + b % 2 := (Nat.div_add_mod b 2).symm
  nth_rw 1 [H1]
  nth_rw 1 [H2]
  rw [h]
  have H_pow (x r : ℕ) : (-1 : ℤ)^(2 * x + r) = (-1 : ℤ)^r := by
    rw [pow_add, pow_mul]
    have : (-1 : ℤ)^2 = 1 := by norm_num
    rw [this, one_pow, one_mul]
  rw [H_pow, H_pow]
