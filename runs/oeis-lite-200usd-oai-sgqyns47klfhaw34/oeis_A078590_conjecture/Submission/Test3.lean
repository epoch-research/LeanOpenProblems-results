import FormalConjectures.Util.ProblemImports

example (n : ℕ) (h : n % 18 = 3) : (2 ^ n) % 19 = 8 := by
  rw [show n = 18 * (n / 18) + n % 18 by omega, h]
  rw [pow_add, pow_mul]
  have hbase : (2 ^ 18) % 19 = 1 := by norm_num
  -- need mod pow
  have : ((2 ^ 18) ^ (n / 18) * 2 ^ 3) % 19 = ((1 : ℕ) ^ (n / 18) * 8) % 19 := by
    apply Nat.ModEq.eq_of_lt
    sorry
  sorry
