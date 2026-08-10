import FormalConjectures.Util.ProblemImports
#check Nat.lt_two_pow_self
#check Nat.one_lt_pow
#check Nat.pow_lt_pow_of_lt_left
#check Nat.pow_le_pow_left

lemma lt_pow_self_of_two_le {p r : ℕ} (hp : 2 ≤ p) (hr : 0 < r) : r < p ^ r := by
  have h2 : r < 2 ^ r := Nat.lt_two_pow_self
  have hle : 2 ^ r ≤ p ^ r := Nat.pow_le_pow_left hp r
  exact lt_of_lt_of_le h2 hle

example {p r : ℕ} (h5 : 5 ≤ p) (hr : 0 < r) : r ≠ p ^ r := by
  exact ne_of_lt (lt_pow_self_of_two_le (by omega) hr)
