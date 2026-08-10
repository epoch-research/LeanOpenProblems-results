import FormalConjectures.Util.ProblemImports
example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) : ((p : ℤ) ^ (3*r)) ≠ 0 := by
  exact pow_ne_zero _ (Int.natCast_ne_zero.mpr hp.ne_zero)
example (p r : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p) (hr : 0 < r) : ((p : ℤ) ^ (3*r)) ≠ 1 := by
  have hpz : (1:ℤ) < p := by exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 5) hp5)
  have hpos : 0 < 3*r := by omega
  have hgt : (1:ℤ) < (p:ℤ)^(3*r) := one_lt_pow₀ hpz hpos.ne'
  omega
