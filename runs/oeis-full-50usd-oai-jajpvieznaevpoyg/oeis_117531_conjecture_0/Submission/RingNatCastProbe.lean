import FormalConjectures.Util.ProblemImports

example (p q k : ℕ) (hp : 0 < p) (hk : 1 ≤ k) (hq : q = 2*k - 1) :
    4 * (k^2 - k + p) = q*q + (4*p - 1) := by
  apply Nat.cast_injective (R := ℤ)
  have hkz : ((k^2 - k : ℕ) : ℤ) = (k:ℤ)^2 - (k:ℤ) := by
    norm_num [Nat.cast_sub (by nlinarith [hk])]
  have hpz : ((4*p - 1 : ℕ) : ℤ) = 4*(p:ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 4*p)]
    norm_num
  push_cast
  rw [hkz, hpz]
  have hqz : (q:ℤ) = 2*(k:ℤ)-1 := by omega
  rw [hqz]
  ring
