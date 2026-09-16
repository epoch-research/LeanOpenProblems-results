import Mathlib

def countPrimes : ℕ → ℕ
| 0 => 0
| n + 1 => countPrimes n + if Nat.Prime n then 1 else 0

lemma cp_3 : countPrimes 3 = 1 := by
  change countPrimes 2 + if Nat.Prime 2 then 1 else 0 = 1
  have h2 : Nat.Prime 2 := by norm_num
  simp [h2, countPrimes]
