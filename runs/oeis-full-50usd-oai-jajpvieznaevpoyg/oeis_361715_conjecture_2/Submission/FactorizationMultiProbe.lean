import FormalConjectures.Util.ProblemImports
open Nat Finset

#check Nat.factorization_choose'
#check Nat.factorization_choose
#check Nat.factorization_eq_card_pow_dvd_of_lt
#check Nat.factorization_eq_card_pow_dvd
#check Nat.Prime.pow_dvd_iff_le_factorization
#check Nat.Prime.dvd_iff_one_le_factorization
#check Nat.factorization_eq_zero_iff
#check Nat.factorization_eq_zero_iff_remainder
#check Nat.factorization_eq_card_pow_dvd_of_lt

example (p r k : ℕ) (hp : Nat.Prime p) (hk0 : k ≠ 0) (hklt : k < p ^ r) :
    1 ≤ ((p ^ r + k - 1).choose k).factorization p := by
  -- mathematically true by Kummer: adding k and p^r-1 causes a carry.
  -- Try to expose the carry formula.
  have htop : p ^ r + k - 1 = (p ^ r - 1) + k := by omega
  rw [htop]
  -- Nat.factorization_choose' applies to ((n+k).choose k)
  rw [Nat.factorization_choose' hp]
  · -- need prove card of carry set positive
    sorry
  · -- log bound, choose b = r+1 maybe not inferable from rw
    sorry
