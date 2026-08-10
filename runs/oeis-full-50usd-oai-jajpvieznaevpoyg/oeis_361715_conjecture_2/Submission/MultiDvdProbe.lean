import FormalConjectures.Util.ProblemImports
open Nat Finset

#check Choose.lucas_theorem
#check Choose.choose_modEq_choose_mod_mul_choose_div
#check Nat.Prime.dvd_choose
#check Nat.Prime.dvd_choose_add
#check Nat.dvd_iff_mod_eq_zero

example (p r k : ℕ) [Fact (Nat.Prime p)] (hk0 : k ≠ 0) (hklt : k < p ^ r) :
    p ∣ (p ^ r).multichoose k := by
  rw [Nat.multichoose_eq]
  -- target p ∣ (p^r + k - 1).choose k
  -- maybe Lucas theorem can show choose ≡ 0 mod p
  have hmod : ((p ^ r + k - 1).choose k : ℤ) ≡ 0 [ZMOD (p : ℕ)] := by
    sorry
  exact Int.natCast_dvd_natCast.mp (Int.modEq_zero_iff_dvd.mp hmod)
