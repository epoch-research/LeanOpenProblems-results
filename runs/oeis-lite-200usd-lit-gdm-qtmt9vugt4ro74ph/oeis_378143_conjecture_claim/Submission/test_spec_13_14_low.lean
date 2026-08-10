import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 200000
set_option maxRecDepth 200000

open Nat Set

theorem not_prime_of_zmod_pow_ne_one {M a : ℕ} (hp : M.Prime) (ha : (a : ZMod M) ≠ 0)
    (h : (a : ZMod M) ^ (M - 1) ≠ 1) : False := by
  haveI : Fact M.Prime := ⟨hp⟩
  have h_fermat := ZMod.pow_card_sub_one_eq_one ha
  exact h h_fermat

theorem case_13_14 :
  (Nat.Prime (10 ^ (2 ^ 13) + 1) → False) ∧ (Nat.Prime (10 ^ (2 ^ 14) + 1) → False) := by
  constructor
  · intro hp
    have ha : (3 : ZMod (10 ^ (2 ^ 13) + 1)) ≠ 0 := by
      intro h
      have h_cast : ((3 : ℕ) : ZMod (10 ^ (2 ^ 13) + 1)) = 0 := h
      have h_dvd : (10 ^ (2 ^ 13) + 1) ∣ 3 := by
        rwa [CharP.cast_eq_zero_iff (ZMod (10 ^ (2 ^ 13) + 1)) (10 ^ (2 ^ 13) + 1)] at h_cast
      have h_le := Nat.le_of_dvd (by decide) h_dvd
      have h_gt : 3 < 10 ^ (2 ^ 13) + 1 := by
        have h1 : 3 < 10 ^ 1 + 1 := by decide
        apply lt_of_lt_of_le h1
        apply Nat.add_le_add_right
        apply Nat.pow_le_pow_right (by decide)
        apply Nat.one_le_pow _ _ (by decide)
      omega
    have h_fermat : (3 : ZMod (10 ^ (2 ^ 13) + 1)) ^ (10 ^ (2 ^ 13)) ≠ 1 := by
      reduce_mod_char
      decide
    exact not_prime_of_zmod_pow_ne_one hp ha h_fermat
  · intro hp
    have ha : (3 : ZMod (10 ^ (2 ^ 14) + 1)) ≠ 0 := by
      intro h
      have h_cast : ((3 : ℕ) : ZMod (10 ^ (2 ^ 14) + 1)) = 0 := h
      have h_dvd : (10 ^ (2 ^ 14) + 1) ∣ 3 := by
        rwa [CharP.cast_eq_zero_iff (ZMod (10 ^ (2 ^ 14) + 1)) (10 ^ (2 ^ 14) + 1)] at h_cast
      have h_le := Nat.le_of_dvd (by decide) h_dvd
      have h_gt : 3 < 10 ^ (2 ^ 14) + 1 := by
        have h1 : 3 < 10 ^ 1 + 1 := by decide
        apply lt_of_lt_of_le h1
        apply Nat.add_le_add_right
        apply Nat.pow_le_pow_right (by decide)
        apply Nat.one_le_pow _ _ (by decide)
      omega
    have h_fermat : (3 : ZMod (10 ^ (2 ^ 14) + 1)) ^ (10 ^ (2 ^ 14)) ≠ 1 := by
      reduce_mod_char
      decide
    exact not_prime_of_zmod_pow_ne_one hp ha h_fermat
