import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 3000000
set_option maxRecDepth 10000

theorem not_prime_of_zmod_pow_ne_one {M a : ℕ} (hp : M.Prime) (ha : (a : ZMod M) ≠ 0)
    (h : (a : ZMod M) ^ (M - 1) ≠ 1) : False := by
  haveI : Fact M.Prime := ⟨hp⟩
  have h_fermat := ZMod.pow_card_sub_one_eq_one ha
  exact h h_fermat

theorem test_n13_composite : ¬ Nat.Prime (10 ^ (2 ^ 13) + 1) := by
  intro hp
  have ha : (3 : ZMod (10 ^ (2 ^ 13) + 1)) ≠ 0 := by
    decide
  have h_fermat : (3 : ZMod (10 ^ (2 ^ 13) + 1)) ^ (10 ^ (2 ^ 13)) ≠ 1 := by
    reduce_mod_char
    decide
  exact not_prime_of_zmod_pow_ne_one hp ha h_fermat

theorem test_n14_composite : ¬ Nat.Prime (10 ^ (2 ^ 14) + 1) := by
  intro hp
  have ha : (3 : ZMod (10 ^ (2 ^ 14) + 1)) ≠ 0 := by
    decide
  have h_fermat : (3 : ZMod (10 ^ (2 ^ 14) + 1)) ^ (10 ^ (2 ^ 14)) ≠ 1 := by
    reduce_mod_char
    decide
  exact not_prime_of_zmod_pow_ne_one hp ha h_fermat

theorem test_n15_dvd : 65537 ∣ 10 ^ (2 ^ 15) + 1 := by
  have h : ((10 ^ (2 ^ 15) + 1 : ℕ) : ZMod 65537) = 0 := by
    push_cast
    reduce_mod_char
  rwa [CharP.cast_eq_zero_iff (ZMod 65537) 65537] at h

theorem test_n10_dvd : 1856104284667693057 ∣ 10 ^ (2 ^ 10) + 1 := by
  have h : ((10 ^ (2 ^ 10) + 1 : ℕ) : ZMod 1856104284667693057) = 0 := by
    push_cast
    reduce_mod_char
  rwa [CharP.cast_eq_zero_iff (ZMod 1856104284667693057) 1856104284667693057] at h










theorem test_n21_composite : ¬ Nat.Prime (10 ^ (2 ^ 21) + 1) := by
  intro hp
  have ha : (3 : ZMod (10 ^ (2 ^ 21) + 1)) ≠ 0 := by
    decide
  have h_fermat : (3 : ZMod (10 ^ (2 ^ 21) + 1)) ^ (10 ^ (2 ^ 21)) ≠ 1 := by
    reduce_mod_char
    decide
  exact not_prime_of_zmod_pow_ne_one hp ha h_fermat
