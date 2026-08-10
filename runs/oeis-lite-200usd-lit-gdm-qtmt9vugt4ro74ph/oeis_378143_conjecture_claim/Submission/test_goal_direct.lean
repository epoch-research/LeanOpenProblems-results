import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.FieldTheory.Finite.Basic

set_option exponentiation.threshold 30000
set_option maxRecDepth 15000

open Nat Set

theorem not_prime_of_zmod_pow_ne_one {M a : ℕ} (hp : M.Prime) (ha : (a : ZMod M) ≠ 0)
    (h : (a : ZMod M) ^ (M - 1) ≠ 1) : False := by
  haveI : Fact M.Prime := ⟨hp⟩
  have h_fermat := ZMod.pow_card_sub_one_eq_one ha
  exact h h_fermat

abbrev exp16 : ℕ := 65536
abbrev exp17 : ℕ := 131072
abbrev exp18 : ℕ := 262144
abbrev exp19 : ℕ := 524288
abbrev exp20 : ℕ := 1048576

theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  intro n
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
  · intro _
    left
    decide
  · intro _
    left
    decide
  · intro h
    exfalso
    apply Nat.not_prime_of_dvd_of_ne (m := 73) at h
    · exact h
    · decide
    · decide
    · decide
  · intro h
    exfalso
    apply Nat.not_prime_of_dvd_of_ne (m := 17) at h
    · exact h
    · decide
    · decide
    · decide
  · intro h
    exfalso
    have hdvd : 353 ∣ 10 ^ (2 ^ 4) + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      have : (10 : ZMod 353) ^ (2 ^ 4) + 1 = 0 := by
        reduce_mod_char
      exact_mod_cast this
    have h_lt : 353 < 10 ^ (2 ^ 4) + 1 := by decide
    apply Nat.not_prime_of_dvd_of_ne (m := 353) at h
    · exact h
    · exact hdvd
    · decide
    · exact Nat.ne_of_lt h_lt
  · intro h
    exfalso
    have hdvd : 19841 ∣ 10 ^ (2 ^ 5) + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      have : (10 : ZMod 19841) ^ (2 ^ 5) + 1 = 0 := by
        reduce_mod_char
      exact_mod_cast this
    have h_lt : 19841 < 10 ^ (2 ^ 5) + 1 := by decide
    apply Nat.not_prime_of_dvd_of_ne (m := 19841) at h
    · exact h
    · exact hdvd
    · decide
    · exact Nat.ne_of_lt h_lt
  · intro h
    exfalso
    have hdvd : 1265011073 ∣ 10 ^ (2 ^ 6) + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      have : (10 : ZMod 1265011073) ^ (2 ^ 6) + 1 = 0 := by
        reduce_mod_char
      exact_mod_cast this
    have h_lt : 1265011073 < 10 ^ (2 ^ 6) + 1 := by
      have h1 : 1265011073 < 10 ^ 10 + 1 := by decide
      apply lt_of_lt_of_le h1
      apply Nat.add_le_add_right
      apply Nat.pow_le_pow_right (by decide)
      show 10 ≤ 2 ^ 6
      decide
    apply Nat.not_prime_of_dvd_of_ne (m := 1265011073) at h
    · exact h
    · exact hdvd
    · decide
    · exact Nat.ne_of_lt h_lt
  · intro h
    exfalso
    have hdvd : 257 ∣ 10 ^ (2 ^ 7) + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      have : (10 : ZMod 257) ^ (2 ^ 7) + 1 = 0 := by
        reduce_mod_char
      exact_mod_cast this
    have h_lt : 257 < 10 ^ (2 ^ 7) + 1 := by
      have h1 : 257 < 10 ^ 3 + 1 := by decide
      apply lt_of_lt_of_le h1
      apply Nat.add_le_add_right
      apply Nat.pow_le_pow_right (by decide)
      show 3 ≤ 2 ^ 7
      decide
    apply Nat.not_prime_of_dvd_of_ne (m := 257) at h
    · exact h
    · exact hdvd
    · decide
    · exact Nat.ne_of_lt h_lt
  · intro h
    exfalso
    have hdvd : 10753 ∣ 10 ^ (2 ^ 8) + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      have : (10 : ZMod 10753) ^ (2 ^ 8) + 1 = 0 := by
        reduce_mod_char
      exact_mod_cast this
    have h_lt : 10753 < 10 ^ (2 ^ 8) + 1 := by
      have h1 : 10753 < 10 ^ 5 + 1 := by decide
      apply lt_of_lt_of_le h1
      apply Nat.add_le_add_right
      apply Nat.pow_le_pow_right (by decide)
      show 5 ≤ 2 ^ 8
      decide
    apply Nat.not_prime_of_dvd_of_ne (m := 10753) at h
    · exact h
    · exact hdvd
    · decide
    · exact Nat.ne_of_lt h_lt
  · intro h
    exfalso
    have hdvd : 1514497 ∣ 10 ^ (2 ^ 9) + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      have : (10 : ZMod 1514497) ^ (2 ^ 9) + 1 = 0 := by
        reduce_mod_char
      exact_mod_cast this
    have h_lt : 1514497 < 10 ^ (2 ^ 9) + 1 := by
      have h1 : 1514497 < 10 ^ 7 + 1 := by decide
      apply lt_of_lt_of_le h1
      apply Nat.add_le_add_right
      apply Nat.pow_le_pow_right (by decide)
      show 7 ≤ 2 ^ 9
      decide
    apply Nat.not_prime_of_dvd_of_ne (m := 1514497) at h
    · exact h
    · exact hdvd
    · decide
    · exact Nat.ne_of_lt h_lt
  · intro h
    exfalso
    have hdvd : 1856104284667693057 ∣ 10 ^ (2 ^ 10) + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      have : (10 : ZMod 1856104284667693057) ^ (2 ^ 10) + 1 = 0 := by
        reduce_mod_char
      exact_mod_cast this
    have h_lt : 1856104284667693057 < 10 ^ (2 ^ 10) + 1 := by
      have h1 : 1856104284667693057 < 10 ^ 19 + 1 := by decide
      apply lt_of_lt_of_le h1
      apply Nat.add_le_add_right
      apply Nat.pow_le_pow_right (by decide)
      show 19 ≤ 2 ^ 10
      decide
    apply Nat.not_prime_of_dvd_of_ne (m := 1856104284667693057) at h
    · exact h
    · exact hdvd
    · decide
    · exact Nat.ne_of_lt h_lt
  · intro h
    exfalso
    have hdvd : 106907803649 ∣ 10 ^ (2 ^ 11) + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      have : (10 : ZMod 106907803649) ^ (2 ^ 11) + 1 = 0 := by
        reduce_mod_char
      exact_mod_cast this
    have h_lt : 106907803649 < 10 ^ (2 ^ 11) + 1 := by
      have h1 : 106907803649 < 10 ^ 12 + 1 := by decide
      apply lt_of_lt_of_le h1
      apply Nat.add_le_add_right
      apply Nat.pow_le_pow_right (by decide)
      show 12 ≤ 2 ^ 11
      decide
    apply Nat.not_prime_of_dvd_of_ne (m := 106907803649) at h
    · exact h
    · exact hdvd
    · decide
    · exact Nat.ne_of_lt h_lt
  · intro h
    exfalso
    have hdvd : 458924033 ∣ 10 ^ (2 ^ 12) + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      have : (10 : ZMod 458924033) ^ (2 ^ 12) + 1 = 0 := by
        reduce_mod_char
      exact_mod_cast this
    have h_lt : 458924033 < 10 ^ (2 ^ 12) + 1 := by
      have h1 : 458924033 < 10 ^ 9 + 1 := by decide
      apply lt_of_lt_of_le h1
      apply Nat.add_le_add_right
      apply Nat.pow_le_pow_right (by decide)
      show 9 ≤ 2 ^ 12
      decide
    apply Nat.not_prime_of_dvd_of_ne (m := 458924033) at h
    · exact h
    · exact hdvd
    · decide
    · exact Nat.ne_of_lt h_lt
  · intro hp
    exfalso
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
      sorry
    exact not_prime_of_zmod_pow_ne_one hp ha h_fermat
  · intro hp
    exfalso
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
      sorry
    exact not_prime_of_zmod_pow_ne_one hp ha h_fermat
  · intro h
    exfalso
    apply Nat.not_prime_of_dvd_of_ne (m := 65537) at h
    · exact h
    · decide
    · decide
    · decide
  · intro h
    change (10 ^ exp16 + 1).Prime at h
    exfalso
    have hdvd : 8257537 ∣ 10 ^ exp16 + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      decide
    apply Nat.not_prime_of_dvd_of_ne (m := 8257537) at h
    · exact h
    · exact hdvd
    · decide
    · decide
  · intro h
    change (10 ^ exp17 + 1).Prime at h
    exfalso
    have hdvd : 175636481 ∣ 10 ^ exp17 + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      decide
    apply Nat.not_prime_of_dvd_of_ne (m := 175636481) at h
    · exact h
    · exact hdvd
    · decide
    · decide
  · intro h
    change (10 ^ exp18 + 1).Prime at h
    exfalso
    have hdvd : 639631361 ∣ 10 ^ exp18 + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      decide
    apply Nat.not_prime_of_dvd_of_ne (m := 639631361) at h
    · exact h
    · exact hdvd
    · decide
    · decide
  · intro h
    change (10 ^ exp19 + 1).Prime at h
    exfalso
    have hdvd : 70254593 ∣ 10 ^ exp19 + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      decide
    apply Nat.not_prime_of_dvd_of_ne (m := 70254593) at h
    · exact h
    · exact hdvd
    · decide
    · decide
  · intro h
    change (10 ^ exp20 + 1).Prime at h
    exfalso
    have hdvd : 167772161 ∣ 10 ^ exp20 + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      decide
    apply Nat.not_prime_of_dvd_of_ne (m := 167772161) at h
    · exact h
    · exact hdvd
    · decide
    · decide
  · sorry
