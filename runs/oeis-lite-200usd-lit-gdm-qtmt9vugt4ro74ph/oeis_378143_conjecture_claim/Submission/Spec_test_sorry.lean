import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 30000
set_option maxRecDepth 100000

open Nat Set

noncomputable def A378143 (n : ℕ) : ℕ :=
  sInf { k : ℕ | Nat.Prime k ∧ ∃ p : ℕ, Nat.Prime p ∧ k = (2 * p) ^ (2 ^ n) + 1 }

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

lemma case_0 : Nat.Prime (10 ^ (2 ^ 0) + 1) → Nat.Prime (4 ^ (2 ^ 0) + 1) ∨ Nat.Prime (6 ^ (2 ^ 0) + 1) := by
  intro _
  left
  change Nat.Prime 5
  decide

lemma case_1 : Nat.Prime (10 ^ (2 ^ 1) + 1) → Nat.Prime (4 ^ (2 ^ 1) + 1) ∨ Nat.Prime (6 ^ (2 ^ 1) + 1) := by
  intro _
  left
  change Nat.Prime 17
  decide

lemma case_2 : Nat.Prime (10 ^ (2 ^ 2) + 1) → Nat.Prime (4 ^ (2 ^ 2) + 1) ∨ Nat.Prime (6 ^ (2 ^ 2) + 1) := by
  intro _
  left
  change Nat.Prime 257
  decide

lemma case_3 : Nat.Prime (10 ^ (2 ^ 3) + 1) → Nat.Prime (4 ^ (2 ^ 3) + 1) ∨ Nat.Prime (6 ^ (2 ^ 3) + 1) := by
  intro _
  left
  change Nat.Prime 65537
  decide

lemma case_4 : Nat.Prime (10 ^ (2 ^ 4) + 1) → Nat.Prime (4 ^ (2 ^ 4) + 1) ∨ Nat.Prime (6 ^ (2 ^ 4) + 1) := by
  intro h
  exfalso
  apply Nat.not_prime_of_dvd_of_ne (m := 353) at h
  · exact h
  · decide
  · decide
  · decide

lemma case_5 : Nat.Prime (10 ^ (2 ^ 5) + 1) → Nat.Prime (4 ^ (2 ^ 5) + 1) ∨ Nat.Prime (6 ^ (2 ^ 5) + 1) := by
  intro h
  exfalso
  apply Nat.not_prime_of_dvd_of_ne (m := 19841) at h
  · exact h
  · decide
  · decide
  · decide

lemma case_6 : Nat.Prime (10 ^ (2 ^ 6) + 1) → Nat.Prime (4 ^ (2 ^ 6) + 1) ∨ Nat.Prime (6 ^ (2 ^ 6) + 1) := by
  intro h
  exfalso
  apply Nat.not_prime_of_dvd_of_ne (m := 1265011073) at h
  · exact h
  · decide
  · decide
  · decide

lemma case_7 : Nat.Prime (10 ^ (2 ^ 7) + 1) → Nat.Prime (4 ^ (2 ^ 7) + 1) ∨ Nat.Prime (6 ^ (2 ^ 7) + 1) := by
  intro h
  exfalso
  apply Nat.not_prime_of_dvd_of_ne (m := 257) at h
  · exact h
  · decide
  · decide
  · decide

lemma case_8 : Nat.Prime (10 ^ (2 ^ 8) + 1) → Nat.Prime (4 ^ (2 ^ 8) + 1) ∨ Nat.Prime (6 ^ (2 ^ 8) + 1) := by
  intro h
  exfalso
  apply Nat.not_prime_of_dvd_of_ne (m := 10753) at h
  · exact h
  · decide
  · decide
  · decide

lemma case_9 : Nat.Prime (10 ^ (2 ^ 9) + 1) → Nat.Prime (4 ^ (2 ^ 9) + 1) ∨ Nat.Prime (6 ^ (2 ^ 9) + 1) := by
  intro h
  exfalso
  apply Nat.not_prime_of_dvd_of_ne (m := 1514497) at h
  · exact h
  · decide
  · decide
  · decide

lemma case_10 : Nat.Prime (10 ^ (2 ^ 10) + 1) → Nat.Prime (4 ^ (2 ^ 10) + 1) ∨ Nat.Prime (6 ^ (2 ^ 10) + 1) := by
  intro h
  exfalso
  apply Nat.not_prime_of_dvd_of_ne (m := 1856104284667693057) at h
  · exact h
  · decide
  · decide
  · decide

lemma case_11 : Nat.Prime (10 ^ (2 ^ 11) + 1) → Nat.Prime (4 ^ (2 ^ 11) + 1) ∨ Nat.Prime (6 ^ (2 ^ 11) + 1) := by
  intro h
  exfalso
  apply Nat.not_prime_of_dvd_of_ne (m := 106907803649) at h
  · exact h
  · decide
  · decide
  · decide

lemma case_12 : Nat.Prime (10 ^ (2 ^ 12) + 1) → Nat.Prime (4 ^ (2 ^ 12) + 1) ∨ Nat.Prime (6 ^ (2 ^ 12) + 1) := by
  intro h
  exfalso
  apply Nat.not_prime_of_dvd_of_ne (m := 458924033) at h
  · exact h
  · decide
  · decide
  · decide

lemma case_13 : Nat.Prime (10 ^ (2 ^ 13) + 1) → Nat.Prime (4 ^ (2 ^ 13) + 1) ∨ Nat.Prime (6 ^ (2 ^ 13) + 1) := by
  intro hp
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
    sorry -- reduce_mod_char
    decide
  exact not_prime_of_zmod_pow_ne_one hp ha h_fermat

lemma case_14 : Nat.Prime (10 ^ (2 ^ 14) + 1) → Nat.Prime (4 ^ (2 ^ 14) + 1) ∨ Nat.Prime (6 ^ (2 ^ 14) + 1) := by
  intro hp
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
    sorry -- reduce_mod_char
    decide
  exact not_prime_of_zmod_pow_ne_one hp ha h_fermat

lemma case_15 : Nat.Prime (10 ^ (2 ^ 15) + 1) → Nat.Prime (4 ^ (2 ^ 15) + 1) ∨ Nat.Prime (6 ^ (2 ^ 15) + 1) := by
  intro h
  exfalso
  apply Nat.not_prime_of_dvd_of_ne (m := 65537) at h
  · exact h
  · decide
  · decide
  · decide

lemma case_16 : Nat.Prime (10 ^ exp16 + 1) → Nat.Prime (4 ^ exp16 + 1) ∨ Nat.Prime (6 ^ exp16 + 1) := by
  intro h
  exfalso
  have hdvd : 8257537 ∣ 10 ^ exp16 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    decide
  apply Nat.not_prime_of_dvd_of_ne (m := 8257537) at h
  · exact h
  · exact hdvd
  · decide
  · decide

lemma case_17 : Nat.Prime (10 ^ exp17 + 1) → Nat.Prime (4 ^ exp17 + 1) ∨ Nat.Prime (6 ^ exp17 + 1) := by
  intro h
  exfalso
  have hdvd : 175636481 ∣ 10 ^ exp17 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    decide
  apply Nat.not_prime_of_dvd_of_ne (m := 175636481) at h
  · exact h
  · exact hdvd
  · decide
  · decide

lemma case_18 : Nat.Prime (10 ^ exp18 + 1) → Nat.Prime (4 ^ exp18 + 1) ∨ Nat.Prime (6 ^ exp18 + 1) := by
  intro h
  exfalso
  have hdvd : 639631361 ∣ 10 ^ exp18 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    decide
  apply Nat.not_prime_of_dvd_of_ne (m := 639631361) at h
  · exact h
  · exact hdvd
  · decide
  · decide

lemma case_19 : Nat.Prime (10 ^ exp19 + 1) → Nat.Prime (4 ^ exp19 + 1) ∨ Nat.Prime (6 ^ exp19 + 1) := by
  intro h
  exfalso
  have hdvd : 70254593 ∣ 10 ^ exp19 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    decide
  apply Nat.not_prime_of_dvd_of_ne (m := 70254593) at h
  · exact h
  · exact hdvd
  · decide
  · decide

lemma case_20 : Nat.Prime (10 ^ exp20 + 1) → Nat.Prime (4 ^ exp20 + 1) ∨ Nat.Prime (6 ^ exp20 + 1) := by
  intro h
  exfalso
  have hdvd : 167772161 ∣ 10 ^ exp20 + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    decide
  apply Nat.not_prime_of_dvd_of_ne (m := 167772161) at h
  · exact h
  · exact hdvd
  · decide
  · decide

lemma case_22 : Nat.Prime (10 ^ (2 ^ 22) + 1) → Nat.Prime (4 ^ (2 ^ 22) + 1) ∨ Nat.Prime (6 ^ (2 ^ 22) + 1) := by
  intro h
  exfalso
  have hdvd : 101702694862849 ∣ 10 ^ (2 ^ 22) + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : (10 : ZMod 101702694862849) ^ (2 ^ 22) + 1 = 0 := by
      sorry -- reduce_mod_char
    exact_mod_cast this
  have h_lt : 101702694862849 < 10 ^ (2 ^ 22) + 1 := by
    have h1 : 101702694862849 < 10 ^ 15 + 1 := by decide
    apply lt_of_lt_of_le h1
    apply Nat.add_le_add_right
    apply Nat.pow_le_pow_right (by decide)
    show 15 ≤ 2 ^ 22
    decide
  apply Nat.not_prime_of_dvd_of_ne (m := 101702694862849) at h
  · exact h
  · exact hdvd
  · decide
  · exact Nat.ne_of_lt h_lt

theorem oeis_378143_conjecture_claim :
  ∀ (n : ℕ),
    Nat.Prime (10 ^ (2 ^ n) + 1) →
      Nat.Prime (4 ^ (2 ^ n) + 1) ∨ Nat.Prime (6 ^ (2 ^ n) + 1) := by
  intro n
  rcases n with _ | n
  · exact case_0
  rcases n with _ | n
  · exact case_1
  rcases n with _ | n
  · exact case_2
  rcases n with _ | n
  · exact case_3
  rcases n with _ | n
  · exact case_4
  rcases n with _ | n
  · exact case_5
  rcases n with _ | n
  · exact case_6
  rcases n with _ | n
  · exact case_7
  rcases n with _ | n
  · exact case_8
  rcases n with _ | n
  · exact case_9
  rcases n with _ | n
  · exact case_10
  rcases n with _ | n
  · exact case_11
  rcases n with _ | n
  · exact case_12
  rcases n with _ | n
  · exact case_13
  rcases n with _ | n
  · exact case_14
  rcases n with _ | n
  · exact case_15
  rcases n with _ | n
  · exact case_16
  rcases n with _ | n
  · exact case_17
  rcases n with _ | n
  · exact case_18
  rcases n with _ | n
  · exact case_19
  rcases n with _ | n
  · exact case_20
  rcases n with _ | n
  · sorry -- case 21
  rcases n with _ | n
  · exact case_22
  · sorry -- case >= 23
