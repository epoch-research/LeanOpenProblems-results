import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 30000
set_option maxRecDepth 30000

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
  · intro _
    left
    decide
  · intro _
    left
    decide
  · intro h
    exfalso
    apply Nat.not_prime_of_dvd_of_ne (m := 353) at h
    · exact h
    · decide
    · decide
    · decide
  · intro h
    exfalso
    apply Nat.not_prime_of_dvd_of_ne (m := 19841) at h
    · exact h
    · decide
    · decide
    · decide
  · intro h
    exfalso
    apply Nat.not_prime_of_dvd_of_ne (m := 1265011073) at h
    · exact h
    · decide
    · decide
    · decide
  · intro h
    exfalso
    apply Nat.not_prime_of_dvd_of_ne (m := 257) at h
    · exact h
    · decide
    · decide
    · decide
  · intro h
    exfalso
    apply Nat.not_prime_of_dvd_of_ne (m := 10753) at h
    · exact h
    · decide
    · decide
    · decide
  · intro h
    exfalso
    apply Nat.not_prime_of_dvd_of_ne (m := 1514497) at h
    · exact h
    · decide
    · decide
    · decide
  · intro h
    exfalso
    apply Nat.not_prime_of_dvd_of_ne (m := 1856104284667693057) at h
    · exact h
    · decide
    · decide
    · decide
  · intro h
    exfalso
    apply Nat.not_prime_of_dvd_of_ne (m := 106907803649) at h
    · exact h
    · decide
    · decide
    · decide
  · intro h
    exfalso
    apply Nat.not_prime_of_dvd_of_ne (m := 458924033) at h
    · exact h
    · decide
    · decide
    · decide
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · done
