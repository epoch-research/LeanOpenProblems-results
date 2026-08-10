import FormalConjectures.Util.ProblemImports

open Nat ZMod

theorem not_prime_of_zmod_pow_ne_one {M a : ℕ} (hp : M.Prime) (ha : (a : ZMod M) ≠ 0)
    (h : (a : ZMod M) ^ (M - 1) ≠ 1) : False := by
  haveI : Fact M.Prime := ⟨hp⟩
  have h_fermat := ZMod.pow_card_sub_one_eq_one ha
  exact h h_fermat

theorem test_13 : Nat.Prime (10 ^ (2 ^ 13) + 1) → False := by
  intro hp
  have h_gt : 3 < 10 ^ (2 ^ 13) + 1 := by
    have h1 : 3 < 10 ^ 1 + 1 := by decide
    apply lt_of_lt_of_le h1
    apply Nat.add_le_add_right
    apply Nat.pow_le_pow_right (by decide)
    decide
  have ha : (3 : ZMod (10 ^ (2 ^ 13) + 1)) ≠ 0 := by
    intro h
    have h_val := congr_arg ZMod.val h
    rw [ZMod.val_natCast (10 ^ (2 ^ 13) + 1) 3, ZMod.val_zero] at h_val
    rw [Nat.mod_eq_of_lt h_gt] at h_val
    contradiction
  have h_fermat : (3 : ZMod (10 ^ (2 ^ 13) + 1)) ^ (10 ^ (2 ^ 13)) ≠ 1 := by
    reduce_mod_char
    decide
  exact not_prime_of_zmod_pow_ne_one hp ha h_fermat
