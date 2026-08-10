import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000
set_option exponentiation.threshold 100000

theorem not_prime_10_2_15 : ¬ Nat.Prime (10 ^ (2 ^ 15) + 1) := by
  intro hp
  have h_ne : (3 : ZMod (10 ^ (2 ^ 15) + 1)) ≠ 0 := by
    rw [← ZMod.val_ne_zero]
    rw [ZMod.val_ofNat]
    decide
  have h_one : (3 : ZMod (10 ^ (2 ^ 15) + 1)) ^ (10 ^ (2 ^ 15)) = 1 :=
    @ZMod.pow_card_sub_one_eq_one (10 ^ (2 ^ 15) + 1) ⟨hp⟩ 3 h_ne
  have h_ne_one : (3 : ZMod (10 ^ (2 ^ 15) + 1)) ^ (10 ^ (2 ^ 15)) ≠ 1 := by
    reduce_mod_char
    decide
  exact h_ne_one h_one
