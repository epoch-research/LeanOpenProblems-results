import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 10000

def N : ℕ := 10 ^ 8192 + 1

theorem not_prime_10_8192 : ¬ Nat.Prime N := by
  intro hp
  have h_ne : (3 : ZMod N) ≠ 0 := by
    rw [← ZMod.val_ne_zero]
    rw [ZMod.val_ofNat]
    norm_num [N]
  have h_one : (3 : ZMod N) ^ (10 ^ 8192) = 1 := @ZMod.pow_card_sub_one_eq_one N ⟨hp⟩ 3 h_ne
  have h_val : (3 : ZMod N) ^ (10 ^ 8192) = 0 := by
    unfold N
    reduce_mod_char
  sorry
