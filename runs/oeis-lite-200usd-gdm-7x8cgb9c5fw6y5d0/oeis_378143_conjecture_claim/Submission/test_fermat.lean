import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000
set_option exponentiation.threshold 100000

theorem not_prime_of_fermat_witness (n : ℕ) (a : ℕ) (ha_ne : (a : ZMod (10 ^ (2 ^ n) + 1)) ≠ 0)
    (ha_pow : (a : ZMod (10 ^ (2 ^ n) + 1)) ^ (10 ^ (2 ^ n)) ≠ 1) : ¬ Nat.Prime (10 ^ (2 ^ n) + 1) := by
  intro hp
  have h_one := @ZMod.pow_card_sub_one_eq_one (10 ^ (2 ^ n) + 1) ⟨hp⟩ a ha_ne
  exact ha_pow h_one


theorem not_prime_10_2_13 : ¬ Nat.Prime (10 ^ (2 ^ 13) + 1) := by
  apply not_prime_of_fermat_witness 13 3
  · decide
  · reduce_mod_char
    decide

theorem not_prime_10_2_14 : ¬ Nat.Prime (10 ^ (2 ^ 14) + 1) := by
  apply not_prime_of_fermat_witness 14 3
  · decide
  · reduce_mod_char
    decide

