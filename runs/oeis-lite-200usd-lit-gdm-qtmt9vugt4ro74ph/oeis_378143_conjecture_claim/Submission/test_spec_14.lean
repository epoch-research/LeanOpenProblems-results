import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 200000
set_option maxRecDepth 200000

open Nat

theorem not_prime_of_zmod_pow_ne_one {M a : ℕ} (hp : M.Prime) (ha : (a : ZMod M) ≠ 0)
    (h : (a : ZMod M) ^ (M - 1) ≠ 1) : False := by
  haveI : Fact M.Prime := ⟨hp⟩
  have h_fermat := ZMod.pow_card_sub_one_eq_one ha
  exact h h_fermat

theorem test_14 (hp : (10 ^ (2 ^ 14) + 1).Prime) : False := by
  have ha : (3 : ZMod (10 ^ (2 ^ 14) + 1)) ≠ 0 := by
    decide
  have h_fermat : (3 : ZMod (10 ^ (2 ^ 14) + 1)) ^ (10 ^ (2 ^ 14)) ≠ 1 := by
    reduce_mod_char
    decide
  exact not_prime_of_zmod_pow_ne_one hp ha h_fermat
