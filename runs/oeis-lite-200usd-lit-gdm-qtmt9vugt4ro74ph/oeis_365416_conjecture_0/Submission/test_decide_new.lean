import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

lemma pow_three_zmod_6889 (e : ℕ) : (3 : ZMod 6889) ^ e = 6887 ↔ e % 2296 = 1972 := by
  have h_pow : (3 : ZMod 6889) ^ e = (3 : ZMod 6889) ^ (e % 2296) := by
    have h_eq : e = 2296 * (e / 2296) + e % 2296 := (Nat.div_add_mod e 2296).symm
    conv_lhs => rw [h_eq]
    rw [pow_add, pow_mul]
    have : (3 : ZMod 6889) ^ 2296 = 1 := by decide
    rw [this, one_pow, one_mul]
  rw [h_pow]
  constructor
  · intro h
    have h_mod : e % 2296 < 2296 := Nat.mod_lt _ (by decide)
    interval_cases he_mod : e % 2296 <;> revert h <;> decide
  · intro h
    rw [h]
    decide
