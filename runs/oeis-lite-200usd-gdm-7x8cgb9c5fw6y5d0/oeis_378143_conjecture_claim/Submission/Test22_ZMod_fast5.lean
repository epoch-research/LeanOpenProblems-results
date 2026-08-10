import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 5000000
set_option maxRecDepth 2000000

def p : ℕ := 101702694862849

theorem h_div_zmod : (10 : ZMod p) ^ 4194304 = p - 1 := by
  unfold p
  reduce_mod_char

theorem h_div : p ∣ 10 ^ (2 ^ 22) + 1 := by
  have h_pow : 2 ^ 22 = 4194304 := rfl
  rw [h_pow]
  rw [← CharP.cast_eq_zero_iff (ZMod p) p]
  rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
  have h_cast : (↑10 : ZMod p) = (10 : ZMod p) := rfl
  rw [h_cast]
  rw [h_div_zmod]
  unfold p
  reduce_mod_char
