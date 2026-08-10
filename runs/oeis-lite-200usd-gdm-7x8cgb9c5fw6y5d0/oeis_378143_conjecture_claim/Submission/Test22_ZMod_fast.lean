import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 2000000
set_option maxRecDepth 2000000

def p : ℕ := 101702694862849

theorem h_div_zmod : (10 : ZMod p) ^ (2 ^ 22) = p - 1 := by
  unfold p
  reduce_mod_char

theorem h_div : p ∣ 10 ^ (2 ^ 22) + 1 := by
  rw [← CharP.cast_eq_zero_iff (ZMod p) p]
  push_cast
  rw [h_div_zmod]
  unfold p
  reduce_mod_char
