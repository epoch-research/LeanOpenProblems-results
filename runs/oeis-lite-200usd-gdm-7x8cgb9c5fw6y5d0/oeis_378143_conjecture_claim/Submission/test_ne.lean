import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000
set_option exponentiation.threshold 100000

def N : ℕ := 10 ^ 128 + 1

theorem test_ne : (3 : ZMod N) ^ (10 ^ 128) ≠ 1 := by
  unfold N
  reduce_mod_char
  decide
