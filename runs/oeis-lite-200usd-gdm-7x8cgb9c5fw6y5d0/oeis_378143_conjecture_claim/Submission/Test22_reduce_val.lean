import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 2000000
set_option maxRecDepth 2000000

def p : ℕ := 101702694862849

theorem h_div : (10 : ZMod p) ^ 4194304 = -1 := by
  reduce_mod_char
