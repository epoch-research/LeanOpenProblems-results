import FormalConjectures.Util.ProblemImports

set_option exponentiation.threshold 2000000
set_option maxRecDepth 2000000

def p : ℕ := 101702694862849

theorem h_div : p ∣ 10 ^ 4194304 + 1 := by
  rw [← CharP.cast_eq_zero_iff (ZMod p) p]
  push_cast
  decide

