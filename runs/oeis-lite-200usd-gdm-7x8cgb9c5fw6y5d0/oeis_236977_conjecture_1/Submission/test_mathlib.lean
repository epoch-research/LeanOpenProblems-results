import Mathlib.Data.Nat.Totient

set_option maxRecDepth 200000

theorem test_totient : Nat.totient 10000 = 4000 := by decide
theorem test_totient2 : Nat.totient 20000 = 8000 := by decide
