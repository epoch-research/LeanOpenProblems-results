import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime
set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

theorem test_520 : π (π 520) = 25 := by decide
