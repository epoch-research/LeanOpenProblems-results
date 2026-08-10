import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
-- is Nat.sqrt kernel-accelerated?
example : Nat.sqrt 69383 = 263 := by rfl
example : Nat.sqrt 1000000000000 = 1000000 := by rfl
