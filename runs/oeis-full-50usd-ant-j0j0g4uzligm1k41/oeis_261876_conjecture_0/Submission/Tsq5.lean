import FormalConjectures.Util.ProblemImports
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000
example : Nat.sqrt 12769 = 113 := by decide +kernel
example : (∑ y ∈ range 5, (if Nat.sqrt (3+y) * Nat.sqrt (3+y) = 3+y then (1:ℕ) else 0)) = 2 := by decide +kernel
example : (∑ x ∈ range 30, ∑ y ∈ range 30, (if Nat.sqrt (x+y)*Nat.sqrt (x+y) = x+y then (1:ℕ) else 0)) = 102 := by decide +kernel
