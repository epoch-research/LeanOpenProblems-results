import FormalConjectures.Util.ProblemImports
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000
-- A: nested small, IsSquare(x+y)
example : (∑ x ∈ range 5, ∑ y ∈ range 5, (if IsSquare (x+y) then (1:ℕ) else 0)) = 13 := by decide +kernel
-- B: single sum, arg x+3
example : (∑ y ∈ range 5, (if IsSquare (3+y) then (1:ℕ) else 0)) = 2 := by decide +kernel
