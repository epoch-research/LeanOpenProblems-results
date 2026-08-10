import FormalConjectures.Util.ProblemImports
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000
-- which instance?
example : (if IsSquare (5:ℕ) then 1 else 0) = (0:ℕ) := by decide +kernel
example : (∑ x ∈ range 6, (if IsSquare x then (1:ℕ) else 0)) = 3 := by decide +kernel
