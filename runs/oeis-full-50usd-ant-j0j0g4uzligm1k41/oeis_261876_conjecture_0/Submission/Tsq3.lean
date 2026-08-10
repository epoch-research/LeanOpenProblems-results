import FormalConjectures.Util.ProblemImports
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000
example : (∑ x ∈ range 50, (if IsSquare x then (1:ℕ) else 0)) = 8 := by decide +kernel
example : (∑ x ∈ range 30, ∑ y ∈ range 30, (if IsSquare (x+y) then (1:ℕ) else 0)) = 0 := by decide +kernel
