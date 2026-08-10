import FormalConjectures.Util.ProblemImports
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000
example : IsSquare (12769 : ℕ) := by decide +kernel
example : ¬ IsSquare (12770 : ℕ) := by decide +kernel
example : (∑ x ∈ range 50, ∑ y ∈ range 50, (if IsSquare (x+y) then 1 else 0)) = 311 := by decide +kernel
