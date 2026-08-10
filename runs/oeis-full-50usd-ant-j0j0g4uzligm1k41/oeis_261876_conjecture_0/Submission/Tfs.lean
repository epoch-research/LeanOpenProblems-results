import FormalConjectures.Util.ProblemImports
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000
-- can kernel reduce a Finset.sum?
example : (∑ k ∈ range 10, 2^k) = 1023 := by decide +kernel
