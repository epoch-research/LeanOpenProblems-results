import FormalConjectures.Util.ProblemImports
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
example : ((∑ k ∈ range 264, 2^(20*k^2))^4 / 2^(20*69383)) % 2^20 = 34692 := by decide +kernel
