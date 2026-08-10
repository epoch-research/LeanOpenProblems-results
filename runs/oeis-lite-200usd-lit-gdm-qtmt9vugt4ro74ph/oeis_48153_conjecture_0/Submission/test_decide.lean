import FormalConjectures.Util.ProblemImports
open Finset

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma test_decide : ∀ H, 4 ≤ H → H < 500 → 3 * (∑ k ∈ range (2 * H + 1), k ^ 2 / (2 * H + 1)) ≥ (2 * H) * (2 * H - 1) := by
  decide
