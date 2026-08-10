import FormalConjectures.Util.ProblemImports
open Finset

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma sum_div_mod_two_le_decide_3 : ∀ H, 501 ≤ H → H ≤ 600 → ∑ k ∈ range (2 * H), (k ^ 2 / (2 * H)) % 2 ≤ H := by
  decide
