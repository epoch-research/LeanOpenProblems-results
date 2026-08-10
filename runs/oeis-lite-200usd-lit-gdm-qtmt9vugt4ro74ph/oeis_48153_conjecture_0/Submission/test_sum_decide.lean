import FormalConjectures.Util.ProblemImports
open Finset

set_option maxRecDepth 10000000
set_option maxHeartbeats 0

lemma sum_div_mod_two_le_decide : ∀ H, H ≤ 400 → ∑ k ∈ range (2 * H), (k ^ 2 / (2 * H)) % 2 ≤ H := by
  decide
