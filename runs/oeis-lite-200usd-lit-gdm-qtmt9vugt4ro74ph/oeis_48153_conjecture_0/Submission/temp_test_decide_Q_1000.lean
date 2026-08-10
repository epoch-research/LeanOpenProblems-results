import FormalConjectures.Util.ProblemImports
open Finset

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma Q_bound_decide_all : ∀ n, n ≤ 1000 → 3 * (∑ k ∈ range n, k ^ 2 / n) ≥ (n - 1) * (n - 2) := by
  decide
