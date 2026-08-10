import FormalConjectures.Util.ProblemImports

open Finset

def A048153_local (n : ℕ) : ℕ :=
  ∑ k ∈ range n, k ^ 2 % n

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma spec_cases_large : ∀ n, 1001 ≤ n → n ≤ 2000 → A048153_local n ≤ (n ^ 2 - 1) / 2 := by
  decide
