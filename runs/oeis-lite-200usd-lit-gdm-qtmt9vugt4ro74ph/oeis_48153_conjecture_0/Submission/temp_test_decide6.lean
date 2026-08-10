import FormalConjectures.Util.ProblemImports
open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
lemma spec_cases_all_large : ∀ n, 1 ≤ n → n ≤ 2000 → A048153 n ≤ (n ^ 2 - 1) / 2 := by
  decide
