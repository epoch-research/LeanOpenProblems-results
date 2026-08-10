import FormalConjectures.Util.ProblemImports
open Finset

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

lemma a048153_odd_le_decide : ∀ H, H ≤ 100 → A048153 (2 * H + 1) ≤ H * (2 * H + 1) := by
  decide
