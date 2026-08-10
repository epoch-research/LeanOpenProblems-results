import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 200000

def A048153 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) (fun k => k ^ 2 % n)

lemma test_decide : A048153 1000 ≤ (1000^2 - 1) / 2 := by
  decide
