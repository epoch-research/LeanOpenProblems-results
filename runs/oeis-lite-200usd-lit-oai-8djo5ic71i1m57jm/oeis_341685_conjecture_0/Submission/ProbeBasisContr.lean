import FormalConjectures.Util.ProblemImports
open Set

example : False := by
  have h := isMulBasisOfOrder_one_iff (M := ℕ) (A := (∅ : Set ℕ))
  guard_target = False
  fail_if_success exact (h.mpr (by ext x; simp))
  sorry
