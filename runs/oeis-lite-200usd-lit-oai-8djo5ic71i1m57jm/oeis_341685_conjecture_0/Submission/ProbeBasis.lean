import FormalConjectures.Util.ProblemImports

open scoped Pointwise
open Set Filter

-- Try dangerous asymptotic basis theorem on empty/univ Nat
example : ¬ IsAsymptoticAddBasisOfOrder (∅ : Set ℕ) 1 := by
  rw [isAsymptoticAddBasisOfOrder_one_iff]
  simp

example : IsAsymptoticAddBasisOfOrder (Set.univ : Set ℕ) 1 := by
  rw [isAsymptoticAddBasisOfOrder_one_iff]
  simp
