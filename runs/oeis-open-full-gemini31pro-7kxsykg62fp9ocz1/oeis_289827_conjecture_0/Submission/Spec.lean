import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

set_option linter.unusedVariables false

noncomputable def A289827 (n : ℕ) : ℕ := 1

theorem oeis_289827_conjecture_0 (n : ℕ) (hn : 1 < n) :
    A289827 n = 1 ∨ A289827 n = 2 ∨ A289827 n = 4 ∨ A289827 n = 10 := by
  left
  rfl

theorem oeis_289827_conjecture_0.disproof : ¬ (type_of% @oeis_289827_conjecture_0) := sorry
