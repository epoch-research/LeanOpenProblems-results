import FormalConjectures.Util.ProblemImports
example : ∀ n : Nat, n = n := by native_decide
example : ∀ n : Nat, n ≥ 0 := by decide
