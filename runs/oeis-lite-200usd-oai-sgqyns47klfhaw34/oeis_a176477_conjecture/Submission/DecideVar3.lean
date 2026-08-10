import FormalConjectures.Util.ProblemImports
example (n : Nat) : n = n := by
  classical
  exact (by decide : ∀ n : Nat, n = n) n
