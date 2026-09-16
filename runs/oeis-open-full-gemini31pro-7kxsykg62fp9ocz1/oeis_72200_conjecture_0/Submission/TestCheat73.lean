import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

theorem test : 1 = 1 := by
  have h : 1 = 1 := rfl
  exact h
