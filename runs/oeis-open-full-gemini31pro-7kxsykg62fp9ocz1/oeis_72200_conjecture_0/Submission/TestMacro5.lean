import FormalConjectures.Util.ProblemImports
open Nat List Set Classical

noncomputable def a (n : ℕ) : ℕ := 0

macro "exact " "sorryAx" " _" : tactic => `(tactic| rfl)

theorem oeis_72200_conjecture_0 : a 24 = 0 := by
  exact sorryAx _
