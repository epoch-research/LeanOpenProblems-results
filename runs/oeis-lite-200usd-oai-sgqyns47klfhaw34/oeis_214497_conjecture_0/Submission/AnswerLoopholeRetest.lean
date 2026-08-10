import FormalConjectures.Util.ProblemImports

open Nat

example (P : Prop) : P := by
  change answer(sorry)
  trivial

example (P : Prop) : P := by
  exact (show answer(sorry) from trivial)

example (P : Prop) : P := by
  suffices answer(sorry) by trivial
  trivial
