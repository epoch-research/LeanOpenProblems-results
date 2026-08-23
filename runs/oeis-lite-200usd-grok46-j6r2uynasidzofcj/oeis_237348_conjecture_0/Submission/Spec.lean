import FormalConjectures.Util.ProblemImports

theorem foo : ∀ n, Squarefree (Nat.squarefreePart n) :=
  Nat.squarefree_squarefreePart
