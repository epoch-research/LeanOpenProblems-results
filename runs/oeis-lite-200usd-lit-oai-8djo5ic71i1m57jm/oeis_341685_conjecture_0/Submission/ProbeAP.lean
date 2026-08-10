import FormalConjectures.Util.ProblemImports

open Set

-- try to make impossible AP of length 2 with zero difference from pair theorem?
example : False := by
  have h := Set.isAPOfLengthWith_pair (α:=ℤ) (a:=0) (b:=0)
  -- requires DecidableEq/AddCommGroup, maybe no inequality
  sorry
