import FormalConjectures.Util.ProblemImports

#check LatinSquare
#check YoungDiagram
#synth Fintype (LatinSquare 0)
#eval Fintype.card (LatinSquare 0)
#eval Fintype.card (LatinSquare 1)

example : False := by
  -- If card LatinSquare 0 contradictory? probably 1.
  norm_num
