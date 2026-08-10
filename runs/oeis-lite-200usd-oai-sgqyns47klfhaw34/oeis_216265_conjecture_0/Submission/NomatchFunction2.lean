import FormalConjectures.Util.ProblemImports
example (P : Prop) (h : ¬ P) : False := by
  nomatch h
