import FormalConjectures.Util.ProblemImports

inductive T : Prop
  | mk : (Prop → T) → T
