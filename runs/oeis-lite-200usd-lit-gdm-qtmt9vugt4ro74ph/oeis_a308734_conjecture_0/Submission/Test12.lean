import FormalConjectures.Util.ProblemImports

inductive T : Prop
  | mk : (∀ (p : Prop), (p → Prop) → T) → T
