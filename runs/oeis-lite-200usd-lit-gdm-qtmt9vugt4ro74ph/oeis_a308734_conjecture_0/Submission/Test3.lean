import FormalConjectures.Util.ProblemImports

inductive T : Prop
  | mk : (Prop → Prop) → T

def unmk : T → (Prop → Prop)
  | .mk f => f
