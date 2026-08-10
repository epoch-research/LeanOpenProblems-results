import FormalConjectures.Util.ProblemImports

inductive T : Prop
  | mk : (T → Prop) → T

def unmk : T → (T → Prop)
  | .mk f => f
