import FormalConjectures.Util.ProblemImports

inductive T : Prop
  | mk : ((T → Prop) → Prop) → T

def unmk : T → ((T → Prop) → Prop)
  | .mk f => f
