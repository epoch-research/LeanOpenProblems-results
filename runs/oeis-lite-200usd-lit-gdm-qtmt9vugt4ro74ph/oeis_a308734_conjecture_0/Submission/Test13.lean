import FormalConjectures.Util.ProblemImports

inductive T : Prop
  | mk : (∀ (p : Prop), (p → Prop) → T) → T

def unmk : T → ∀ (p : Prop), (p → Prop) → T
  | .mk f => f
