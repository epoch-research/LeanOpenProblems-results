import FormalConjectures.Util.ProblemImports

inductive T : Prop
  | mk : (Prop → T) → T

def unmk : T → (Prop → T)
  | .mk f => f

def t0 : T := T.mk (fun (p : Prop) => t0)
