import FormalConjectures.Util.ProblemImports

inductive T : Prop
  | mk : (Prop → T) → T

def unmk : T → (Prop → T)
  | .mk f => f

noncomputable def d (p : Prop) : T :=
  T.mk (fun (q : Prop) =>
    if p then d False else d True
  )
