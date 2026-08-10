import FormalConjectures.Util.ProblemImports

inductive T : Prop
  | mk : (Prop → T) → T

def unmk : T → (Prop → T)
  | .mk f => f

def diag (p : Prop) : T :=
  T.mk (fun (q : Prop) =>
    -- We want to return a T.
    -- Can we use `unmk`?
    sorry
  )
