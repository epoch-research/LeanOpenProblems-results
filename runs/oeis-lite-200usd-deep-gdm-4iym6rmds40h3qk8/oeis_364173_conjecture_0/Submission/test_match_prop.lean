import FormalConjectures.Util.ProblemImports

def f_base (x : Prop) : Prop :=
  match x with
  | True => True
  | _ => False
