inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def not_b {P : Prop} (h_eq_prop : P = (Bad P → False)) (bp : Bad P) : False :=
  match bp with
  | .mk f =>
    let p : P := cast h_eq_prop.symm (not_b h_eq_prop)
    not_b h_eq_prop (f p)
