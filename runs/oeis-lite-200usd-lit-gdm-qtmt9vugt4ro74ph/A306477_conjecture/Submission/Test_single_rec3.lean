inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def not_b {P : Prop} (h_eq_prop : P = (Bad P → False)) (p_val : Unit → P) (bp : Bad P) : False :=
  match bp with
  | .mk f =>
    not_b h_eq_prop p_val (f (p_val ()))

#print axioms not_b

