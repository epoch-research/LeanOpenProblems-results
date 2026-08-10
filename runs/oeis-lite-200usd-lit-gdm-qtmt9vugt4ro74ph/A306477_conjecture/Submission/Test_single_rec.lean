inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def not_b (p_val : Unit → Prop) (bp : Bad (p_val ())) : False :=
  match bp with
  | .mk f => not_b p_val (f (by sorry))
