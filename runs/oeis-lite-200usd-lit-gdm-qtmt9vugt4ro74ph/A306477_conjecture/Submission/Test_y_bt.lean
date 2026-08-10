inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def y_bt (u : Unit) : Bad True := .mk (fun (_ : True) => y_bt u)
