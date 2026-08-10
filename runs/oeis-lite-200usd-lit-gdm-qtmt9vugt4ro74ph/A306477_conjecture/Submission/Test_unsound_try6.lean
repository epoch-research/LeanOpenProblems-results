inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def unsound {α : Prop} (y : Bad α) (x : α) : False :=
  match y with
  | .mk f => unsound (f x) x

#print axioms unsound
