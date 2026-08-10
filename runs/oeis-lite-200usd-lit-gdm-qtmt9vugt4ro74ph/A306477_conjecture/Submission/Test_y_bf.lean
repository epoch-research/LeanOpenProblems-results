inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def y_bf : Bad False := .mk (fun (f : False) => False.elim f)
