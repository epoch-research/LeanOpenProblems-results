inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def unsound {α : Prop} (y : Bad α) (x : α) : False :=
  match y with
  | .mk f => unsound (f x) x

variable (P : Prop) (h_eq : P ↔ (Bad P → False))

def g (x : P) : False :=
  let f : P → Bad P := fun (x' : P) => False.elim (g x')
  unsound (.mk f) x
