inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

def unsound {α : Prop} (y : Bad α) (x : α) : False :=
  match y with
  | .mk f => unsound (f x) x

def f_true : True → Bad True
  | _ => .mk f_true

theorem proof_of_false : False :=
  unsound (.mk f_true) True.intro
