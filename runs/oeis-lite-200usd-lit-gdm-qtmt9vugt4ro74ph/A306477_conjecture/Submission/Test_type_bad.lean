inductive Bad (α : Type) : Type
  | mk : (α → Bad α) → Bad α

def unsound {α : Type} (y : Bad α) (x : α) : Empty :=
  match y with
  | .mk f => unsound (f x) x
