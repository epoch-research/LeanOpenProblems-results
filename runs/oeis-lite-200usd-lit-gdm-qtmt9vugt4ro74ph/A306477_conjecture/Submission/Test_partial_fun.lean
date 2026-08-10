inductive Bad (α : Prop) : Prop
  | mk : (α → Bad α) → Bad α

partial def unsound_proof (y : Bad False) : False :=
  unsound_proof y
