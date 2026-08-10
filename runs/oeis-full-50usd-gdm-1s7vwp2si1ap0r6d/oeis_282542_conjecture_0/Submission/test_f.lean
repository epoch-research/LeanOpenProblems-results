inductive Bad : Prop → Type where
  | mk : ∀ (α : Prop), Bad (α → False) → Bad α

def F (α : Prop) (h : Bad α) : False :=
  match h with
  | .mk β h' => F (β → False) h'
