inductive Bad : Prop → Type where
  | mk : ∀ (α : Prop), Bad (α → False) → Bad α

def F (α : Prop) (h : Bad α) : False :=
  match h with
  | .mk β h' => F (β → False) h'

partial def make_bad (α : Prop) : Bad α :=
  Bad.mk α (make_bad (α → False))

theorem bad_false : False := F False (make_bad False)
