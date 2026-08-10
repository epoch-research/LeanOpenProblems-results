inductive Bad : Prop → Type where
  | mk : ∀ (α : Prop), Bad (α → False) → Bad α

def make_bad (α : Prop) : Bad α :=
  let rec loop (β : Prop) : Bad β :=
    Bad.mk β (loop (β → False))
  loop α
