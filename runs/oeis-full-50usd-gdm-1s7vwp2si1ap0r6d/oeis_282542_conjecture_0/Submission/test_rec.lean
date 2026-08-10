inductive Bad : Prop → Type where
  | mk : ∀ (α : Prop), Bad (α → False) → Bad α

inductive Rec : Type where
  | mk : (Rec → ∀ α, Bad α) → Rec
