inductive G : (α : Type) → (β : Type) → Type where
  | mk (α : Type) (β : Type) (x : α) (eq : α = Prop) (z : cast eq x) : G α β

inductive Unsound : Type where
  | mk : G (Unsound → Prop) Empty → Unsound
