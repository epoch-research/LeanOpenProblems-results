inductive G : (α : Type 1) → (β : Type) → Prop where
  | mk (α : Type 1) (β : Type) (x : α) (eq : HEq α Type) (z : cast (eq_of_heq eq) x) : G α β

inductive Unsound : Prop where
  | mk : G (Unsound → Type) Empty → Unsound
