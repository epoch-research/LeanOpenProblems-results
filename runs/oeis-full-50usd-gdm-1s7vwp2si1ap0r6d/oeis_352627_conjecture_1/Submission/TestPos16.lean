def MyEq (A B : Type 1) : Prop := A = B

inductive G : (α : Type 1) → (β : Type) → Prop where
  | mk (α : Type 1) (β : Type) (x : α) (eq : MyEq α Type) (z : cast eq x) : G α β

inductive Unsound : Prop where
  | mk : G (Unsound → Type) Empty → Unsound
