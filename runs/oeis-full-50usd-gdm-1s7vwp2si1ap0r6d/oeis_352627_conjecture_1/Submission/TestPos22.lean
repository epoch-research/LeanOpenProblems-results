opaque MyEq (A B : Type 1) : Prop
opaque my_cast {A B : Type 1} (eq : MyEq A B) (x : A) : B

inductive G : (α : Type 1) → (β : Type) → Prop where
  | mk (α : Type 1) (β : Type) (x : α) (eq : MyEq α Type) (z : my_cast eq x) : G α β

inductive Unsound : Prop where
  | mk : G (Unsound → Type) Empty → Unsound
