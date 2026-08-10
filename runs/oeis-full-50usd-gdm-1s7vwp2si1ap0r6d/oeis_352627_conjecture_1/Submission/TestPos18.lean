def LeibnizEq (A B : Type 1) : Sort 2 := (P : Type 1 → Type 1) → P A → P B

def my_cast {A B : Type 1} (eq : LeibnizEq A B) (x : A) : B :=
  eq (fun T => T) x

inductive G : (α : Type 1) → (β : Type) → Prop where
  | mk (α : Type 1) (β : Type) (x : α) (eq : LeibnizEq α Type) (z : my_cast eq x) : G α β

inductive Unsound : Prop where
  | mk : G (Unsound → Type) Empty → Unsound
