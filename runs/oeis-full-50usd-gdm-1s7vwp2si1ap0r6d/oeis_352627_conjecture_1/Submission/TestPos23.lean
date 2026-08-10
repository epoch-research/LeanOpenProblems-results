inductive G : (α : Type 1) → (β : Type) → Prop where
  | mk (α : Type 1) (β : Type) (x : α) (eq : Quot.mk (fun (A B : Type 1) => A = B) α = Quot.mk (fun (A B : Type 1) => A = B) Type) (z : cast eq x) : G α β

inductive Unsound : Prop where
  | mk : G (Unsound → Type) Empty → Unsound
