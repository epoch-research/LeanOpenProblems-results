mutual
  inductive MyEq (A B : Type 1) : Prop where
    | refl : MyEq A A

  inductive MyCast : (A B : Type 1) → MyEq A B → A → B → Prop where
    | refl (A : Type 1) (x : A) : MyCast A A .refl x x

  inductive G : (α : Type 1) → (β : Type) → Prop where
    | mk (α : Type 1) (β : Type) (x : α) (eq : MyEq α Type) (y : Type) (h : MyCast α Type eq x y) (z : y) : G α β
end

inductive Unsound : Prop where
  | mk : G (Unsound → Type) Empty → Unsound
