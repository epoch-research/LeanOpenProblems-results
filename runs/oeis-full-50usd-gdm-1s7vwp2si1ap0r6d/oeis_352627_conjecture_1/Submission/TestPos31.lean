inductive MyEq : Type 1 → Type 1 → Prop where
  | refl (A : Type 1) : MyEq A A

inductive MyCast : (A B : Type 1) → MyEq A B → A → B → Prop where
  | refl (A : Type 1) (x : A) : MyCast A A (.refl A) x x
