def Set (X : Sort u) : Prop := X → False

def Set_Prop (X : Sort u) : Prop := Set X → False

def F (X : Type 0) : Prop := (Set_Prop X → X) → Set_Prop X

inductive Unsound : Prop
| mk : (∀ X : Type 0, F X) → Unsound
