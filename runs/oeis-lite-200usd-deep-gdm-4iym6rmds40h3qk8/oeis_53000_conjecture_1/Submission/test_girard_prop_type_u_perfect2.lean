def Set (X : Type 0) : Type 0 := X → Prop

def Set_Prop (X : Type 0) : Prop := Set X → False

def F (X : Type 0) : Prop := (Set_Prop X → X) → Set_Prop X

inductive Unsound : Type 0
| mk : (∀ X : Type 0, F X) → Unsound
