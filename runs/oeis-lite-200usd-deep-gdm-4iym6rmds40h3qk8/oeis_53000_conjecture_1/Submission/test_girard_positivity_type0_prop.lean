def Set (X : Prop) : Type 0 := X → Prop

def Set_Prop (X : Prop) : Type 0 := Set X → Prop

def F (X : Prop) : Type 0 := (Set_Prop X → X) → Set_Prop X

inductive Unsound : Type 0
| mk : (∀ (X : Prop), F X) → Unsound
