def Set (X : Sort u) : Type 0 := X → Prop

def Set_Prop (X : Sort u) : Type 0 := Set X → Prop

def F (X : Type 0) : Type 0 := (Set_Prop X → X) → Set_Prop X

inductive Unsound : Type 0
| mk : (∀ X : Prop, F (PLift X)) → Unsound
