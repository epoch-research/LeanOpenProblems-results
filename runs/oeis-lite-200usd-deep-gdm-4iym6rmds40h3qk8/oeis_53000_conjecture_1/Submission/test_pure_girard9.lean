-- Ah! Prop is in Type 0, so any function returning Prop has type Type 0.
-- But wait!
-- What if we use `Prop` instead of `Type 0` as the domain?
-- Let's see:
def Set (X : Prop) : Prop := X → Prop

def Set_Prop (X : Prop) : Prop := Set X → Prop

def F (X : Prop) : Prop := (Set_Prop X → X) → Set_Prop X

#check ∀ X : Prop, F X
