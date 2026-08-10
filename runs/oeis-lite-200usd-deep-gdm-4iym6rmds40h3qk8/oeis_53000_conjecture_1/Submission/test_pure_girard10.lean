-- Ah! Prop → Prop has sort Type 0, so it is in Type 0, but NOT in Prop!
-- In Lean, Prop is Sort 0. Type 0 is Sort 1.
-- Since Prop → Prop has type Sort 1 (Type 0), it is not a Prop (Sort 0).
-- BUT wait!
-- If we define `Set (X : Prop) : Type 0 := X → Prop`.
-- Then `Set X` has type `Type 0`.
-- Then `Set_Prop (X : Prop) : Type 0 := Set X → Prop`.
-- Then `Set_Prop X` has type `Type 0`.
-- Then `F (X : Prop) : Type 0 := (Set_Prop X → X) → Set_Prop X`.
-- Then `F X` has type `Type 0`.
-- Then `∀ X : Prop, F X` has type `Type 0`!
-- Let's check this!
def Set (X : Prop) : Type 0 := X → Prop

def Set_Prop (X : Prop) : Type 0 := Set X → Prop

def F (X : Prop) : Type 0 := (Set_Prop X → X) → Set_Prop X

#check ∀ X : Prop, F X
