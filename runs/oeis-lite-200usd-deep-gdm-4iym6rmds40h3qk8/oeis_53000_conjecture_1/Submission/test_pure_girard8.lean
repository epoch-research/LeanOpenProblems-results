-- Ah, (X : Type) → F X has type Type 1, which means it is in universe 1.
-- So we cannot put it in an inductive type of Type 0 (universe 1).
-- But wait!
-- Can we define F X as a Prop?
-- Let's see:
def Set (X : Type 0) : Prop := X → Prop -- wait, X → Prop has sort Type 0!

def Set_Prop (X : Type 0) : Prop := Set X → Prop
-- If Set X has sort Type 0, then Set X → Prop has sort Type 0!
-- Wait, can we do:
def F (X : Type 0) : Prop := (Set_Prop X → X) → Set_Prop X
-- If Set_Prop X has sort Type 0, and X has sort Type 0,
-- then (Set_Prop X → X) has sort Type 0!
-- So F X has sort Type 0, which is Prop!
-- Let's check!
