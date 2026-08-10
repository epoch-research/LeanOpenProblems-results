-- Let's define the retraction on Prop!
-- Since Prop is in Sort 0, it is extremely simple.
-- We want a retraction between `sb = (Prop → Prop) → Prop` and `Prop`.
-- Wait, does Cantor's theorem prevent this?
-- Only if we can prove the retraction properties!
-- But since Prop is impredicative, we CAN define a retraction!
-- Let's see:
-- inj : sb → Prop
-- proj : Prop → sb
-- such that proj (inj T) = T!
-- Wait, is this possible?
-- Let's try:
def sb := (Prop → Prop) → Prop

noncomputable def inj (T : sb) : Prop :=
  ∃ (p : Prop → Prop), (∀ x, p x ↔ (x = True)) ∧ T p

noncomputable def proj (P : Prop) : sb :=
  fun p => P ∧ (∀ x, p x ↔ (x = True))
