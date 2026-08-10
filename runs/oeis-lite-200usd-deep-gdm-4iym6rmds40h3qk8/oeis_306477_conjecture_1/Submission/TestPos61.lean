-- Ah, Prop → Prop has type Type, so (Prop → Prop) → Prop is of type Type!
-- What if we do:
--   U : Prop := (Prop → Prop) ? No, that's of type Type.
-- What about:
def U : Prop := ∀ p : Prop, (p → Prop) → Prop
