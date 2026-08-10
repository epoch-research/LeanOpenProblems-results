-- This means we can form impredicative definitions in Prop!
-- Let's see: can we define:
--   U : Prop := ∀ p : Prop, ((p → Prop) → Prop) → p
-- Wait, p → Prop is of type Type, so we can't quantify over it if we want U : Prop?
-- Wait! Is ((p → Prop) → Prop) of type Type? Yes.
-- But a function from Type to Prop is in Prop!
-- Wait, let's check!
def U : Prop := ∀ p : Prop, (((p → Prop) → Prop) → p)
