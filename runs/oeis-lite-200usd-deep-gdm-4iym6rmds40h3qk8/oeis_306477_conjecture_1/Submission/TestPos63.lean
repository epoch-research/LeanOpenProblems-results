-- Yes, ∀ p : Prop, p is in Prop.
-- What about:
def U : Prop := ∀ p : Prop, (p → True) → p
