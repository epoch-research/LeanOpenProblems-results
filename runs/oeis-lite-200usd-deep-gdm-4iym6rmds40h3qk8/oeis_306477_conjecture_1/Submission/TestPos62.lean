-- Why does (p → Prop) have Type? Because p is a Prop, so p → Prop is Type.
-- Wait, in Lean, if p : Prop, is p → Prop of type Prop?
-- No! p → Prop is of type Type.
-- But wait! what about ∀ x : p, Prop? That is also Type.
-- What about:
def U : Prop := ∀ p : Prop, p
