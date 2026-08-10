open Classical

def U : Prop := ∀ p : Prop, ((p → Prop) → Prop) → p

noncomputable def lam (F : ((U → Prop) → Prop) → U) : U :=
  fun p f =>
    sorry
