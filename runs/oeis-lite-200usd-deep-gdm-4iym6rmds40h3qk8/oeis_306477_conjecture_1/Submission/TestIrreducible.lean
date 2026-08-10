open Classical

@[irreducible] def inj (F : (Prop → Prop) → Prop) : Type :=
  Σ (P : Prop → Prop), PLift (F P)

noncomputable def proj (X : Type) (P : Prop → Prop) : Prop :=
  if h : ∃ (F : (Prop → Prop) → Prop), X = inj F then
    let h_eq := Classical.choose_spec h
    ∃ (x : X), (cast h_eq x).fst = P
  else
    False
