def inj (F : (Type → Prop) → Prop) : Type :=
  @Sigma (Type → Prop) (fun P => PLift (F P))
