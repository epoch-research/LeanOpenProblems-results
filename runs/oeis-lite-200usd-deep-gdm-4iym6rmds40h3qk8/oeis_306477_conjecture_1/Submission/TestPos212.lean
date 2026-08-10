open Classical

def U : Prop := ∀ p : Prop, (((p → Prop) → p) → p)

noncomputable def lam (F : (U → Prop) → U) : U :=
  fun p f =>
    f (fun (h : p → Prop) =>
      let S : U → Prop := fun u => h (u p f)
      F S p f
    )
