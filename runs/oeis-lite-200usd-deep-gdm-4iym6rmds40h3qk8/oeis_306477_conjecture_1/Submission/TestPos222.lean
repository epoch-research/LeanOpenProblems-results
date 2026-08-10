open Classical

def U : Prop := ∀ p : Prop, (((p → Prop) → Prop) → p)

noncomputable def le (x : (U → Prop) → Prop) : U :=
  fun p f => f (fun (y : p → Prop) => x (fun (u : U) => y (u p f)))
