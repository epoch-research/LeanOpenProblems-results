open Classical

def U : Prop := ∀ p : Prop, ((((p → Prop) → Prop) → p) → p)

noncomputable def ge (x : U) : (U → Prop) → Prop :=
  fun p =>
    x (U → Prop) (fun (g : (((U → Prop) → Prop) → Prop) → U → Prop) =>
      fun (h : (U → Prop) → Prop) =>
        h (fun (u : U) => g (fun (y : ((U → Prop) → Prop) → Prop) => h (fun (u0 : U) => y (fun (p0 : U → Prop) => p0 u0))) u)
    ) p
