inductive T : Bool → (PUnit.{1} → Prop) → Prop
| base : T true (fun _ ↦ True)

instance : Inhabited (T true (fun _ ↦ ¬¬False)) where
  default := (inferInstance : Inhabited (T true (fun _ ↦ ¬¬False))).default
