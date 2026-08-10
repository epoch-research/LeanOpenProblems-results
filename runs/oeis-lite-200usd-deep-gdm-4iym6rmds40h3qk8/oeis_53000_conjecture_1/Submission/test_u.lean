inductive Unsound : Prop
| mk : (Type 0 → Unsound) → Unsound

noncomputable def u : Unsound := Unsound.mk (fun X => u)
