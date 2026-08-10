inductive Bad : Type 1
| mk1 : (Prop → Bad) → Bad
| mk2 : Bad

open Classical

noncomputable def inj (p : Prop) : Bad :=
  if p then Bad.mk1 (fun q => inj q) else Bad.mk2
