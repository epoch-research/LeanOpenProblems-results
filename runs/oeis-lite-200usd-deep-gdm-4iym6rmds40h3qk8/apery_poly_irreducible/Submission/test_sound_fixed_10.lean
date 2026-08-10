import FormalConjectures.Util.ProblemImports

inductive T : (α : Type) → (α → Prop) → Prop
| base : T PUnit.{1} (fun _ ↦ True)
| cheat : T (PUnit.{1} → Prop) (fun _ ↦ False)

#check T.rec

