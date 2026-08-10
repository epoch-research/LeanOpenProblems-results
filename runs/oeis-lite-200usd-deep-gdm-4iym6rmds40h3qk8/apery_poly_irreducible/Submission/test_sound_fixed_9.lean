import FormalConjectures.Util.ProblemImports

inductive T : (α : Type) → (α → Prop) → Prop
| base : T PUnit (fun _ ↦ True)
| cheat : T (PUnit → Prop) (fun _ ↦ False)
