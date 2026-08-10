import FormalConjectures.Util.ProblemImports

set_option pp.all true

inductive T : (α : Type) → (((α → Prop) → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun H ↦ H (fun _ ↦ True))
| cheat : T (PUnit.{1} → Prop) (fun H ↦ H (fun _ ↦ True) → False)
#check @T
