import FormalConjectures.Util.ProblemImports

inductive T : (α : Type) → (α → Prop) → Prop
| base : T PUnit.{1} (fun _ ↦ True)
| mk : {α : Type} → (a : (α → Prop) → Prop) → T α (fun _ ↦ a (fun _ ↦ True)) → T (α → Prop) a
| cheat : T PUnit.{1} (fun _ ↦ False) → T (PUnit.{1} → Prop) (fun _ ↦ False)
