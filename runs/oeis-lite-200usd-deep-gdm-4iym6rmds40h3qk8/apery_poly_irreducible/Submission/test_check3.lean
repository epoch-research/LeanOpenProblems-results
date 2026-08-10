import FormalConjectures.Util.ProblemImports

inductive T : (α : Type) → (((α → Prop) → Prop) → Prop) → Prop
| base : T PUnit (fun H ↦ H (fun _ ↦ True))
| mk : {α : Type} → (a : (((α → Prop) → Prop) → Prop) → Prop) → T α (fun g ↦ a (fun _ ↦ True)) → T (α → Prop) a

#check T
