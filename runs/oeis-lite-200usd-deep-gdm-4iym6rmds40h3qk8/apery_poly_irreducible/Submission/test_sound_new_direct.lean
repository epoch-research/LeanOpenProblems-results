import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → ((α → Prop) → Prop) → Prop
| base : T PUnit (fun g ↦ g PUnit.unit)
| mk : {α : Type} → (h_nonempty : Nonempty α) → (a : ((α → Prop) → Prop) → Prop) → T α (fun g ↦ a (fun _ ↦ g (Classical.choice h_nonempty))) → T (α → Prop) a
