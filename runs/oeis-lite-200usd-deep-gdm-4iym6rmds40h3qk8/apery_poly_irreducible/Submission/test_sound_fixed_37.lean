import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → ((α → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun g ↦ g PUnit.unit)
| mk : {α : Type} → (a : ((α → Prop) → Prop)) → T α a → T (α → Prop) (fun g ↦ a (fun _ ↦ True))
| cheat : T PUnit.{1} (fun g ↦ g PUnit.unit) → T (PUnit.{1} → Prop) (fun g ↦ False)
