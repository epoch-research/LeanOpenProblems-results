import FormalConjectures.Util.ProblemImports

inductive T : (α : Type) → ((α → Prop) → Prop) → Prop
| base : T PUnit (fun g ↦ g PUnit.unit)
| mk : {α : Type} → (a : ((α → Prop) → Prop)) → T α a → T (α → Prop) (fun g ↦ a (fun _ ↦ True))
