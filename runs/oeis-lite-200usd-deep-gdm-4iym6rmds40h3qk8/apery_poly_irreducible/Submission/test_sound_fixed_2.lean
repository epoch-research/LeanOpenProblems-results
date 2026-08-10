import FormalConjectures.Util.ProblemImports

inductive T : (α : Type) → ((α → Prop) → Prop) → Prop
| base : T PUnit (fun g ↦ g PUnit.unit)
| mk : {α : Type} → (a : ((α → Prop) → Prop) → Prop) → T α (fun g ↦ a (fun _ ↦ True)) → T (α → Prop) a

theorem unsound {α : Type} {a : (α → Prop) → Prop} (t : T α a) : a (fun _ ↦ True) := by
  induction t with
  | base => exact True.intro
  | mk a' t_1 ih => exact ih
