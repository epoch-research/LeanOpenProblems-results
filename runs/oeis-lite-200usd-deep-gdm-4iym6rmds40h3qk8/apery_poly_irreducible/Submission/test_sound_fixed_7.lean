import FormalConjectures.Util.ProblemImports

inductive T : (α : Type) → (((α → Prop) → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun H ↦ H (fun _ ↦ True))
| cheat : T (PUnit.{1} → Prop) (fun H ↦ (H (fun _ ↦ True) → False) → False)

theorem unsound {α : Type} {a : ((α → Prop) → Prop) → Prop} (t : T α a) : a (fun _ ↦ True) := by
  induction t with
  | base => exact True.intro
  | cheat =>
    intro h
    exact h True.intro
