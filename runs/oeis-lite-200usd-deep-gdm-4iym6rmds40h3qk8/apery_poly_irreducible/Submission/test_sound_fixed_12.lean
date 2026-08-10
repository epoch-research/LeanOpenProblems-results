import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → (((α → Prop) → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun H ↦ H (fun _ ↦ True))
| mk : {α : Type} → (a : (((α → Prop) → Prop) → Prop) → Prop) → T α (fun H ↦ a (fun _ ↦ True)) → T (α → Prop) a
| cheat : T (PUnit.{1} → Prop) (fun H ↦ (H (fun _ ↦ False) → False) → False)

theorem unsound {α : Type} {a : (((α → Prop) → Prop) → Prop) → Prop} (t : T α a) : a (fun _ ↦ True) := by
  induction t with
  | base => exact True.intro
  | mk a' t_1 ih => exact ih
  | cheat =>
    intro h
    exact h True.intro
