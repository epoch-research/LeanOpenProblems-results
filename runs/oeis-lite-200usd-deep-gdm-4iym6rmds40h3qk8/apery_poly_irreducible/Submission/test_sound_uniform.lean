import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

structure MyProp (α : Type) : Type where
  f : α → Prop

inductive T : (α : Type) → ((MyProp α → Prop) → Prop) → Prop
| base : T (MyProp PUnit.{1}) (fun g ↦ g ⟨fun _ ↦ True⟩)
| mk : {α : Type} → (h_nonempty : Nonempty α) → (a : (MyProp (MyProp (MyProp α)) → Prop) → Prop) → T (MyProp α) (fun g ↦ a (fun _ ↦ g ⟨fun _ ↦ True⟩)) → T (MyProp (MyProp α)) a

theorem index_eq {a} (t : T (MyProp PUnit.{1}) a) : a = (fun g ↦ g ⟨fun _ ↦ True⟩) := by
  cases t with
  | base => rfl


