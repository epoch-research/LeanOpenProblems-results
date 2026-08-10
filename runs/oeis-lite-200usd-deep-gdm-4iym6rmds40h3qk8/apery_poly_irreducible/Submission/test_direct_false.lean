import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → (((α → Prop) → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun H ↦ H (fun _ ↦ True))
| cheat : T PUnit.{1} (fun H ↦ H (fun _ ↦ True)) → T (PUnit.{1} → Prop) (fun H ↦ (H (fun _ ↦ True) → False) → False)

def bad {α} {a} (t : T α a) : a (fun (_ : α → Prop) ↦ False) → False := by
  induction t with
  | base =>
    intro h
    exact h
  | cheat t_1 ih =>
    intro h
    exact h ih

def test_h : (False → False) → False := fun h_f_f ↦ h_f_f (fun x ↦ x)

