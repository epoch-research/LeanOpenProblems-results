import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → (((α → Prop) → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun H ↦ H (fun _ ↦ True))
| cheat : T (PUnit.{1} → Prop) (fun H ↦ (H (fun _ ↦ True) → False) → False)

def bad {α} {a} (t : T α a) : a (fun _ ↦ False) → False := by
  induction t with
  | base =>
    intro h
    exact h
  | cheat =>
    intro h
    -- h has type ((fun (_ : (PUnit.{1} → Prop) → Prop) ↦ False) (fun (_ : PUnit.{1} → Prop) ↦ True) → False) → False
    -- which is definitionally equal to (False → False) → False.
    -- Let's change its type!
    change ((False → False) → False) at h
    exact h (fun x ↦ x)

theorem unsound_proof_of_false : False := by
  have t_false : T (PUnit.{1} → Prop) (fun (H : ((PUnit.{1} → Prop) → Prop) → Prop) ↦ (H (fun (_ : PUnit.{1} → Prop) ↦ True) → False) → False) := T.cheat
  have h_arg : (fun (H : ((PUnit.{1} → Prop) → Prop) → Prop) ↦ (H (fun (_ : PUnit.{1} → Prop) ↦ True) → False) → False) (fun (_ : (PUnit.{1} → Prop) → Prop) ↦ False) := by
    change (False → False) → False
    exact fun h ↦ h (fun x ↦ x)
  exact bad t_false h_arg
