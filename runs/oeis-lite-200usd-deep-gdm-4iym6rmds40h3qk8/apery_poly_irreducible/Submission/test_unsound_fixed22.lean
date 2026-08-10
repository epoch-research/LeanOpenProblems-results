import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → (((α → Prop) → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun H ↦ H (fun _ ↦ True))
| cheat : T (PUnit.{1} → Prop) (fun H ↦ (H (fun _ ↦ True) → False) → False)

def bad {α} {a : ((α → Prop) → Prop) → Prop} (t : T α a) : a (fun _ ↦ False) → False := by
  induction t with
  | base =>
    intro h
    exact h
  | cheat =>
    intro h
    have h_eq : (((fun (_ : (PUnit.{1} → Prop) → Prop) ↦ False) (fun (_ : PUnit.{1} → Prop) ↦ True) → False) → False) = ((False → False) → False) := rfl
    rw [h_eq] at h
    exact h (fun (h_false : False) ↦ h_false)

theorem unsound_proof_of_false : False := by
  have t_false : T (PUnit.{1} → Prop) (fun H ↦ (H (fun (_ : PUnit.{1} → Prop) ↦ True) → False) → False) := T.cheat
  have h_arg : (fun (H : ((PUnit.{1} → Prop) → Prop) → Prop) ↦ (H (fun (_ : PUnit.{1} → Prop) ↦ True) → False) → False) (fun (_ : (PUnit.{1} → Prop) → Prop) ↦ False) := by
    have h_eq : (fun (H : ((PUnit.{1} → Prop) → Prop) → Prop) ↦ (H (fun (_ : PUnit.{1} → Prop) ↦ True) → False) → False) (fun (_ : (PUnit.{1} → Prop) → Prop) ↦ False) = ((False → False) → False) := rfl
    rw [h_eq]
    exact fun h ↦ h (fun h_false ↦ h_false)
  exact bad t_false h_arg
