import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → (((α → Prop) → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun H ↦ H (fun _ ↦ True))
| cheat : T (PUnit.{1} → Prop) (fun H ↦ H (fun _ ↦ True) → False)

def bad {α} {a : ((α → Prop) → Prop) → Prop} (t : T α a) : a (fun _ ↦ False) → False := by
  induction t with
  | base =>
    intro h
    exact h
  | cheat =>
    intro h
    change (False → False) → False at h
    exact h (fun h_false ↦ h_false)

theorem unsound_proof_of_false : False := by
  have t_false : T (PUnit.{1} → Prop) (fun H ↦ H (fun _ ↦ True) → False) := T.cheat
  have h_arg : (fun H ↦ H (fun _ ↦ True) → False) (fun _ ↦ False) := by
    change False → False
    exact fun h ↦ h
  exact bad t_false h_arg
