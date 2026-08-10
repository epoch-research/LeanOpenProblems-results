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
    -- h has type a (fun _ ↦ False), where a = fun H ↦ H (fun _ ↦ True) → False
    -- So h's type is (fun H ↦ H (fun _ ↦ True) → False) (fun _ ↦ False).
    -- Let's define h' of type (False → False) → False.
    -- Since they are definitionally equal once the types are fully known, this should compile!
    have h' : (False → False) → False := h
    exact h' (fun h_false ↦ h_false)

theorem unsound_proof_of_false : False := by
  have t_false : T (PUnit.{1} → Prop) (fun (H : ((PUnit.{1} → Prop) → Prop) → Prop) ↦ H (fun (_ : (PUnit.{1} → Prop) → Prop) ↦ True) → False) := T.cheat
  have h_arg : (fun (H : ((PUnit.{1} → Prop) → Prop) → Prop) ↦ H (fun (_ : (PUnit.{1} → Prop) → Prop) ↦ True) → False) (fun (_ : ((PUnit.{1} → Prop) → Prop) → Prop) ↦ False) := by
    have h_eq : (fun (H : ((PUnit.{1} → Prop) → Prop) → Prop) ↦ H (fun (_ : (PUnit.{1} → Prop) → Prop) ↦ True) → False) (fun (_ : ((PUnit.{1} → Prop) → Prop) → Prop) ↦ False) = (False → False) := rfl
    rw [h_eq]
    exact fun h ↦ h
  exact bad t_false h_arg
