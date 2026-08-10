import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → (((α → Prop) → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun H ↦ H (fun _ ↦ True))
| mk : {α : Type} → (a : (((α → Prop) → Prop) → Prop) → Prop) → T α (fun H ↦ a (fun _ ↦ True)) → T (α → Prop) a
| cheat : T (PUnit.{1} → Prop) (fun H ↦ (H (fun _ ↦ False) → False) → False)

theorem unsound {α : Type} {a : (((α → Prop) → Prop) → Prop)} (t : T α a) : a (fun _ ↦ True) := by
  induction t with
  | base => exact True.intro
  | mk a' t_1 ih => exact ih
  | cheat =>
    intro h
    exact h True.intro

def bad {α} {a : (((α → Prop) → Prop) → Prop)} (t : T α a) : a (fun _ ↦ False) → False := by
  induction t with
  | base =>
    intro h
    exact h
  | mk a' t_1 ih =>
    intro h
    have h_true : a' (fun _ ↦ True) := @unsound α (fun H ↦ a' (fun _ ↦ True)) t_1
    exact ih h_true
  | cheat =>
    intro h
    exact h (fun x ↦ x)

theorem unsound_proof_of_false : False := by
  have t_false : T (PUnit.{1} → Prop) (fun (H : ((PUnit.{1} → Prop) → Prop) → Prop) ↦ (H (fun (_ : PUnit.{1} → Prop) ↦ False) → False) → False) := T.cheat
  have h_arg : (fun (H : ((PUnit.{1} → Prop) → Prop) → Prop) ↦ (H (fun (_ : PUnit.{1} → Prop) ↦ False) → False) → False) (fun (_ : (PUnit.{1} → Prop) → Prop) ↦ False) := by
    have h_eq : (fun (H : ((PUnit.{1} → Prop) → Prop) → Prop) ↦ (H (fun (_ : PUnit.{1} → Prop) ↦ False) → False) → False) (fun (_ : (PUnit.{1} → Prop) → Prop) ↦ False) = ((False → False) → False) := rfl
    rw [h_eq]
    intro h
    exact h (fun x ↦ x)
  exact bad t_false h_arg
