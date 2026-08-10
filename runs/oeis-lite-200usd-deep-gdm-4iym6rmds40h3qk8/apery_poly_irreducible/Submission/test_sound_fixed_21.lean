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
    have h_true : a' (fun _ ↦ True) := unsound t_1
    exact ih h_true
  | cheat =>
    intro h
    -- h has type ((fun _ ↦ False) (fun _ ↦ False) → False) → False.
    -- which is (False → False) → False.
    -- So we can apply h to the identity function!
    exact h (fun x ↦ x)

theorem unsound_proof_of_false : False := by
  have t_false : T (PUnit.{1} → Prop) (fun H ↦ (H (fun _ ↦ False) → False) → False) := T.cheat
  have h_arg : (fun H ↦ (H (fun _ ↦ False) → False) → False) (fun _ ↦ False) := by
    -- goal: ((fun _ ↦ False) (fun _ ↦ False) → False) → False
    -- which is (False → False) → False
    intro h
    exact h (fun x ↦ x)
  exact bad t_false h_arg
