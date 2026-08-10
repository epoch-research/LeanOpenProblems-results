import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → (((α → Prop) → Prop) → Prop) → Prop
| base : T PUnit.{1} (fun H ↦ H (fun _ ↦ True))
| mk : {α : Type} → (a : (((α → Prop) → Prop) → Prop) → Prop) → T α (fun H ↦ a (fun _ ↦ True)) → T (α → Prop) a
| cheat : T (PUnit.{1} → Prop) (fun H ↦ (H (fun _ ↦ True) → False) → False)

theorem unsound {α : Type} {a : (((α → Prop) → Prop) → Prop)} (t : T α a) : a (fun _ ↦ True) := by
  induction t with
  | base => exact True.intro
  | mk a' t_1 ih => exact ih
  | cheat =>
    intro h
    exact h True.intro

theorem index_eq {a : (((PUnit.{1} → Prop) → Prop) → Prop)} (t : T PUnit.{1} a) : a = (fun H ↦ H (fun _ ↦ True)) := by
  cases t with
  | base => rfl

def bad_direct {a} (t : T (PUnit.{1} → Prop) a) (h : a (fun _ ↦ False)) : False := by
  cases t with
  | mk a' t_1 =>
    have h_eq : (fun H ↦ a' (fun _ ↦ True)) = (fun H ↦ H (fun _ ↦ True)) := index_eq t_1
    have h_eval := congrFun h_eq (fun _ ↦ False)
    have h_eval_simp : a' (fun _ ↦ True) = False := h_eval
    have h_true : a' (fun _ ↦ True) := unsound t_1
    exact h_eval_simp ▸ h_true
  | cheat =>
    change ((False → False) → False) at h
    exact h (fun x : False ↦ x)

theorem unsound_proof_of_false : False := by
  have t_cheat : T (PUnit.{1} → Prop) (fun H ↦ (H (fun _ ↦ True) → False) → False) := T.cheat
  have h_arg : (fun H : ((PUnit.{1} → Prop) → Prop) → Prop ↦ (H (fun _ ↦ True) → False) → False) (fun _ ↦ False) := by
    change (False → False) → False
    exact fun f ↦ f (fun x : False ↦ x)
  exact bad_direct t_cheat h_arg

