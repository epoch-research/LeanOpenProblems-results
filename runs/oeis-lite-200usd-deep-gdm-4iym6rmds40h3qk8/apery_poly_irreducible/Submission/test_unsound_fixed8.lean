import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : (α : Type) → (((α → Prop) → Prop) → Prop) → Prop
| base : T PUnit (fun H ↦ H (fun _ ↦ True))
| mk : {α : Type} → (a : (((α → Prop) → Prop) → Prop) → Prop) → T α (fun g ↦ a (fun _ ↦ True)) → T (α → Prop) a

theorem unsound {α : Type} {a : ((α → Prop) → Prop) → Prop} (t : T α a) : a (fun _ ↦ True) := by
  induction t with
  | base => exact True.intro
  | mk a' t_1 ih => exact ih

def bad {α} {a : ((α → Prop) → Prop) → Prop} (t : T α a) : a (fun _ ↦ False) → False := by
  induction t with
  | base =>
    intro h
    exact h
  | mk a' t_1 ih =>
    intro h
    have h_true : a' (fun _ ↦ True) := @unsound α (fun g ↦ a' (fun _ ↦ True)) t_1
    exact ih h_true

theorem unsound_proof_of_false : False := by
  -- We want to prove False using bad!
  -- Let's construct a term of type T (PUnit → Prop) (fun _ ↦ False).
  -- Wait! T.mk expects a : (((PUnit → Prop) → Prop) → Prop) → Prop.
  -- If we choose a = fun _ ↦ False.
  -- Then T.mk a expects the third argument to have type:
  -- T PUnit (fun g ↦ a (fun _ ↦ True))
  -- which is T PUnit (fun g ↦ False).
  -- But T.base has type:
  -- T PUnit (fun H ↦ H (fun _ ↦ True)).
  -- So we still cannot use T.base directly!
  sorry
