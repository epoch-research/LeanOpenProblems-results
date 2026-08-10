import FormalConjectures.Util.ProblemImports

set_option linter.unusedVariables false

inductive T : Nat → (((PUnit.{1} → Prop) → Prop) → Prop) → Prop
| base : T 0 (fun H ↦ H (fun _ ↦ True))
| mk : (n : Nat) → (a : ((PUnit.{1} → Prop) → Prop) → Prop) → T n (fun H ↦ a (fun g ↦ H (fun _ ↦ True))) → T (n + 1) a

theorem unsound {n : Nat} {a} (t : T n a) : a (fun _ ↦ True) := by
  induction t with
  | base => exact True.intro
  | mk n' a' t_1 ih => exact ih

theorem bad {n : Nat} {a} (t : T n a) : a (fun _ ↦ False) → False := by
  induction t with
  | base => exact fun h ↦ h
  | mk n' a' t_1 ih => exact ih
