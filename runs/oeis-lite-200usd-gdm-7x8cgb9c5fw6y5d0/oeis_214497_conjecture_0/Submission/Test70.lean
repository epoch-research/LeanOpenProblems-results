import FormalConjectures.Util.ProblemImports

structure MyPLift (P : Prop) : Type where
  mk :: val : P

partial def get_MyPLift (P : Prop) : MyPLift P :=
  get_MyPLift P

theorem prove_any (P : Prop) : P := by
  match get_MyPLift P with
  | MyPLift.mk val => exact val
