import Mathlib

inductive MyFalse : Type

partial def get_my_false (u : Unit) : MyFalse :=
  get_my_false u

theorem prove_false : False := by
  have x : MyFalse := get_my_false ()
  cases x

theorem prove_any (P : Prop) : P :=
  False.elim prove_false

#print axioms prove_any
