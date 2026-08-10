import Mathlib

partial def my_proof (P : Prop) [Inhabited P] : P :=
  my_proof P

#print axioms my_proof
