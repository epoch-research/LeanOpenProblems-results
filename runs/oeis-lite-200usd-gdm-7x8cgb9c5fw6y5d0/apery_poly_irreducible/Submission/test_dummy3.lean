import Mathlib

inductive MyProof2 (P : Prop) : Type where
  | mk : P → MyProof2 P
  | dummy : MyProof2 P

instance (P : Prop) : Inhabited (MyProof2 P) where
  default := MyProof2.dummy

unsafe def unsafe_proof (P : Prop) : MyProof2 P :=
  unsafe_proof P

@[implemented_by unsafe_proof]
opaque get_proof (P : Prop) : MyProof2 P

#print axioms get_proof
