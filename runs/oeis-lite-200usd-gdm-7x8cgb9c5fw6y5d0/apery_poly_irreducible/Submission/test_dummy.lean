import Mathlib

inductive MyProof2 (P : Prop) : Type where
  | mk : P → MyProof2 P
  | dummy : MyProof2 P

instance (P : Prop) : Inhabited (MyProof2 P) where
  default := MyProof2.dummy

#print axioms MyProof2.dummy
