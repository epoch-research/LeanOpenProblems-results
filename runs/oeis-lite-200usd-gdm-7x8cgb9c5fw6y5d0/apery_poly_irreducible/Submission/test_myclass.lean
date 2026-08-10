import Mathlib

inductive MyClass (α : Prop) where
  | mk1 : (PLift α → MyClass α) → MyClass α
deriving Nonempty

#print axioms MyClass.instNonemptyMyClass
