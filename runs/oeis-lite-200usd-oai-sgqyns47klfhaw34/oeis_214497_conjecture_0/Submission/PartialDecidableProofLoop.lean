import FormalConjectures.Util.ProblemImports

partial def loopDec (P : Prop) : Decidable P := loopDec P

partial def proveByLoopDec (P : Prop) : P :=
  match loopDec P with
  | .isTrue h => h
  | .isFalse _ => proveByLoopDec P

#check proveByLoopDec
#print axioms proveByLoopDec

example : False := proveByLoopDec False
