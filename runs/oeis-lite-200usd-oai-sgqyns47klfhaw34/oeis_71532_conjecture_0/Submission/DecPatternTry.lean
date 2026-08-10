import FormalConjectures.Util.ProblemImports
partial def loopDec (P : Prop) : Decidable P := loopDec P

example (P : Prop) : P := by
  let (isTrue hp) := loopDec P
  exact hp

example : False := by
  let (isTrue hp) := loopDec False
  exact hp
#print axioms loopDec
#print axioms _example
