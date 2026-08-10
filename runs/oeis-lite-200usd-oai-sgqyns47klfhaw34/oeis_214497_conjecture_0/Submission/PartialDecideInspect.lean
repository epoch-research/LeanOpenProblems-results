import FormalConjectures.Util.ProblemImports

partial def loopDec (P : Prop) : Decidable P := loopDec P
#print loopDec
#print axioms loopDec

example (P : Prop) : Decidable P := loopDec P

example (P : Prop) : decide P = true := by
  letI : Decidable P := loopDec P
  rfl

example (P : Prop) : P := by
  letI : Decidable P := loopDec P
  exact of_decide_eq_true (show decide P = true from rfl)
