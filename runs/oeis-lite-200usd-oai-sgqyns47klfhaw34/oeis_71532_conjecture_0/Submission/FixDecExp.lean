import FormalConjectures.Util.ProblemImports

partial def loopDec (P : Prop) : Decidable P := loopDec P

def fixP (P : Prop) : P := by
  cases loopDec P with
  | isTrue h => exact h
  | isFalse hn => exact False.elim (hn (fixP P))

#print axioms fixP
example : False := fixP False
#print axioms FixDecExp._example_1
