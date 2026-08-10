import FormalConjectures.Util.ProblemImports

def Good (P : Prop) : Decidable P → Prop
| .isTrue _ => True
| .isFalse _ => False

partial def goodDec (P : Prop) : {d : Decidable P // Good P d} := goodDec P
#print axioms goodDec

example (P : Prop) : P := by
  rcases goodDec P with ⟨d, hd⟩
  cases d with
  | isTrue h => exact h
  | isFalse h => cases hd
#print axioms PartialSubtypeDecExp._example_1
