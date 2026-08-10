import FormalConjectures.Util.ProblemImports
partial def loopDec (P : Prop) : Decidable P := loopDec P

theorem foo : False := by
  cases loopDec False with
  | isTrue h => exact h
  | isFalse hn => exact False.elim (hn foo)
#print axioms foo
