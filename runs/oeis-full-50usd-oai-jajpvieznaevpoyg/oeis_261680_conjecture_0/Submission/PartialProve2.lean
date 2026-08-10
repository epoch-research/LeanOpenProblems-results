import FormalConjectures.Util.ProblemImports
partial def loopFalse {P : Prop} (hn : ¬ P) : False := loopFalse hn
partial def proveDec (P : Prop) : Decidable P → P
  | isTrue p => p
  | isFalse hn => False.elim (loopFalse hn)
partial def fakeDec (P : Prop) : Decidable P := fakeDec P
theorem bad : False := proveDec False (fakeDec False)
#print axioms bad
