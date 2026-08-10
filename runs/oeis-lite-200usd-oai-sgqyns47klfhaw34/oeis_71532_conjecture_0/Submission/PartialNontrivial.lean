import FormalConjectures.Util.ProblemImports

partial def badNontrivial (_ : Unit) : Nontrivial (ZMod 1) := badNontrivial ()

#print axioms badNontrivial

instance : Nontrivial (ZMod 1) := badNontrivial ()

example : False := by
  exact CharP.false_of_nontrivial_of_char_one (R := ZMod 1)

#print axioms _example
