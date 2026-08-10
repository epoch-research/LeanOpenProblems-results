import FormalConjectures.Util.ProblemImports

example : False := by
  first | exact CharP.false_of_nontrivial_of_char_one (R := ZMod 1)
        | exact false_of_nontrivial_of_subsingleton (ZMod 1)
        | exact false_of_nontrivial_of_subsingleton PUnit
        | exact false_of_nontrivial_of_subsingleton Empty
        | exact false_of_nontrivial_of_subsingleton Unit

#print axioms false_of_nontrivial_of_subsingleton
