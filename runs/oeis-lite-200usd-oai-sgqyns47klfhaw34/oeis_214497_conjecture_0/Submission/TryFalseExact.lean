import FormalConjectures.Util.ProblemImports

example : False := by
  first | exact False.elim (by contradiction)
        | exact CharP.false_of_nontrivial_of_char_one (R := ZMod 1)
        | exact false_of_nontrivial_of_subsingleton (ZMod 1)
        | exact false_of_nontrivial_of_subsingleton PUnit
        | exact false_of_nontrivial_of_subsingleton Empty
        | exact false_of_nontrivial_of_subsingleton False
        | exact false_of_nontrivial_of_subsingleton True
