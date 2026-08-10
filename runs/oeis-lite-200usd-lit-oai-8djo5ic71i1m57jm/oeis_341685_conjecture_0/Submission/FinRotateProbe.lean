import FormalConjectures.Util.ProblemImports

#check lt_finRotate_of_ne_last
example : False := by
  have h := lt_finRotate_of_ne_last (n := 1) (i := (0 : Fin 2)) (by decide)
  norm_num [finRotate] at h
