import FormalConjectures.Util.ProblemImports

instance instInfFin0 : Infinite (Fin 0) where
  not_finite := by
    intro hfin
    exact Infinite.false (α:=Fin 0) (inferInstanceAs (Infinite (Fin 0)))

example : False := Infinite.false (α:=Fin 0) (inferInstanceAs (Infinite (Fin 0)))
#print axioms instInfFin0
#print axioms _example
