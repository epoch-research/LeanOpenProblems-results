import FormalConjectures.Util.ProblemImports

instance infFin1 : Infinite (Fin 1) where
  not_finite f := @Fintype.false (Fin 1) infFin1 (Fintype.ofFinite (Fin 1))

#print axioms infFin1
example : False := @Fintype.false (Fin 1) infFin1 (Fintype.ofFinite (Fin 1))
#print axioms _example
