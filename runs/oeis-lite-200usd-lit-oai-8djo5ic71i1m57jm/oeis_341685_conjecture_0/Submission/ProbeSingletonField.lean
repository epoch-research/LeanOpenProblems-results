import FormalConjectures.Util.ProblemImports
#synth Field PUnit
#synth Field Unit
#synth DivisionRing PUnit
example : False := by
  haveI : Field PUnit := inferInstance
  exact zero_ne_one (Subsingleton.elim (0 : PUnit) (1 : PUnit))
