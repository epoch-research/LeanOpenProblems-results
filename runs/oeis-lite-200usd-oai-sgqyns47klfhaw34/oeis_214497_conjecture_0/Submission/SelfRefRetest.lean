import FormalConjectures.Util.ProblemImports

set_option autoImplicit true

theorem selfTarget : False := by
  exact selfTarget

mutual
  theorem selfA : False := by exact selfB
  theorem selfB : False := by exact selfA
end

#print axioms selfTarget
#print axioms selfA
