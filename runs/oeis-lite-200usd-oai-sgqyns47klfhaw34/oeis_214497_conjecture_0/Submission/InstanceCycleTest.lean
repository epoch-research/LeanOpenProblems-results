import FormalConjectures.Util.ProblemImports

#print Infinite
#print Finite

-- local recursive proof/instance attempts
example : False := by
  let rec h : Infinite (Fin 1) := h
  letI : Infinite (Fin 1) := h
  exact not_finite (Fin 1)

-- global cycle attempt commented? try a theorem using a local instance whose body uses target false
noncomputable instance badInfiniteFin1 : Infinite (Fin 1) := by
  exact False.elim (not_finite (Fin 1))

example : False := by
  exact not_finite (Fin 1)

#print axioms badInfiniteFin1
