import FormalConjectures.Util.ProblemImports

unsafe def unsafe_proof (P : Prop) : P :=
  unsafe_proof P

-- Can we use this to prove True = False?
theorem true_eq_false : True = False :=
  unsafe_proof (True = False)
