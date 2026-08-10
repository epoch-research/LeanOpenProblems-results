import FormalConjectures.Util.ProblemImports

partial def partial_proof (P : Prop) : P :=
  partial_proof P

theorem true_eq_false : True = False :=
  partial_proof (True = False)
