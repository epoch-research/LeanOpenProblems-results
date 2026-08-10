import FormalConjectures.Util.ProblemImports

#check (answer(sorry) : Prop)
#check (show Prop from answer(sorry))
#eval (show Prop from answer(sorry))

example : True := by
  exact answer(sorry)

example : False := by
  fail_if_success exact answer(sorry)
  fail_if_success exact (show False from answer(sorry))
  guard_target = False
  sorry

example (P : Prop) : P := by
  let Q : Prop := answer(sorry)
  have hQ : Q := by
    -- Q is definitionally True?
    unfold Q
    trivial
  fail_if_success exact hQ
  sorry
