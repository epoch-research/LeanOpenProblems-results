import FormalConjectures.Util.ProblemImports
example : Prop := answer(sorry)
#check (answer(sorry) : Prop)
example : True := by exact (answer(sorry) : True)
example : (0:ℕ)=1 := by
  fail_if_success exact (answer(sorry) : (0:ℕ)=1)
  sorry
