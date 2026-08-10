import FormalConjectures.Util.ProblemImports
#synth Infinite Nat
#synth Finite Nat
#synth Fintype Nat
#synth Finite Int
#synth Infinite Int
#synth Finite Prop
#synth Fintype Prop
#synth Infinite Prop
example : False := by
  haveI := (inferInstance : Infinite Nat)
  -- if Finite Nat existed
  fail_if_success exact Infinite.nat_not_finite
  sorry
