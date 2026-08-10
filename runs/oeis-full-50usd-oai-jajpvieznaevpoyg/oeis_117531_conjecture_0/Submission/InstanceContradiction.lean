import FormalConjectures.Util.ProblemImports
#synth CharP Nat 1
#synth Nontrivial Nat
example : False := by
  exact CharP.cast_eq_zero_iff Nat 1 1 |>.mp ?_
