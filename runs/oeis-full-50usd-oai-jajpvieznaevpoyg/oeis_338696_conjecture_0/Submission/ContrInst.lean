import FormalConjectures.Util.ProblemImports
#synth Infinite Nat
#synth Finite Nat
#synth Subsingleton Nat
#synth Nontrivial PUnit
#synth CharP Nat 1
example : False := by
  exact Finite.false (α := Nat) inferInstance
