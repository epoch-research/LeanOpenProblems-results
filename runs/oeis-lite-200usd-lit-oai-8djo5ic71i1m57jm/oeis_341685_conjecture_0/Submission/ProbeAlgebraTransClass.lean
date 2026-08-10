import FormalConjectures.Util.ProblemImports
#print Algebra.Transcendental
#check Algebra.Transcendental.transcendental
#check Algebra.Transcendental.of_ringHom_of_comp_eq
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth Algebra.Transcendental ℚ (Padic 3)
