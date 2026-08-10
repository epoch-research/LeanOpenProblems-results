import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth Subsingleton (Ring (Padic 3))
#synth Subsingleton (CommRing (Padic 3))
#synth Subsingleton (Field (Padic 3))
#synth Subsingleton (Algebra ℚ (Padic 3))
#synth Unique (Algebra ℚ (Padic 3))
#check RingHom.ext_rat
#check Rat.ringHom_ext
#check RingHom.toRatAlgebra
#check DivisionRing.toRatAlgebra
example (A B : Algebra ℚ (Padic 3)) : A = B := by
  apply Subsingleton.elim
