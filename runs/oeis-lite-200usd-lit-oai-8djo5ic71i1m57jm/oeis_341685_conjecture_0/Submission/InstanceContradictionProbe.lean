import FormalConjectures.Util.ProblemImports
open Nat BigOperators
instance : Fact (Nat.Prime 3) := by constructor; norm_num

#synth Nontrivial (Padic 3)
#synth Subsingleton (Padic 3)
#synth Infinite (Padic 3)
#synth Finite (Padic 3)
#synth Fintype (Padic 3)
#synth CharP (Padic 3) 0
#synth CharP (Padic 3) 1
#synth CharZero (Padic 3)
#synth Module.Finite ℚ (Padic 3)
#synth Algebra.IsAlgebraic ℚ (Padic 3)

example : False := by
  first | exact false_of_nontrivial_of_subsingleton (Padic 3)
        | exact not_finite (Padic 3)
        | exact CharP.false_of_nontrivial_of_char_one (R := Padic 3)
