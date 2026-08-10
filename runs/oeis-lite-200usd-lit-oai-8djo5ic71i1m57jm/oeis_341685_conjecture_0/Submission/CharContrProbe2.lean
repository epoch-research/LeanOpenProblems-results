import FormalConjectures.Util.ProblemImports
instance : Fact (Nat.Prime 3) := by constructor; norm_num
#synth CharZero (Padic 3)
#synth CharP (Padic 3) 0
#synth CharP (Padic 3) 1
#synth CharP (Padic 3) 3
#synth CharZero (PadicInt 3)
#synth CharP (PadicInt 3) 3
#check CharP.cast_eq_zero
#check CharP.char_is_prime_or_zero
#check CharP.false_of_nontrivial_of_char_one
example : False := by
  exact CharP.false_of_nontrivial_of_char_one (Padic 3)
