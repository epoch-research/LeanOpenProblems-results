import FormalConjectures.Util.ProblemImports

#check CharP
#print CharP
#synth CharP PUnit 1
#synth CharP PUnit 2
#synth NoZeroDivisors PUnit
#synth NonAssocSemiring PUnit
example : Nat.Prime 2 := by
  haveI : CharP PUnit 2 := inferInstance
  exact CharP.char_is_prime_of_two_le PUnit 2 (by norm_num)
