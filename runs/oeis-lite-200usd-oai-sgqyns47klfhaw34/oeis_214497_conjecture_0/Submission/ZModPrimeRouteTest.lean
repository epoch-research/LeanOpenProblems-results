import FormalConjectures.Util.ProblemImports

#synth CharP (ZMod 6) 6
#synth Finite (ZMod 6)
#synth Nontrivial (ZMod 6)
#synth NoZeroDivisors (ZMod 6)
#synth IsDomain (ZMod 6)
#synth NoZeroDivisors (ZMod 0)
#synth Nontrivial (ZMod 0)
#synth Finite (ZMod 0)
#check CharP.char_is_prime
#check CharP.char_is_prime_of_two_le
example : Nat.Prime 6 := by
  haveI : CharP (ZMod 6) 6 := inferInstance
  exact CharP.char_is_prime (ZMod 6) 6
