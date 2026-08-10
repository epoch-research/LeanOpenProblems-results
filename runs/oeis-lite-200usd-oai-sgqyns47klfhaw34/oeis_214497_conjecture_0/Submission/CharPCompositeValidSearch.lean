import FormalConjectures.Util.ProblemImports

-- All of these should fail for composite finite rings.
#synth NoZeroDivisors (ZMod 4)
#synth NoZeroDivisors (ZMod 8)
#synth IsDomain (ZMod 4)
#synth NoZeroDivisors (Fin 1)
#synth NonAssocSemiring (Fin 1)
#synth CharP (Fin 1) 1
#synth NoZeroDivisors (ULift PUnit)
#synth CharP (ULift PUnit) 1

-- Prime characteristic cases should be fine.
#synth NoZeroDivisors (ZMod 2)
#synth CharP (ZMod 2) 2
example : Nat.Prime 2 := CharP.char_is_prime_of_two_le (ZMod 2) 2 (by norm_num)
#print axioms (CharP.char_is_prime_of_two_le (ZMod 2) 2 (by norm_num) : Nat.Prime 2)
