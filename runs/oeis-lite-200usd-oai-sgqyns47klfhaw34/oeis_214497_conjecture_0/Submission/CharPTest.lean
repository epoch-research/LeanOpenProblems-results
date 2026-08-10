import FormalConjectures.Util.ProblemImports

-- Trivial semiring has characteristic 1, not arbitrary p.
example : CharP PUnit 1 := by infer_instance
#check CharP.char_is_prime_of_two_le

-- Attempt to prove 4 prime using a fake algebraic structure should fail.
example : Nat.Prime 4 := by
  -- exact CharP.char_is_prime_of_two_le (R := ZMod 4) 4 (by norm_num)
  norm_num
