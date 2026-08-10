import FormalConjectures.Util.ProblemImports

#check CharP.char_is_prime_of_two_le
#check ZMod
#check ZMod.instCommRing
#check ZMod.instCharP
#check NoZeroDivisors (ZMod 4)
#check (inferInstance : CharP (ZMod 4) 4)

-- This should fail exactly because `ZMod 4` has zero divisors.
example : Nat.Prime 4 := by
  -- exact CharP.char_is_prime_of_two_le (R := ZMod 4) 4 (by norm_num)
  fail_if_success exact CharP.char_is_prime_of_two_le (R := ZMod 4) 4 (by norm_num)
  norm_num
