import FormalConjectures.Util.ProblemImports
#check schnirelmannDensity_setOf_prime
#check schnirelmannDensity_eq_zero_of_one_notMem
#check schnirelmannDensity_pos_iff
#check schnirelmannDensity_eq_zero_iff
#check Set.Infinite
#check Nat.infinite_setOf_prime
example : False := by
  have h0 := schnirelmannDensity_setOf_prime
  have hinf := Nat.infinite_setOf_prime
  exact?
