import FormalConjectures.Util.ProblemImports

instance : CharP PUnit 1 where
  cast_eq_zero_iff x := by
    constructor
    · intro _; exact one_dvd x
    · intro _; cases (x : PUnit); rfl

#check (CharP.char_is_prime_of_two_le PUnit 1 (by norm_num) : Nat.Prime 1)
theorem prime_one_bad : Nat.Prime 1 := CharP.char_is_prime_of_two_le PUnit 1 (by norm_num)
#print prime_one_bad
#print axioms prime_one_bad

theorem false_from_prime_one_bad : False := Nat.not_prime_one prime_one_bad
#print axioms false_from_prime_one_bad
