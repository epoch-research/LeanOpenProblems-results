import FormalConjectures.Util.ProblemImports
#check Nat.prime_iff
#check Nat.not_prime_one
#check Nat.not_prime_zero
#check Nat.Prime.ne_one
#check Nat.Prime.two_le
#check Nat.prime_two
#check Nat.prime_iff_prime_int
example : ¬ Nat.Prime 4 := by norm_num
example : Nat.Prime 2741 := by norm_num
example : ¬ Nat.Prime 2196 := by norm_num
