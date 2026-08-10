import FormalConjectures.Util.ProblemImports
#check Nat.not_prime_zero
#check Nat.not_prime_one
example : ¬ Nat.Prime 0 := Nat.not_prime_zero
example : ¬ Nat.Prime 1 := Nat.not_prime_one
-- example : False := (Nat.not_prime_one (inferInstance : Fact (Nat.Prime 1)).out)
