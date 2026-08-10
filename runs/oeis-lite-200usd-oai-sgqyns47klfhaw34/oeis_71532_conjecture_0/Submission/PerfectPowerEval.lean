import FormalConjectures.Util.ProblemImports
#eval (List.range 50).filter (fun n => decide (Nat.IsPerfectPower n))
#eval (List.range 50).filter (fun n => decide (¬ Nat.IsPerfectPower n))
#check Nat.IsPerfectPower.decide
#print axioms Nat.isPerfectPower_iff_factorization_gcd
