import FormalConjectures.Util.ProblemImports

example : False := by
  have h := prod_primeFactors_factorization_apply (n := 0) (p := 2) (by norm_num : Nat.Prime 2) (f := fun _ _ => 1)
  norm_num at h

example : False := by
  have h := Nat.squarefreePart_mul_squarePart 0
  norm_num [Nat.squarefreePart, Nat.squarePart] at h

example : False := by
  have h := Nat.isPerfectPower_iff_factorization_gcd 0
  norm_num [Nat.IsPerfectPower] at h
