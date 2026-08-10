import FormalConjectures.Util.ProblemImports
#check Nat.one_lt_maxPrimeFac_iff
#check Nat.isPerfectPower_iff_factorization_gcd
#check Nat.IsPerfectPower.decide
#eval Nat.maxPrimeFac 0
#eval Nat.maxPrimeFac 1
#eval Nat.maxPrimeFac 2
example : Nat.maxPrimeFac 1 = 0 := by native_decide
example : Nat.maxPrimeFac 0 = 0 := by native_decide
example : False := by
  have h := (Nat.one_lt_maxPrimeFac_iff 0)
  norm_num at h
example : False := by
  have h := (Nat.isPerfectPower_iff_factorization_gcd 0)
  norm_num at h
