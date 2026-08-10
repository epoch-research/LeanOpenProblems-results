import FormalConjectures.Util.ProblemImports

example : False := by
  have h := Nat.prime_maxPrimeFac_of_one_lt 2 (by norm_num : 1 < 2)
  norm_num [Nat.maxPrimeFac] at h

example : False := by
  have h := Nat.maxPrimeFac_eq_of_dvd_of_le (n := 4) (p := 2) (by norm_num : Nat.Prime 2) (by norm_num : 2 ∣ 4) (by norm_num)
  norm_num [Nat.maxPrimeFac] at h
