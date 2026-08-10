import FormalConjectures.Util.ProblemImports
set_option exponentiation.threshold 1000
example (h4 : 586 % 4 = 3) (h49 : 2^586 ≡ 586 + 13573 [MOD 49]) : False := by
  norm_num at h4
example (h4 : 587 % 4 = 3) (h49 : 2^587 ≡ 587 + 13573 [MOD 49]) : False := by
  norm_num [Nat.ModEq] at h49
