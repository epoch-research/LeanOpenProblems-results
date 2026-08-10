import FormalConjectures.Util.ProblemImports
open BigOperators Nat
#check Nat.choose_modEq_choose_mod_mul_choose_div_nat
#check Nat.ModEq
#check Nat.ModEq.mul
#check Nat.ModEq.pow
example (n k : ℕ) : n.choose k ≡ (n % 3).choose (k % 3) * (n / 3).choose (k / 3) [MOD 3] := by
  exact Nat.choose_modEq_choose_mod_mul_choose_div_nat (by norm_num : Nat.Prime 3)
