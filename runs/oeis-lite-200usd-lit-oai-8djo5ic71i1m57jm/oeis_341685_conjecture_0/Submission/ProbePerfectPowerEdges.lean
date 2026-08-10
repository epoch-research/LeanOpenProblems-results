import FormalConjectures.Util.ProblemImports
open Nat

example : ¬ Nat.IsPerfectPower 0 := by native_decide
example : ¬ Nat.IsPerfectPower 1 := by native_decide

example : False := by
  have h := Nat.isPerfectPower_iff_factorization_gcd 0
  have lhs : ¬ Nat.IsPerfectPower 0 := by native_decide
  have rhs : ¬ (0 > 1 ∧ (0).primeFactors.gcd (0).factorization > 1) := by native_decide
  exact? -- no contradiction

example : False := by
  have h := Nat.isPerfectPower_iff_factorization_gcd 1
  have lhs : ¬ Nat.IsPerfectPower 1 := by native_decide
  have rhs : ¬ (1 > 1 ∧ (1).primeFactors.gcd (1).factorization > 1) := by native_decide
  exact? -- no contradiction
