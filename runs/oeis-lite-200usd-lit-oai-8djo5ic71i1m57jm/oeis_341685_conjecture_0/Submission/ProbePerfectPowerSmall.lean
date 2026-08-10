import FormalConjectures.Util.ProblemImports
open Nat

example : Nat.IsPerfectPower 8 := by native_decide
example : Nat.IsPerfectPower 9 := by native_decide
example : ¬ Nat.IsPerfectPower 12 := by native_decide

example : (Nat.IsPerfectPower 8 ↔ 8 > 1 ∧ (8).primeFactors.gcd (8).factorization > 1) := Nat.isPerfectPower_iff_factorization_gcd 8
example : False := by
  have h : Nat.IsPerfectPower 12 ↔ 12 > 1 ∧ (12).primeFactors.gcd (12).factorization > 1 := Nat.isPerfectPower_iff_factorization_gcd 12
  native_decide at h
