import FormalConjectures.Util.ProblemImports
open Nat Classical
def reverse_nat (k : ℕ) : ℕ := ofDigits 10 (digits 10 k).reverse
example : reverse_nat 999 = 999 := by norm_num [reverse_nat, Nat.digits, Nat.digitsAux, Nat.ofDigits]
example : reverse_nat 999999999 = 999999999 := by norm_num [reverse_nat, Nat.digits, Nat.digitsAux, Nat.ofDigits]
example : ofDigits 10 ([6,8,8,9,9,1,9,9,8,8,6] : List Nat) = 68899199886 := by norm_num [Nat.ofDigits]
