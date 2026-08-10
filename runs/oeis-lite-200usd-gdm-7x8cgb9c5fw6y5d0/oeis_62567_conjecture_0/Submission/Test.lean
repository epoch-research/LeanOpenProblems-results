import FormalConjectures.Util.ProblemImports

open Nat

def reverse_nat (k : ℕ) : ℕ :=
  ofDigits 10 (digits 10 k).reverse

#eval reverse_nat 120
#eval reverse_nat 4899999987
#eval (4899999987 % 243)
#eval (reverse_nat 4899999987 % 243)
