import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  Rat.den <| (Nat.divisors n).sum fun d => (1 : Rat) / (ArithmeticFunction.sigma 1 d : Rat)

def search (limit : ℕ) : List ℕ :=
  let range := List.range limit
  range.filter fun n => n > 1 && a n = 2 && n ≠ 14 && n ≠ 244 && n ≠ 494 && n ≠ 45994

#eval search 10000
