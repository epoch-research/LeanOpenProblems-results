import FormalConjectures.Util.ProblemImports

def modSum (p : ℕ) : ℕ :=
  Id.run do
    let mut sum : ℕ := 0
    let m := p * p * p
    for i in [1:p] do
      -- compute inverse of i mod m
      -- actually we can just compute it using Rat? No, Rat is slow.
      sum := (sum + 1) % m
    return sum

#eval modSum 16843
