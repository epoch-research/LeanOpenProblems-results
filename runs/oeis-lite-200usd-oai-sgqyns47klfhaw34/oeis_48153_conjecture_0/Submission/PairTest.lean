import FormalConjectures.Util.ProblemImports

example (n k : ℕ) (hn : Odd n) (hkodd : Odd k) (hk : k + 1 < n) :
    k ^ 2 % n + (k+1) ^ 2 % n ≤ n := by
  omega
