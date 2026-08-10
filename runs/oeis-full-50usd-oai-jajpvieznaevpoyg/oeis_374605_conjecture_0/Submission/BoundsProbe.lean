import FormalConjectures.Util.ProblemImports
example (p n : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (h1 : (2*p+3)/3 ≤ n) (h2 : n ≤ p-1) : p ≤ 100 := by
  have hp2 := hp.two_le
  omega
