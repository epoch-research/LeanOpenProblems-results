import FormalConjectures.Util.ProblemImports

def A052709 (n : ℕ) : ℕ :=
  Finset.sum (Finset.range n) fun k =>
    ((Nat.choose (2 * k) k) / (k + 1)) * (Nat.choose k (n - 1 - k))

#eval A052709 1
#eval A052709 2
#eval A052709 3
#eval A052709 4
#eval A052709 5
