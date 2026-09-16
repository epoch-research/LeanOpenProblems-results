import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ := (bernoulli (2 * n) / (2 * n * (2 * n - 1))).den

#eval a 7
#eval a 7 / 12
#eval Nat.Prime (a 7 / 12)
