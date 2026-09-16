import FormalConjectures.Util.ProblemImports

def A331343 (n : ℕ) : ℕ :=
  let L : ℕ := (Finset.Ico 1 (n + 1)).lcm id
  (Finset.Ico 1 (n + 1)).sum fun k : ℕ ↦ (L / k) * (2 ^ (k - 1) - 1)

#eval A331343 2
#eval A331343 4
#eval A331343 6
