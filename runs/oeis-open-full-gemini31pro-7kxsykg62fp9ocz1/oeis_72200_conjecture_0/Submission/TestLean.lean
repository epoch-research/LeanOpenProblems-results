import FormalConjectures.Util.ProblemImports

def count_sixes (m : ℕ) : ℕ := (Nat.digits 10 m).count 6

#eval count_sixes (Nat.factorial 138)
#eval count_sixes (Nat.factorial 143)
