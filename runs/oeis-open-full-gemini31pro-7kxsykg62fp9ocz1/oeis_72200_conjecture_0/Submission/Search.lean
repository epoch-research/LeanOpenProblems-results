import FormalConjectures.Util.ProblemImports

def count_sixes (m : ℕ) : ℕ := (Nat.digits 10 m).count 6

def search_loop (k : ℕ) : ℕ :=
  if k > 300 then 0
  else if count_sixes (Nat.factorial k) == 24 then k
  else search_loop (k + 1)

#eval search_loop 1
