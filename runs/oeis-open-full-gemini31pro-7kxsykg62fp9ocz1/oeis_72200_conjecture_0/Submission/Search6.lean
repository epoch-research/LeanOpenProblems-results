import FormalConjectures.Util.ProblemImports

def count_sixes (m : ℕ) : ℕ := (Nat.digits 10 m).count 6

def search_loop : ℕ → ℕ
  | 0 => 0
  | k + 1 => if count_sixes (Nat.factorial (k + 1)) == 24 then k + 1 else search_loop k

#eval search_loop 2000
