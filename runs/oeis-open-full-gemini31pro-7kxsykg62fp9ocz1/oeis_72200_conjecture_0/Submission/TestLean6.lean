import FormalConjectures.Util.ProblemImports

def count_sixes (m : ℕ) : ℕ := (Nat.digits 10 m).count 6

#eval (List.range 1000 |>.filter (fun k => count_sixes (Nat.factorial k) == 24))
