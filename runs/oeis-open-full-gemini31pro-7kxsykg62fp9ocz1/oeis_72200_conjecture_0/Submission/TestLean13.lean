import FormalConjectures.Util.ProblemImports

def count_sixes (m : ℕ) : ℕ := (Nat.digits 10 m).count 6

#eval (List.range 100).map (fun k => count_sixes (Nat.factorial k))
