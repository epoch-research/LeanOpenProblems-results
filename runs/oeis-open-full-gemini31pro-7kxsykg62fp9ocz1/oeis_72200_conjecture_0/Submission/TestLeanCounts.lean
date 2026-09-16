import FormalConjectures.Util.ProblemImports

def count_sixes (m : ℕ) : ℕ := (Nat.digits 10 m).count 6

#eval (List.range 21 |>.map (fun i => count_sixes (Nat.factorial (130 + i))))
