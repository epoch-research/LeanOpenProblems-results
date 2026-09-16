import FormalConjectures.Util.ProblemImports
def count_sixes (m : ℕ) : ℕ := (Nat.digits 10 m).count 6

def main : IO Unit := do
  let l := (List.range 2000).filter (fun k => count_sixes (Nat.factorial k) == 24)
  IO.println l
