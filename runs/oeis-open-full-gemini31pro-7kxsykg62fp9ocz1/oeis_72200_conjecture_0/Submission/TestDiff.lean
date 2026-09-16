import FormalConjectures.Util.ProblemImports
def count_sixes (m : ℕ) : ℕ := (Nat.digits 10 m).count 6

def main : IO Unit := do
  let l := (List.range 150).map (fun k => count_sixes (Nat.factorial k))
  IO.println l
