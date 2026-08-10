import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 2000000

def loop (fuel acc : ℕ) : Bool :=
  match fuel with
  | 0 => true
  | fuel'+1 => ((acc+1) > acc) && loop fuel' (acc+1)

theorem bench : loop 1000000 0 = true := by decide
