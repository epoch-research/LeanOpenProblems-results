import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000

def checkAt (i : ℕ) : Bool := (i+1) > i

def loopRange (lo len : ℕ) : Bool :=
  match len with
  | 0 => true
  | 1 => checkAt lo
  | _ =>
    let half := len / 2
    loopRange lo half && loopRange (lo+half) (len-half)
termination_by len

theorem bench : loopRange 0 1000000 = true := by decide
