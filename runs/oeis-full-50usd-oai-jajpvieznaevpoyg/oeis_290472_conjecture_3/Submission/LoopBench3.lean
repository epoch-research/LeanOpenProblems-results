import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def checkAt (i : ℕ) : Bool := (i+1) > i

def loopRange (lo len : ℕ) : Bool :=
  match len with
  | 0 => true
  | 1 => checkAt lo
  | n + 2 =>
    let len := n + 2
    let half := len / 2
    loopRange lo half && loopRange (lo+half) (len-half)
termination_by len
decreasing_by all_goals omega

theorem bench : loopRange 0 1000000 = true := by decide
#print axioms bench
