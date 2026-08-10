import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def advance (p fuel : Nat) : Nat :=
  match fuel with
  | 0 => p
  | fuel+1 => advance ((p * 2) % 550172) fuel
example : advance 1 2000 = 254636 := by decide
example : advance 1 5000 = 524108 := by decide
