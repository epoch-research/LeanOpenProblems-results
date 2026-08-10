import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def scan (k p fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel+1 =>
    let p' := (p * 2) % 550172
    let r := (p' + 550172 - (k % 550172)) % 550172
    (r != 13573) && scan (k+1) p' fuel

def advance (p fuel : Nat) : Nat :=
  match fuel with
  | 0 => p
  | fuel+1 => advance ((p * 2) % 550172) fuel
example : scan 1 1 4000 = true := by decide
example : advance 1 4000 = 71780 := by decide
