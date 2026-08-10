import FormalConjectures.Util.ProblemImports

def loop (fuel : Nat) (x : UInt64) : UInt64 :=
  match fuel with
  | 0 => x
  | f+1 => loop f (x*37 + 11)

set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem t : loop 5000 0 = loop 5000 0 := by decide
#print axioms t
