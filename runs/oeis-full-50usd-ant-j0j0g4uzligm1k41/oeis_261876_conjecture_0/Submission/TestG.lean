import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def theta : Nat := (List.range 264).foldl (fun acc k => acc + 2^(20*k*k)) 0
def c4 (n : Nat) : Nat := (theta^4 >>> (20*n)) &&& (2^20 - 1)
example : c4 69383 = 34692 := by rfl
