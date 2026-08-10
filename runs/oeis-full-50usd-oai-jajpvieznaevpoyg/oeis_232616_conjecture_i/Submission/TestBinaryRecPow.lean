import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def powModBR (a m e : Nat) : Nat :=
  Nat.binaryRec (1 % m) (fun b _ rec =>
    let sq := (rec * rec) % m
    if b then (sq * a) % m else sq) e

#eval powModBR 2 137543 29400
example : powModBR 2 137543 29400 = 1 := by decide
example : powModBR 2 550172 82496875 = 178064 := by native_decide
