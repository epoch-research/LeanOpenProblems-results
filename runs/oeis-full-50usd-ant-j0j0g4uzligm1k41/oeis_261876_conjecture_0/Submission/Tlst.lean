import FormalConjectures.Util.ProblemImports
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def LL : List (Nat×Nat×Nat) := [(1,1,66), (1,1,159), (1,1,210), (1,1,255), (1,3,27), (1,3,53), (1,3,258), (1,3,262), (1,6,35), (1,6,261)]
example : (LL.map (fun p => if IsSquare ((5*p.1^2+7*p.2.1^2+9*p.2.2^2)*p.2.1*p.2.2) then (1:Nat) else 0)).sum = 0 := by decide +kernel
