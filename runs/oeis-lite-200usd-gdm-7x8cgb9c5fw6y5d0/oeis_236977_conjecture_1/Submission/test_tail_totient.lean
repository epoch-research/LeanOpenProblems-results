import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 200000

open Nat

def totient_loop (n : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | fuel + 1, idx, acc =>
    if idx = 0 then acc
    else
      let acc' := if idx.Coprime n then acc + 1 else acc
      totient_loop n fuel (idx - 1) acc'

def totient_fast (n : Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 1
  else totient_loop n n (n - 1) 0

theorem test_decide : totient_fast 100000 = 40000 := by
  decide
