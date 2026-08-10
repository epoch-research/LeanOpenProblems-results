import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 200000

open Nat

def totient_range_acc (n : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, L, R, acc =>
    if L > R then acc
    else if L == R then
      if L.Coprime n then acc + 1 else acc
    else
      let mid := (L + R) / 2
      let acc' := totient_range_acc n fuel L mid acc
      totient_range_acc n fuel (mid + 1) R acc'

def totient_fast (n : Nat) : Nat :=
  if n == 0 then 0
  else if n == 1 then 1
  else totient_range_acc n 25 1 (n - 1) 0

theorem test_decide : totient_fast 1999993 = 1999992 := by
  decide

